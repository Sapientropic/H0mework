#!/usr/bin/env python3
"""Reconstruct byte-exact original-path sources from this repository, without the source repo.

The exported modules differ from the fixed research sources only in local import
addresses; this tool inverts that rewrite using tools/export-map.json and verifies every
reconstructed byte against the recorded source digest (and, when --receipt is given,
against the receipt's own source_sha256 object). Reconstructed files are written to a new
directory outside the repository or under its ignored .local directory; tracked files are unchanged.

Example:
  python3 tools/source_view.py --output /tmp/view \\
      --receipt evidence/physics/low-energy/results/exact-readout.json
  python3 scripts/physics/low-energy/check_readout.py \\
      --root /tmp/view --receipt evidence/physics/low-energy/results/exact-readout.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
EXPORT_MAP = ROOT / "tools" / "export-map.json"
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
EXTERNAL = {"Mathlib", "Batteries", "Lean", "Std", "Init", "ImportGraph"}


class ViewError(Exception):
    pass


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


# The comment/string masking and import tokenizer below are vendored unchanged from the
# audited migration tooling so both directions parse identically.

def mask_comments_and_strings(text: str) -> str:
    result = list(text)
    i = 0
    while i < len(text):
        start = i
        literal = False
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ViewError("Unterminated Lean block comment")
        elif text.startswith('r', i) and (raw := re.compile(r'r(#+)"').match(text, i)):
            closing = '"' + raw.group(1)
            end = text.find(closing, raw.end())
            if end < 0:
                raise ViewError("Unterminated Lean raw string")
            literal = True
            i = end + len(closing)
        elif text[i] == "«":
            end = text.find("»", i + 1)
            if end < 0:
                raise ViewError("Unterminated Lean quoted identifier")
            literal = True
            i = end + 1
        elif text[i] == '"':
            literal = True
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ViewError("Unterminated Lean string")
        elif (text[i] == "'" and i + 2 < len(text)
              and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'"))):
            end = i + 3 if text[i + 1] != "\\" else i + 4
            if end <= len(text) and text[end - 1] == "'":
                literal = True
                i = end
            else:
                i += 1
                continue
        else:
            i += 1
            continue
        for j in range(start, min(i, len(text))):
            if text[j] not in "\r\n":
                result[j] = " "
        if literal:
            result[start] = text[start]
    return "".join(result)


def import_tokens(text: str) -> list[tuple[int, int, str]]:
    masked = mask_comments_and_strings(text)
    tokens = []
    offset = 0
    header = True
    continuation = False
    imported = False
    current_count = None
    for line in masked.splitlines(keepends=True):
        stripped = line.strip()
        if not stripped:
            offset += len(line)
            continue
        if re.match(r"(?:public|private|protected)\s+import\b", stripped):
            raise ViewError("Unsupported Lean import modifier")
        match = re.match(r"\s*import\b", line)
        if match:
            if current_count == 0:
                raise ViewError("Empty Lean import declaration")
            current_count = 0
            if not header:
                raise ViewError("Import after a declaration is unsupported")
            start = match.end()
            continuation = True
            imported = True
        elif header and continuation and line[0].isspace():
            start = 0
        elif header and stripped in ("prelude", "module") and not imported:
            offset += len(line)
            continue
        else:
            if current_count == 0:
                raise ViewError("Empty Lean import declaration")
            header = False
            continuation = False
            offset += len(line)
            continue
        for token in re.finditer(r"\S+", line[start:]):
            name = token.group()
            if name in ("all", "public", "private"):
                raise ViewError(f"Unsupported Lean import syntax: {name}")
            if not MODULE.fullmatch(name):
                raise ViewError(f"Unsafe or unsupported module name: {name!r}")
            begin = offset + start + token.start()
            tokens.append((begin, begin + len(name), name))
            current_count += 1
        offset += len(line)
    if current_count == 0:
        raise ViewError("Empty Lean import declaration")
    return tokens


def transform(text: str, tokens, mapping: dict[str, str]) -> bytes:
    edits = [(begin, end, mapping[module]) for begin, end, module in tokens
             if module.split(".")[0] not in EXTERNAL]
    for begin, end, replacement in sorted(edits, reverse=True):
        text = text[:begin] + replacement + text[end:]
    return text.encode("utf-8")


def source_path(value: str) -> str:
    if (not isinstance(value, str) or not value or value.startswith("/")
            or any(c in value for c in ("\\", ":", "\0", "\n", "\r"))
            or any(p in ("", ".", "..") for p in value.split("/"))):
        raise ViewError(f"Unsafe source-view path: {value!r}")
    return value


def load_map():
    try:
        data = json.loads(EXPORT_MAP.read_bytes())
    except (OSError, ValueError) as error:
        raise ViewError(f"Cannot read {EXPORT_MAP.name}: {error}") from error
    if not isinstance(data, dict) or data.get("schema") != 1:
        raise ViewError("Unsupported export map schema")
    modules = {}
    for row in data.get("modules", []):
        name = data["lean_directory"] + "/" + row["source"].replace(".", "/") + ".lean"
        if name in modules:
            raise ViewError(f"Duplicate module entry: {name}")
        modules[name] = row
    artifacts = {row["source"]: row for row in data.get("artifacts", [])}
    if len(artifacts) != len(data.get("artifacts", [])):
        raise ViewError("Duplicate artifact entry in export map")
    if modules.keys() & artifacts.keys():
        raise ViewError("Ambiguous original module/artifact path")
    return data, modules, artifacts


def reconstruct(paths=(), receipts=()) -> dict[str, bytes]:
    data, modules, artifacts = load_map()
    inverse = {}
    for row in data["modules"]:
        previous = inverse.get(row["target"])
        if previous is not None and previous != row["source"]:
            raise ViewError(f"Ambiguous inverse mapping for {row['target']}")
        inverse[row["target"]] = row["source"]

    def artifact_bytes(name):
        source_path(name)
        if name not in artifacts:
            raise ViewError(f"Original artifact is not exported: {name}")
        row = artifacts[name]
        raw = (ROOT / row["path"]).read_bytes()
        if sha(raw) != row["source_sha256"]:
            raise ViewError(f"Exported artifact differs from its recorded digest: {name}")
        return raw

    requested = {source_path(p) for p in paths}
    expected = {}
    by_target = {row["path"]: row for row in data.get("artifacts", [])}
    for receipt in receipts:
        row = by_target.get(receipt)
        if row is None:
            raise ViewError(f"Receipt is not an exported artifact of this repository: {receipt}")
        blob = artifact_bytes(row["source"])
        try:
            hashes = json.loads(blob).get("source_sha256")
        except ValueError as error:
            raise ViewError(f"Receipt is not valid JSON: {receipt}") from error
        if not isinstance(hashes, dict) or not hashes:
            raise ViewError(f"Receipt needs a nonempty source_sha256 object: {receipt}")
        requested.add(row["source"])  # the receipt itself is exported byte-exact
        for name, digest in hashes.items():
            source_path(name)
            if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
                raise ViewError(f"Invalid receipt digest: {name}")
            if name in expected and expected[name] != digest:
                raise ViewError(f"Receipts disagree on original digest: {name}")
            expected[name] = digest
            requested.add(name)
    if not requested:
        raise ViewError("Select at least one original path or receipt")

    outputs = {}
    for name in sorted(requested):
        if name not in modules:
            outputs[name] = artifact_bytes(name)
            continue
        row = modules[name]
        raw = (ROOT / row["path"]).read_bytes()
        if sha(raw) != row["target_sha256"]:
            raise ViewError(f"Exported module differs from its recorded digest: {row['path']}")
        text = raw.decode("utf-8")
        tokens = import_tokens(text)
        reverse = {}
        for begin, end, module in tokens:
            if module.split(".")[0] in EXTERNAL:
                continue
            if module not in inverse:
                raise ViewError(f"Unmapped exported import: {module}")
            reverse[module] = inverse[module]
        original = transform(text, tokens, reverse)
        import_tokens(original.decode("utf-8"))  # the inverted text must still parse
        if sha(original) != row["source_sha256"]:
            raise ViewError(f"Reconstructed source digest differs: {name}")
        outputs[name] = original
    for name, digest in expected.items():
        if sha(outputs[name]) != digest:
            raise ViewError(f"Receipt source digest differs: {name}")
    if len({name.casefold() for name in outputs}) != len(outputs):
        raise ViewError("Case-colliding original paths")
    return outputs


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="New directory under an existing temporary parent, outside this repository")
    parser.add_argument("--path", action="append", default=[],
                        help="Original source path of an exported module or artifact")
    parser.add_argument("--receipt", action="append", default=[],
                        help="Repository path of an exported JSON receipt with source_sha256")
    args = parser.parse_args(argv)
    output = args.output
    if ".." in output.parts or output.is_symlink():
        print(json.dumps({"ok": False, "error": "Unsafe output directory"}))
        return 1
    output = output.resolve()
    local = (ROOT / ".local").resolve()
    inside = output.is_relative_to(ROOT.resolve()) and not output.is_relative_to(local)
    if inside or output.exists():
        print(json.dumps({"ok": False, "error":
                          "Output must be a new directory outside tracked files "
                          "(only the gitignored .local/ area is allowed inside the repository)"}))
        return 1
    try:
        outputs = reconstruct(args.path, args.receipt)
        output.mkdir(parents=True, exist_ok=False)
        try:
            for name, raw in outputs.items():
                path = output / source_path(name)
                path.parent.mkdir(parents=True, exist_ok=True)
                with path.open("xb") as handle:
                    handle.write(raw)
        except BaseException:
            shutil.rmtree(output, ignore_errors=True)
            raise
    except (ViewError, OSError, ValueError) as error:
        print(json.dumps({"ok": False, "error": str(error)}))
        return 1
    print(json.dumps({"ok": True, "files": len(outputs), "root": str(output)}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
