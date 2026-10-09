#!/usr/bin/env python3
"""Reconstruct verified public or exact source-layout views from this export.

The exported modules relocate local imports, declared private-name owners, include_str
addresses, declared resource digests and explicit proof-body build adaptations. The default original-path view uses published
receipt bytes; --exact restores the pinned source bytes, requiring --private-originals
for sanitized receipts. Both
identities and the unchanged receipt payloads are checked with tools/export-map.json.
Reconstructed files are written to a new
directory outside the repository or under its ignored .local directory; tracked files are
unchanged.

Schema 2: a source file may have several pinned byte versions (different papers pin
different Homework revisions). Every version is exported under its own target
(H0mework.Versions.<tag>.* for later versions); rows carry source_sha256 plus the list of
revisions the bytes satisfy. Receipts always record digests, so reconstruction picks the
row matching the receipt; a bare --path is accepted only when the path has one byte
version.

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

from publication import (PublicationError, verify_artifact, verify_file_sizes,
                         verify_repository_file_sizes)

ROOT = Path(__file__).resolve().parents[1]
EXPORT_MAP = ROOT / "tools" / "export-map.json"
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
EXTERNAL = {"Mathlib", "Batteries", "Lean", "Std", "Init", "ImportGraph", "Aesop"}


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
    module_header = False
    current_count = None
    for line in masked.splitlines(keepends=True):
        stripped = line.strip()
        if not stripped:
            offset += len(line)
            continue
        if re.match(r"(?:private|protected)\s+import\b", stripped):
            raise ViewError("Unsupported Lean import modifier")
        match = re.match(r"\s*(?P<public>public\s+)?(?P<meta>meta\s+)?import\b(?P<all>\s+all\b)?", line)
        if match:
            if any(match[name] for name in ("public", "meta", "all")) and not module_header:
                raise ViewError("Lean import modifiers require a module header")
            if match["public"] and match["all"]:
                raise ViewError("Lean public import cannot import all")
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
            module_header = module_header or stripped == "module"
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


def rewrite_private_names(text: str, rewrites, *, reverse: bool = False) -> str:
    """Relocate only declared private module owners; reverse restores source names.

    Rows declare ``private_name_rewrites`` as source_name/target_name pairs. An owner
    can stand alone in a Name quotation or precede a numeric private-name component.
    Comments, strings and longer module names remain byte-for-byte unchanged.
    """
    if rewrites is None:
        return text
    if not isinstance(rewrites, list):
        raise ViewError("Private-name rewrites must be a list")
    mapping = {}
    targets = set()
    for rewrite in rewrites:
        if not isinstance(rewrite, dict) or set(rewrite) != {"source_name", "target_name"}:
            raise ViewError("Private-name rewrites need source_name and target_name")
        source, target = rewrite["source_name"], rewrite["target_name"]
        for name in (source, target):
            if (not isinstance(name, str) or not name.startswith("_private.")
                    or not MODULE.fullmatch(name)):
                raise ViewError(f"Invalid private module owner: {name!r}")
        if source in mapping or target in targets:
            raise ViewError("Private-name rewrites must have unique sources and targets")
        mapping[source] = target
        targets.add(target)
    if not mapping:
        return text
    if reverse:
        mapping = {target: source for source, target in mapping.items()}
    owners = "|".join(re.escape(name) for name in sorted(mapping, key=len, reverse=True))
    # Lean identifiers also admit !, ?, and letter-like symbols outside Python's \w.
    name_chars = r"\w'.!?\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    boundary = rf"(?![{name_chars}])"
    pattern = re.compile(rf"(?<![{name_chars}])(?:{owners})(?={boundary}|\.[0-9]+(?:\.|{boundary}))")
    edits = [(match.start(), match.end(), mapping[match.group()])
             for match in pattern.finditer(mask_comments_and_strings(text))]
    for begin, end, replacement in reversed(edits):
        text = text[:begin] + replacement + text[end:]
    return text


def rewrite_private_owner_strings(text: str, rewrites, *, reverse: bool = False) -> str:
    """Relocate registered private-owner prefixes used by declaration lookup."""
    if rewrites is None:
        return text
    if not isinstance(rewrites, list):
        raise ViewError("Private-owner string rewrites must be a list")
    mapping, targets = {}, set()
    for rule in rewrites:
        if not isinstance(rule, dict) or set(rule) != {"source_owner", "target_owner"}:
            raise ViewError("Private-owner string rewrites need source_owner and target_owner")
        source, target = rule["source_owner"], rule["target_owner"]
        if any(not isinstance(name, str) or not name.startswith("_private.")
               or not MODULE.fullmatch(name) for name in (source, target)):
            raise ViewError("Invalid private-owner string prefix")
        if source in mapping or target in targets:
            raise ViewError("Private-owner string rewrites must be invertible")
        mapping[source] = target
        targets.add(target)
    if not mapping:
        return text
    if reverse:
        mapping = {target: source for source, target in mapping.items()}
    masked = mask_comments_and_strings(text)
    literals = {'"' + owner + '."': owner for owner in mapping}
    matches = {owner: [] for owner in mapping}
    for index, token in enumerate(masked):
        if token != '"' or not re.search(r"\.startsWith\s*\Z", masked[:index]):
            continue
        literal = re.match(r'"(?:\\.|[^"\\])*"', text[index:])
        if literal is not None and literal[0] in literals:
            matches[literals[literal[0]]].append((index, index + len(literal[0])))
    edits = []
    for owner, spans in matches.items():
        if len(spans) != 1:
            raise ViewError("Declared private-owner prefix literal is absent or duplicated")
        begin, end = spans[0]
        edits.append((begin, end, '"' + mapping[owner] + '."'))
    for begin, end, replacement in sorted(edits, reverse=True):
        text = text[:begin] + replacement + text[end:]
    return text


def rewrite_private_owner_expressions(text: str, rewrites, *, reverse: bool = False) -> str:
    """Relocate declared dynamic Name constructors, preserving the private index."""
    if rewrites is None:
        return text
    if not isinstance(rewrites, list):
        raise ViewError("Private-owner expressions must be a list")
    seen = set()
    for rule in rewrites:
        if (not isinstance(rule, dict) or set(rule) != {"source_expression", "target_expression", "count"}
                or rule["count"] != 1):
            raise ViewError("Private-owner expressions require one exact source and target")
        source, target = rule["source_expression"], rule["target_expression"]
        if not isinstance(source, str) or not isinstance(target, str) or source in seen:
            raise ViewError("Invalid private-owner expression")
        seen.add(source)
        family = re.fullmatch(r'\s*let moduleName := Name\.mkSimple \("([A-Za-z_][A-Za-z0-9_]*)"\+\+family\)', source)
        private = re.fullmatch(r'\(Name\.str `_private "([A-Za-z_][A-Za-z0-9_]*)"\)', source)
        valid = source == '(Name.str `_private moduleName.toString)' and target == '(Name.append `_private moduleName)'
        if family:
            named = re.fullmatch(r'\s*let moduleName := \("(H0mework\.[A-Za-z_][A-Za-z0-9_.]*)"\+\+family\)\.toName', target)
            valid = named is not None and named[1].endswith('.' + family[1])
        elif private:
            named = re.fullmatch(r'\(`_private\.(H0mework\.[A-Za-z_][A-Za-z0-9_.]*)\)', target)
            valid = named is not None and named[1].endswith('.' + private[1])
        elif source == '(Name.str `_private file)':
            named = re.fullmatch(r'\(Name\.append `_private \("(H0mework\.[A-Za-z_][A-Za-z0-9_.]*\.)" \+\+ file\)\.toName\)', target)
            valid = named is not None and MODULE.fullmatch(named[1][:-1]) is not None
        elif source == '(Name.str `_private moduleName)':
            named = re.fullmatch(r'\(Name\.append `_private \("(H0mework\.[A-Za-z_][A-Za-z0-9_.]*\.)" \+\+ moduleName\)\.toName\)', target)
            valid = named is not None and MODULE.fullmatch(named[1][:-1]) is not None
        if not valid:
            raise ViewError("Unsupported private-owner Name construction")
        before, after = (target, source) if reverse else (source, target)
        masked = mask_comments_and_strings(text)
        offset = len(before) - len(before.lstrip())
        positions = [match.start() for match in re.finditer(re.escape(before), text)
                     if masked[match.start() + offset] == before[offset]]
        if len(positions) != 1:
            raise ViewError("Declared private-owner expression is absent or duplicated")
        begin = positions[0]
        text = text[:begin] + after + text[begin + len(before):]
    return text


def audit_observer_start(text: str) -> int | None:
    """Locate one executable observer body, without matching comments or strings."""
    masked = mask_comments_and_strings(text)
    commands = list(re.finditer(r"(?m)^run_cmd[ \t]+do[ \t]*\r?\n", masked))
    named = r"(?:[ \t]+\([ \t]*name[ \t]*:=[ \t]*[A-Za-z_][A-Za-z0-9_'.]*[ \t]*\))?"
    headers = re.finditer(
        r'(?m)^elab' + named + r'[ \t]+"(?:\\.|[^"\\\r\n])*"[ \t]*:[ \t]*command[ \t]*=>[ \t]*do[ \t]*\r?\n',
        text)
    commands.extend(match for match in headers
                    if masked[match.start():match.start() + 4] == "elab")
    if not commands:
        return None
    if len(commands) != 1:
        raise ViewError("Audit module rewrites need one trailing observer command")
    return commands[0].end()


def name_audit_command(text: str, rule, *, reverse: bool = False) -> str:
    """Give a colliding command registration a module-owned name; keep its body."""
    if rule is None:
        return text
    if not isinstance(rule, dict) or set(rule) != {"source_declaration", "target_name"}:
        raise ViewError("Audit command name needs source_declaration and target_name")
    source, name = rule["source_declaration"], rule["target_name"]
    if (not isinstance(source, str)
            or not re.fullmatch(r'elab "(?:\\.|[^"\\\r\n])*" : command => do', source)
            or not isinstance(name, str) or not MODULE.fullmatch(name)):
        raise ViewError("Invalid audit command naming rule")
    target = "elab (name := " + name + ")" + source[4:]
    before, after = (target, source) if reverse else (source, target)
    masked = mask_comments_and_strings(text)
    matches = [match for match in re.finditer(r"(?m)^" + re.escape(before) + r"(?=\r?$)", text)
               if masked[match.start():match.start() + 4] == "elab"]
    if len(matches) != 1:
        raise ViewError("Declared audit command is absent or duplicated")
    begin, end = matches[0].span()
    return text[:begin] + after + text[end:]


def rewrite_audit_module_names(text: str, rewrites, *, reverse: bool = False) -> str:
    """Relocate declared module quotations in the trailing observer command."""
    if rewrites is None:
        return text
    if not isinstance(rewrites, list):
        raise ViewError("Audit module rewrites must be a list")
    if not rewrites:
        return text
    mapping, targets = {}, set()
    for item in rewrites:
        if not isinstance(item, dict) or set(item) != {"source_module", "target_module"}:
            raise ViewError("Audit module rewrites need source_module and target_module")
        source, target = item["source_module"], item["target_module"]
        if any(not isinstance(name, str) or not MODULE.fullmatch(name) for name in (source, target)):
            raise ViewError("Invalid audit module name")
        if source in mapping or target in targets:
            raise ViewError("Audit module rewrites must be invertible")
        mapping[source] = target
        targets.add(target)
    if reverse:
        mapping = {target: source for source, target in mapping.items()}
    split = audit_observer_start(text)
    if split is None:
        raise ViewError("Audit module rewrites need one trailing observer command")
    tail = text[split:]
    owners = "|".join(re.escape(name) for name in sorted(mapping, key=len, reverse=True))
    pattern = re.compile(r"(?<!`)`(" + owners + r")(?![\w'.!?])")
    matches = list(pattern.finditer(mask_comments_and_strings(tail)))
    if set(mapping) != {match[1] for match in matches}:
        raise ViewError("Declared audit module quotation is absent")
    for match in reversed(matches):
        tail = tail[:match.start(1)] + mapping[match[1]] + tail[match.end(1):]
    return text[:split] + tail


def rewrite_audit_runtime(text: str, environments, full_closure=False, *, reverse=False) -> str:
    """Keep legacy boundary overrides; an absent boundary traverses every edge."""
    if not isinstance(full_closure, bool):
        raise ViewError("Audit full-closure option must be boolean")
    if environments is None:
        environments = []
    if (not isinstance(environments, list) or any(not isinstance(name, str) for name in environments)
            or len(environments) != len(set(environments))):
        raise ViewError("Audit boundary environments must be a unique list")
    if not environments and not full_closure:
        return text
    source_marker = "open Lean Elab Command in\nrun_cmd do"
    target_marker = "open Lean Elab Command in\nset_option maxHeartbeats 0 in\nrun_cmd do"
    marker = target_marker if reverse and full_closure else source_marker
    if text.count(marker) != 1:
        raise ViewError("Audit runtime rewrite needs one trailing observer command")
    split = text.index(marker)
    prefix, tail = text[:split], text[split:]
    for variable in environments:
        if variable not in {"BELL_FIBER_PAID_NAMES", "BELL_DETECTOR_PAID_NAMES",
                            "BELL_PULSE_PAID_NAMES", "BELL_ANCHORS_PAID_NAMES"}:
            raise ViewError("Unregistered audit boundary environment")
        source = (f'  let some paidPath ← IO.getEnv "{variable}" |\n'
                  '    throwError "missing paid source-dependency boundary"\n'
                  '  let paidText ← IO.FS.readFile paidPath')
        target = (f'  let paidText ← match (← IO.getEnv "{variable}") with\n'
                  '    | some paidPath => IO.FS.readFile paidPath\n'
                  '    | none => pure "[]"')
        before, after = (target, source) if reverse else (source, target)
        if tail.count(before) != 1:
            raise ViewError("Declared audit boundary block is absent or duplicated")
        start = tail.index(before)
        if mask_comments_and_strings(tail)[start:start + 5] != "  let":
            raise ViewError("Audit boundary rewrite must address executable observer code")
        tail = tail.replace(before, after)
    if full_closure:
        before, after = (target_marker, source_marker) if reverse else (source_marker, target_marker)
        tail = tail.replace(before, after, 1)
    return prefix + tail


def name_local_instances(text: str, rules, *, reverse: bool = False) -> str:
    """Give colliding anonymous local instances explicit names; keep type and value."""
    if rules is None:
        return text
    if not isinstance(rules, list):
        raise ViewError("Local instance names must be a list")
    sources, names = set(), set()
    for rule in rules:
        if not isinstance(rule, dict) or set(rule) != {"source_declaration", "target_name"}:
            raise ViewError("Local instance names need source_declaration and target_name")
        source, name = rule["source_declaration"], rule["target_name"]
        match = re.fullmatch(r"(local[ \t]+instance)([ \t]*:[ \t]*[^\n\r:=\";]+)", source) \
            if isinstance(source, str) else None
        if match is None or not isinstance(name, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
            raise ViewError("Invalid anonymous local instance naming rule")
        if source in sources or name in names:
            raise ViewError("Local instance names must be invertible")
        sources.add(source)
        names.add(name)
    for rule in rules:
        source, name = rule["source_declaration"], rule["target_name"]
        split = re.match(r"local[ \t]+instance", source).end()
        target = source[:split] + " " + name + source[split:]
        before, after = (target, source) if reverse else (source, target)
        pattern = re.compile(r"(?m)^[ \t]*(" + re.escape(before) + r")(?=[ \t]*(?::=|where\b))")
        matches = list(pattern.finditer(mask_comments_and_strings(text)))
        if len(matches) != 1:
            raise ViewError("Declared anonymous local instance is absent or duplicated")
        begin, end = matches[0].span(1)
        text = text[:begin] + after + text[end:]
    return text


def invert_resources(text: str, rewrites) -> str:
    """Map relocated include_str literals back to their original addresses."""
    for rewrite in rewrites or []:
        target, source = rewrite["target_address"], rewrite["source_address"]
        count = text.count(f'"{target}"')
        if count != 1:
            raise ViewError(
                f"Relocated resource address not unique in exported file: {target!r}")
        text = text.replace(f'"{target}"', f'"{source}"')
    return text


def invert_resource_digests(raw: bytes, row: dict) -> bytes:
    for rewrite in reversed(row.get("resource_sha256_rewrites", [])):
        target = json.dumps(rewrite["target"]).encode()
        source = json.dumps(rewrite["source"]).encode()
        if raw.count(target) != 1:
            raise ViewError("Published module resource digest is not unique")
        raw = raw.replace(target, source)
    return raw


def rewrite_proof_bodies(text: str, rewrites, *, reverse: bool = False) -> str:
    """Apply declared compilation proofs while retaining the exact theorem statement."""
    if rewrites is None:
        return text
    if not isinstance(rewrites, list):
        raise ViewError("Invalid proof-body rewrites")
    for rewrite in rewrites:
        if not isinstance(rewrite, dict) or set(rewrite) != {"declaration", "source", "public"}:
            raise ViewError("Invalid proof-body rewrite")
        declaration = rewrite["declaration"]
        source, public = rewrite["source"], rewrite["public"]
        if not isinstance(declaration, str) or not MODULE.fullmatch(declaration):
            raise ViewError("Invalid proof declaration")
        statements = []
        for block in (source, public):
            if not isinstance(block, str) or not block.endswith("\n"):
                raise ViewError("Invalid proof-body block")
            statement, separator, body = block.partition(" := by\n")
            if (not separator or not re.match(r"^theorem\s+" + re.escape(declaration) + r"(?:\s|:)", statement)
                    or not body.strip() or any(line and not line[0].isspace() for line in body.splitlines())):
                raise ViewError("Rewrite must contain one theorem and its indented proof")
            statements.append(statement)
        if statements[0] != statements[1]:
            raise ViewError("Proof-body rewrite changes the theorem statement")
        before, after = (public, source) if reverse else (source, public)
        if before == after or text.count(before) != 1:
            raise ViewError("Proof-body rewrite anchor is not unique")
        text = text.replace(before, after, 1)
    return text


def module_views(row: dict, inverse: dict) -> tuple[bytes, bytes]:
    """Return the public source-layout view and its exact pinned source."""
    raw = (ROOT / row["path"]).read_bytes()
    if sha(raw) != row["target_sha256"]:
        raise ViewError(f"Exported module differs from its recorded digest: {row['path']}")
    text = name_audit_command(raw.decode("utf-8"), row.get("audit_command_name"), reverse=True)
    text = name_local_instances(text, row.get("local_instance_names"), reverse=True)
    text = rewrite_audit_runtime(text, row.get("audit_boundary_fallbacks"),
                                 row.get("audit_full_closure", False), reverse=True)
    text = rewrite_audit_module_names(text, row.get("audit_module_rewrites"), reverse=True)
    text = rewrite_private_names(text, row.get("private_name_rewrites"),
                                 reverse=True)
    text = rewrite_private_owner_strings(text, row.get("private_owner_string_rewrites"), reverse=True)
    text = rewrite_private_owner_expressions(text, row.get("private_owner_expression_rewrites"), reverse=True)
    tokens = import_tokens(text)
    reverse = {}
    for _, _, module in tokens:
        if module.split(".")[0] in EXTERNAL:
            continue
        if module in (row.get("import_map") or {}):
            reverse[module] = row["import_map"][module]
            continue
        source_row = inverse.get(module)
        if source_row is None:
            raise ViewError(f"Unmapped exported import: {module}")
        reverse[module] = source_row["source"] if not source_row["source"].startswith("file:") \
            else _file_token(source_row, row)
    view = invert_resources(transform(text, tokens, reverse).decode("utf-8"),
                            row.get("resource_rewrites")).encode("utf-8")
    import_tokens(view.decode("utf-8"))
    original = invert_resource_digests(view, row)
    original = rewrite_proof_bodies(original.decode("utf-8"), row.get("proof_body_rewrites"), reverse=True).encode("utf-8")
    if sha(original) != row["source_sha256"]:
        raise ViewError(f"Reconstructed source digest differs: {row['source_path']}")
    if sha(view) != row.get("view_sha256", row["source_sha256"]):
        raise ViewError(f"Public source-layout digest differs: {row['source_path']}")
    return view, original


def artifact_views(row: dict, private_originals=None) -> tuple[bytes, bytes | None]:
    raw = (ROOT / row["path"]).read_bytes()
    original = None
    if row.get("publication") and private_originals is not None:
        digest = row["source_sha256"]
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ViewError("Invalid private source digest")
        path = Path(private_originals) / digest
        if not path.is_file():
            raise ViewError("Private original receipt is unavailable")
        original = path.read_bytes()
    try:
        raw = verify_artifact(raw, row, original)
    except PublicationError as error:
        raise ViewError(f"Artifact identity failed: {row['path']}: {error}") from error
    return raw, original if row.get("publication") else raw


def source_path(value: str) -> str:
    if (not isinstance(value, str) or not value or value.startswith("/")
            or any(c in value for c in ("\\", ":", "\0", "\n", "\r"))
            or any(p in ("", ".", "..") for p in value.split("/"))):
        raise ViewError(f"Unsafe source-view path: {value!r}")
    return value


def source_record(row: dict, path: str) -> dict | None:
    """Select an original layout while retaining its shared complete body owner."""
    if path == row.get("source_path", row.get("source")):
        return row
    for alias in row.get("source_aliases", []):
        if (not isinstance(alias, dict)
                or set(alias) & {"path", "target", "target_sha256", "import_map", "proof_body_rewrites"}
                or alias.get("source_sha256") != row["source_sha256"]
                or not MODULE.fullmatch(str(alias.get("original_module_name", "")))
                or not re.fullmatch(r"[0-9a-f]{40}", str(alias.get("source_revision", "")))
                or not isinstance(alias.get("source_revisions"), list)
                or any(not re.fullmatch(r"[0-9a-f]{40}", str(ref)) for ref in alias["source_revisions"])
                or alias["source_revision"] not in alias["source_revisions"]):
            raise ViewError("Invalid shared source-layout identity")
        original_path = source_path(alias.get("source_path"))
        if original_path != path:
            continue
        result = {**row, **{key: alias[key] for key in
                          ("source_path", "source_sha256", "source_revision", "source_revisions", "source_origin")
                          if key in alias}, "source": "file:" + original_path}
        if "source_origin" not in alias:
            result.pop("source_origin", None)
        return result
    return None


def load_map():
    try:
        data = json.loads(EXPORT_MAP.read_bytes())
    except (OSError, ValueError) as error:
        raise ViewError(f"Cannot read {EXPORT_MAP.name}: {error}") from error
    if not isinstance(data, dict) or data.get("schema") not in (1, 2):
        raise ViewError("Unsupported export map schema")
    directory = data["lean_directory"]
    # module rows keyed by original source path; several rows per path are byte versions
    modules: dict[str, list[dict]] = {}
    inverse = {}
    for row in data.get("modules", []):
        if data["schema"] == 1:
            row = {**row, "source_path": directory + "/" + row["source"].replace(".", "/") + ".lean",
                   "variant": "base", "import_map": None}
        key = row["source_path"]
        modules.setdefault(key, []).append(row)
        previous = inverse.get(row["target"])
        if previous is not None and previous != row:
            raise ViewError(f"Ambiguous inverse mapping for {row['target']}")
        inverse[row["target"]] = row
    for row in data.get("modules", []):
        seen = set()
        for alias in row.get("source_aliases", []):
            if not isinstance(alias, dict):
                raise ViewError("Invalid shared source-layout identity")
            key = source_path(alias.get("source_path"))
            if key == row["source_path"] or key in seen:
                raise ViewError("Duplicate shared source-layout address")
            seen.add(key)
            modules.setdefault(key, []).append(source_record(row, key))
    artifacts: dict[str, list[dict]] = {}
    for row in data.get("artifacts", []):
        artifacts.setdefault(row["source"], []).append(row)
    if set(modules) & set(artifacts):
        raise ViewError("Ambiguous original module/artifact path")
    return data, modules, artifacts, inverse


def row_at(row: dict, rev: str) -> bool:
    """Whether the row's bytes are the version pinned at revision ``rev``."""
    if "source_revisions" in row:
        return rev in row["source_revisions"]
    return row["source_revision"] == rev


def pick(rows: list[dict], path: str, digests: set[str] | None, at: str | None) -> dict:
    if digests:
        matches = [row for row in rows if row["source_sha256"] in digests
                   or (row.get("publication") and row["target_sha256"] in digests)
                   or row.get("view_sha256") in digests]
        if at is not None and len(matches) > 1:
            era = [row for row in matches if row_at(row, at)]
            if era:
                matches = era
        if not matches:
            raise ViewError(f"No exported byte version matches the receipt digests: {path}")
        # Digest-matched rows all carry identical source bytes; a path pinned at
        # several revisions can legitimately have one row per copy.
        return matches[0]
    if at is not None:
        matches = [row for row in rows if row_at(row, at)]
        if not matches:
            return None  # the path did not exist with exported bytes at this revision
        return matches[0]
    distinct = {row["source_sha256"] for row in rows}
    if len(distinct) > 1:
        raise ViewError(
            f"Several pinned byte versions of {path}; select one via a receipt or --at")
    return rows[0]


def reconstruct(paths=(), receipts=(), prefixes=(), at=None,
                receipt_prefixes=(), exact=False, private_originals=None) -> tuple[dict[str, bytes], list[str]]:
    data, modules, artifacts, inverse = load_map()
    if at is not None:
        revisions = data.get("revisions", {})
        rev = revisions.get(at)
        if rev is None:
            known = {row["source_revision"] for rows in modules.values() for row in rows}
            known |= {row["source_revision"] for rows in artifacts.values() for row in rows}
            hits = {r for r in known if r.startswith(at)}
            if len(hits) != 1:
                raise ViewError(f"--at does not resolve to one pinned revision: {at}")
            rev = hits.pop()
        at = rev

    def artifact_bytes(name, digests=None):
        source_path(name)
        rows = artifacts.get(name)
        if not rows:
            raise ViewError(f"Original artifact is not exported: {name}")
        row = pick(rows, name, digests, at)
        if row is None:
            raise ViewError(f"Original artifact does not exist at the pinned revision: {name}")
        public, original = artifact_views(row, private_originals)
        if exact and original is None:
            raise ViewError("Exact receipt reconstruction requires --private-originals")
        return original if exact else public

    requested = {source_path(p) for p in paths}
    for prefix in prefixes:
        source_path(prefix.rstrip("/") + "/x")  # validate as a path fragment
        hits = [name for name in set(modules) | set(artifacts)
                if name == prefix or name.startswith(prefix.rstrip("/") + "/")]
        if not hits:
            raise ViewError(f"No exported source under prefix: {prefix}")
        requested.update(hits)
    expected: dict[str, set[str]] = {}

    def receipt_hashes(blob, label):
        try:
            document = json.loads(blob)
        except ValueError as error:
            raise ViewError(f"Receipt is not valid JSON: {label}") from error
        # Audited check-ins pin source bytes under *_sha256 tables (plus the
        # legacy source_hashes); the runtime scripts assert every table that is
        # present, so merge all.
        merged = {}
        for key, table in document.items():
            if key == "source_hashes" or key.endswith("_sha256"):
                if isinstance(table, dict):
                    merged.update(table)
        return merged

    def merge_hashes(hashes, label, receipt_source=None):
        for name, digest in hashes.items():
            if "/" not in name and receipt_source is not None:
                # Bare keys are package-dir-relative provenance labels.
                resolved = receipt_source.rsplit("/", 1)[0] + "/" + name
                if resolved in modules or resolved in artifacts:
                    name = resolved
                else:
                    continue
            source_path(name)
            if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
                raise ViewError(f"Invalid receipt digest: {name}")
            expected.setdefault(name, set()).add(digest)
            requested.add(name)

    for prefix in receipt_prefixes:
        for rows in artifacts.values():
            for row in rows:
                if not row["path"].startswith(prefix):
                    continue
                if not row["path"].endswith(".json") or row.get("binary"):
                    continue
                if at is not None and not row_at(row, at):
                    continue
                blob = artifact_bytes(row["source"])
                try:
                    hashes = receipt_hashes(blob, row["path"])
                except ViewError:
                    continue
                if isinstance(hashes, dict) and hashes:
                    merge_hashes(hashes, row["path"], row["source"])
    for receipt in receipts:
        rows = [row for rows in artifacts.values() for row in rows if row["path"] == receipt]
        if len(rows) != 1:
            raise ViewError(f"Receipt is not an exported artifact of this repository: {receipt}")
        blob = artifact_bytes(rows[0]["source"], {rows[0]["source_sha256"]})
        hashes = receipt_hashes(blob, receipt)
        if not isinstance(hashes, dict) or not hashes:
            raise ViewError(f"Receipt needs a nonempty source_sha256 object: {receipt}")
        requested.add(rows[0]["source"])
        expected[rows[0]["source"]] = {rows[0]["source_sha256"] if exact
                                       else rows[0]["target_sha256"]}
        merge_hashes(hashes, receipt, rows[0]["source"])
    if not requested:
        raise ViewError("Select at least one original path or receipt")

    outputs = {}
    skipped = []
    for name in sorted(requested):
        digests = expected.get(name)
        if name not in modules and name not in artifacts:
            # A receipt may pin a file this repository already tracks verbatim
            # (e.g. Lean/lean-toolchain): identical bytes satisfy the pin.
            if digests:
                local = ROOT / name
                if local.is_file():
                    raw = local.read_bytes()
                    if sha(raw) in digests:
                        outputs[name] = raw
                        continue
                    raise ViewError(f"Tracked file differs from its pinned bytes: {name}")
                # Receipts also pin runtime-generated outputs (a replay writes
                # its own receipt.json): not exportable, not needed as input.
                # A pinned Lean source can never be a runtime output, though —
                # its absence means the export is missing a real input.
                if name.startswith("Lean/") and name.endswith(".lean"):
                    raise ViewError(f"Pinned Lean source is not exported: {name}")
                skipped.append(name)
                expected.pop(name, None)
                continue
            raise ViewError(f"Original path is not exported: {name}")
        if name not in modules:
            if pick(artifacts[name], name, digests, at) is None:
                continue
            outputs[name] = artifact_bytes(name, digests)
            continue
        row = pick(modules[name], name, digests, at)
        if row is None:
            continue
        public, original = module_views(row, inverse)
        outputs[name] = original if exact else public
    for name, digests in expected.items():
        accepted = set(digests)
        if not exact:
            for row in modules.get(name, []) + artifacts.get(name, []):
                if row["source_sha256"] in digests:
                    accepted.add(row.get("view_sha256", row.get("target_sha256", row["source_sha256"])))
        if sha(outputs[name]) not in accepted:
            raise ViewError(f"Receipt source digest differs: {name}")
    if len({name.casefold() for name in outputs}) != len(outputs):
        raise ViewError("Case-colliding original paths")
    return outputs, skipped


def _file_token(file_row: dict, importer_row: dict) -> str:
    """Original import token for an exported non-module file.

    The importing file referenced it by its path relative to the importer, as a
    dotted Lean name (a flat sibling directory yields the bare basename).
    """
    source = file_row["source"]
    assert source.startswith("file:")
    target_path = source[5:]
    importer = importer_row["source"]
    assert importer.startswith("file:")
    import posixpath
    rel = posixpath.relpath(target_path, posixpath.dirname(importer[5:]))
    if rel.startswith("../"):
        raise ViewError(f"Cannot recover the original import token of {target_path} "
                        f"from {importer[5:]}")
    return rel[:-5].replace("/", ".")


def verify_all(private_originals=None) -> dict:
    """Check pinned modules, original artifacts and published receipt payloads."""
    data, modules, artifacts, inverse = load_map()
    if (ROOT / ".git").exists():
        verify_repository_file_sizes(ROOT)
    else:
        # Source bundles have no Git index; include unbound execution logs too.
        paths = {row["path"] for rows in (*modules.values(), *artifacts.values()) for row in rows}
        paths.add("tools/export-map.json")
        paths.update(path.relative_to(ROOT).as_posix()
                     for path in (ROOT / "evidence").rglob("*") if path.is_file())
        verify_file_sizes(ROOT, paths)
    checked = 0
    for path, rows in sorted(modules.items()):
        for row in rows:
            module_views(row, inverse)
            checked += 1
    artifact_checked = 0
    published = 0
    private_checked = 0
    for path, rows in sorted(artifacts.items()):
        for row in rows:
            _, original = artifact_views(row, private_originals)
            if row.get("publication"):
                published += 1
                private_checked += original is not None
            artifact_checked += 1
    return {"modules": checked, "artifacts": artifact_checked,
            "published_receipts": published, "private_originals_verified": private_checked}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=None,
                        help="New directory under an existing temporary parent, outside this repository")
    parser.add_argument("--path", action="append", default=[],
                        help="Original source path of an exported module or artifact")
    parser.add_argument("--receipt", action="append", default=[],
                        help="Repository path of an exported JSON receipt with source_sha256")
    parser.add_argument("--path-prefix", action="append", default=[],
                        help="Export every module/artifact whose original source path starts "
                             "with this prefix (single byte version required per path)")
    parser.add_argument("--at", default=None, metavar="REV",
                        help="Pinned revision tag or commit prefix; resolves which byte "
                             "version to use for multi-version paths")
    parser.add_argument("--receipt-prefix", action="append", default=[], metavar="DIR",
                        help="Merge the pin lists of every exported JSON receipt under this "
                             "repository path (with --at, only receipts pinned at that "
                             "revision contribute)")
    parser.add_argument("--verify-all", action="store_true",
                        help="Verify every module and original/published artifact; writes nothing")
    parser.add_argument("--exact", action="store_true",
                        help="Restore exact pinned source bytes; sanitized receipts need private originals")
    parser.add_argument("--private-originals", type=Path,
                        help="Private archive directory with original receipt files named by source SHA256")
    args = parser.parse_args(argv)
    if args.verify_all:
        try:
            result = verify_all(args.private_originals)
            if args.exact and result["private_originals_verified"] != result["published_receipts"]:
                raise ViewError("Exact verification requires all private original receipts")
        except (ViewError, OSError, ValueError) as error:
            print(json.dumps({"ok": False, "error": str(error)}))
            return 1
        print(json.dumps({"ok": True, **result}, ensure_ascii=False))
        return 0
    if args.output is None:
        print(json.dumps({"ok": False, "error": "--output is required unless --verify-all"}))
        return 1
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
        outputs, skipped = reconstruct(args.path, args.receipt, args.path_prefix,
                                       args.at, args.receipt_prefix, args.exact, args.private_originals)
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
    print(json.dumps({"ok": True, "files": len(outputs), "root": str(output),
                      "view": "exact" if args.exact else "public",
                      "runtime_generated_skipped": skipped}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
