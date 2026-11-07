#!/usr/bin/env python3
"""Verify and rebuild the book's additional public society proofs."""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import json
import re

import first_release as release
import generated_society as finite
import source_view
import whole_ledger


MAP = "checks/society-book-map.json"
SELECTION = "checks/society-book-selection.json"
SCHEMA = "h0mework/society-book-map@1"


@contextmanager
def book_map():
    previous = release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP
    release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = SCHEMA, SCHEMA, MAP
    try:
        yield
    finally:
        release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = previous


def entry(root):
    identity = release.verify_map(root, MAP, require_ready=True)
    finite.require(identity["ok"], "Book source map failed: " + str(identity["errors"]))
    selection, exported, epochs = finite.selected_views(root, exact=True, selection_path=SELECTION)
    data = release.read_json(root / MAP)
    finite.require(data["acceptance"]["selection_sha256"] == release.sha((root / SELECTION).read_bytes()),
                   "Accepted book selection changed")
    scopes, entries = finite.package_scopes(data, exported, root)
    compiled = {path for scope in scopes.values() for path in scope["files"]}
    proof_paths = {row["path"] for state in epochs.values() for row in state["modules"].values()}
    finite.require(proof_paths <= compiled, "Book selection has unbuilt owners: " + str(sorted(proof_paths - compiled)))
    selected = {(row["source_commit"], path) for row in selection["selections"] for path in row["roots"]}
    mapped = set()
    for claim in release.selected_claims(data):
        for row in claim["selection_roots"]:
            epoch, path = row["source_commit"], row["source_path"]
            finite.require((epoch, path) in selected and epochs[epoch]["modules"][path]["target"] == row["public_module"],
                           "Book family root differs from recovered selection: " + path)
            mapped.add((epoch, path))
    finite.require(selected == mapped, "A selected root is missing from the book family map")
    for _, role, _, row in release.claim_entries(release.selected_claims(data)):
        kind = "artifacts" if role == "resources" else "modules"
        record = epochs[row["source_commit"]][kind].get(row["source_path"])
        finite.require(record is not None and record["path"] == row["public"]["path"],
                       "Claim map uses a different source owner: " + row["source_path"])
    kernel = finite.artifact(root, data["acceptance"]["scoped_kernel"])
    finite.require(kernel["status"] == "passed" and kernel["execution"]["exit_code"] == 0,
                   "Scoped audit did not pass its independent kernel replay")
    checked_types = finite.recorded_acceptance(data, scopes, entries, root)
    return {"status": "passed", "families": identity["claims"], "selected_roots": len(selected),
            "proof_owners": len(proof_paths), "exact_sources": sum(len(s["modules"]) for s in epochs.values()),
            "resources": sum(len(s["artifacts"]) for s in epochs.values()), "complete_types": checked_types}


def source(root, output, *, exact):
    _, _, epochs = finite.selected_views(root, exact=exact, selection_path=SELECTION)
    directory = release.new_output(root, output)
    for epoch, state in epochs.items():
        for path, body in state["outputs"].items():
            target = directory / epoch / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(body)
    return {"status": "passed", "view": "exact" if exact else "public",
            "files": sum(len(s["outputs"]) for s in epochs.values())}


def scoped_kernel(root, output):
    data = release.read_json(root / MAP)
    claim = next(row for row in data["claims"] if row["id"] == "pgs-public-pf10-bounded-independent-audit")
    reference, = claim["resources"]
    raw = release.repo_file(root, reference["public"]["path"]).read_bytes()
    finite.require(release.sha(raw) == reference["source_sha256"], "Original scoped kernel consumer changed")
    original = raw.decode()
    owners = {
        row["source_path"][5:-5].replace("/", "."): row["public_module"]
        for family in data["claims"] if family["id"] in {
            "pgs-public-pf10-bounded-independent-audit", "pgs-public-pf11-paid-revocation-and-handoff"
        }
        for row in family["selection_roots"] if row["source_path"].startswith("Lean/SaturationMonoid/")
    }
    inventory, = re.findall(r"(?m)^  let owned := #\[([^\n]*)\]$", original)
    names = [name.strip().removeprefix("`") for name in inventory.split(",")]
    rules = [{"source_module": name, "target_module": owners[name]} for name in names]
    program = source_view.rewrite_audit_module_names(original, rules)
    imports = {name: owners[name] for _, _, name in source_view.import_tokens(program) if name in owners}

    def rebind(text, mapping):
        for begin, end, name in reversed(source_view.import_tokens(text)):
            if name in mapping:
                text = text[:begin] + mapping[name] + text[end:]
        return text

    program = rebind(program, imports)
    reversed_imports = {target: name for name, target in imports.items()}
    restored = source_view.rewrite_audit_module_names(rebind(program, reversed_imports), rules, reverse=True)
    finite.require(restored == original, "Scoped consumer address adaptation is not reversible")
    directory = release.new_output(root, output)
    file = directory / "consumer.lean"
    file.write_text(program)
    log = directory / "kernel.log"
    run = release.run_process(
        ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true", "--root=..",
         "../" + file.relative_to(root).as_posix()], root, log, release.build_environment(),
    )
    text = log.read_text()
    lines = [line.split("PUBLIC SCOPED AUDIT KERNEL PASS: ", 1)[1]
             for line in text.splitlines() if "PUBLIC SCOPED AUDIT KERNEL PASS: " in line]
    passed = run["exit_code"] == 0 and len(lines) == 1 and "SCOPED CLIENT CLOSURES PASS" in text
    result = {"status": "passed" if passed else "failed", "execution": run, "original_sha256": release.sha(raw),
              "adapted_sha256": release.sha(file.read_bytes()), "module_rewrites": rules, "kernel": lines}
    (directory / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("entry")
    for command in ("source", "build", "trust", "types", "scoped-kernel"):
        child = commands.add_parser(command)
        child.add_argument("--output", required=True)
        if command == "source":
            child.add_argument("--exact", action="store_true")
        elif command != "scoped-kernel":
            child.add_argument("--package", action="append")
    args = parser.parse_args()
    try:
        with book_map():
            if args.command == "entry":
                result = entry(release.ROOT)
            elif args.command == "source":
                result = source(release.ROOT, args.output, exact=args.exact)
            elif args.command == "types":
                result = whole_ledger.types(args.output, args.package)
            elif args.command == "scoped-kernel":
                result = scoped_kernel(release.ROOT, args.output)
            else:
                result = release.execute(args.command, release.ROOT, MAP, args.output, args.package)
        success = result.get("ok", result.get("status") == "passed")
        print(json.dumps({"command": args.command, "status": "passed" if success else "failed",
                          **{k: v for k, v in result.items() if k in {
                              "families", "selected_roots", "proof_owners", "exact_sources", "resources",
                              "complete_types", "view", "files", "receipt", "kernel"}}}, ensure_ascii=False))
        return 0 if success else 1
    except (release.ReleaseError, source_view.ViewError, OSError, ValueError, TypeError, KeyError, StopIteration) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, ensure_ascii=False))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
