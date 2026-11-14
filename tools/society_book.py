#!/usr/bin/env python3
"""Verify and rebuild the book's additional public society proofs."""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import json
from pathlib import Path
import re

import first_release as release
import generated_society as finite
import source_view
import whole_ledger


MAP = "checks/society-book-map.json"
SELECTION = "checks/society-book-selection.json"
SUPPLEMENT_MAP = "checks/society-book-supplement-map.json"
SUPPLEMENT_SELECTION = "checks/society-book-supplement-selection.json"
SCHEMA = "h0mework/society-book-map@1"


@contextmanager
def book_map(path=MAP):
    previous = release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP
    release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = SCHEMA, SCHEMA, path
    try:
        yield
    finally:
        release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = previous


def verify_supply_91(root, reference, epochs):
    accepted = finite.artifact(root, reference)
    inventory = accepted["inventory"]
    epoch = epochs[inventory["original_receipt_commit"]]
    source = inventory["original_receipt"]
    raw = epoch["outputs"][source]
    receipt = json.loads(raw)
    profile = inventory["profile"]
    actual = accepted["original_readback"]
    finite.require(release.sha(raw) == inventory["original_receipt_sha256"]
                   and (receipt["seq"], receipt["status"], receipt["clock"]) == (91, "SUPPLIED", "137")
                   and receipt["checkpoint"] == profile["checkpoint"]
                   and receipt["protocol"] == profile["revision"]
                   and len(profile["files"]) == receipt["runtime_files"],
                   "Source-supply receipt or installed profile changed")
    canonical = json.dumps(profile["files"], ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
    finite.require(release.sha(canonical) == receipt["protocol"], "Installed supply program identity differs")
    consumer = receipt["consumer"]
    finite.require(epoch["artifacts"][consumer["path"]]["source_sha256"] == consumer["sha256"],
                   "Original supply readback program differs")
    installed = epochs[profile["checkpoint"]]["artifacts"]
    for name, digest in profile["files"].items():
        path = "Verification/public-audit/network/" + name
        finite.require(installed[path]["source_sha256"] == digest, "Installed supply program differs: " + name)
    for path in inventory["consumer_sources"]:
        finite.require(path in epoch["artifacts"], "Missing original supply consumer: " + path)
    expected = {name: digest for name, digest in receipt["receipts"].items() if name != "lookups"}
    expected.update({"lookups/" + name: digest for name, digest in receipt["receipts"]["lookups"].items()})
    finite.require(expected.keys() == inventory["receipt_inputs"].keys(), "Original supply receipt inventory differs")
    for name, path in inventory["receipt_inputs"].items():
        row = epoch["artifacts"][path]
        finite.require(release.sha(epoch["outputs"][path]) == row["source_sha256"] == expected[name],
                       "Original supply receipt bytes differ: " + name)
    fixture = accepted["offline_fixture"]
    finite.require(accepted["status"] == "passed" and actual["exit_code"] == 0
                   and actual["reconstructed_receipt_sha256"] == expected["actual"]
                   and fixture["rpc"] == fixture["economic_requests"] == 0
                   and fixture["live_deployment"] is False,
                   "Source-supply readback and local controls did not pass")
    return len(expected)


def entry(root, map_path=MAP, selection_path=SELECTION):
    identity = release.verify_map(root, map_path, require_ready=True)
    finite.require(identity["ok"], "Book source map failed: " + str(identity["errors"]))
    selection, exported, epochs = finite.selected_views(root, exact=map_path == MAP, selection_path=selection_path)
    data = release.read_json(root / map_path)
    finite.require(data["acceptance"]["selection_sha256"] == release.sha((root / selection_path).read_bytes()),
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
        kind = "artifacts" if release.entry_kind(role, row) == "artifact" else "modules"
        record = epochs[row["source_commit"]][kind].get(row["source_path"])
        finite.require(record is not None and record["path"] == row["public"]["path"],
                       "Claim map uses a different source owner: " + row["source_path"])
    runtime = {}
    if map_path == SUPPLEMENT_MAP:
        gaps = {(row["source_commit"], path)
                for row in selection["selections"] for path in row["audited_gaps"]}
        finite.require(len(gaps) == 29 and gaps <= selected, "Book supplement lost an audited gap")
        runtime["audited_gaps"] = len(gaps)
        runtime["original_supply_receipts"] = verify_supply_91(root, data["acceptance"]["supply_91"], epochs)
        readers = finite.artifact(root, data["acceptance"]["standalone_readers"])
        expected_readers = {(row["source_commit"], path)
                            for row in selection["selections"] for path in row["standalone_readers"]}
        checked_readers = {(row["source_commit"], row["source_path"]) for row in readers["readers"]}
        finite.require(readers["status"] == "passed" and checked_readers == expected_readers
                       and len(readers["readers"]) == len(expected_readers),
                       "Book standalone reader inventory differs from the selected originals")
        for row in readers["readers"]:
            epoch, path = row["source_commit"], row["source_path"]
            finite.require(row["exit_code"] == 0 and row["source_sha256"] == epochs[epoch]["artifacts"][path]["source_sha256"],
                           "Book standalone reader did not check the selected original: " + path)
        runtime["standalone_readers"] = len(checked_readers)
    else:
        kernel = finite.artifact(root, data["acceptance"]["scoped_kernel"])
        finite.require(kernel["status"] == "passed" and kernel["execution"]["exit_code"] == 0,
                       "Scoped audit did not pass its independent kernel replay")
    checked_types = finite.recorded_acceptance(data, scopes, entries, root)
    return {"status": "passed", "families": identity["claims"], "selected_roots": len(selected),
            "proof_owners": len(proof_paths), "exact_sources": sum(len(s["modules"]) for s in epochs.values()),
            "resources": sum(len(s["artifacts"]) for s in epochs.values()), "complete_types": checked_types, **runtime}


def source(root, output, *, exact, selection_path=SELECTION, private_originals=None):
    selection, _, epochs = finite.selected_views(root, exact=exact, selection_path=selection_path,
                                                 private_originals=private_originals)
    restored = set()
    for binding in selection.get("original_source_bodies", []):
        revision, path = binding["source_commit"], binding["source_path"]
        finite.require((revision, path) not in restored and revision in epochs and path in epochs[revision]["modules"],
                       "Original source binding lies outside the selection or repeats: " + path)
        state = epochs[revision]
        owner = state["modules"][path]
        origin = owner.get("source_origin", {})
        raw = release.repo_file(root, binding["original_artifact"]).read_bytes()
        original_path = origin.get("original_source_path", origin.get("original_path", origin.get("source_path")))
        original_sha = origin.get("original_source_sha256")
        if original_sha is None and origin.get("kind") == "git-source-supplement":
            # Older signed rows carry the replacement's Git SHA only. The
            # original and effective byte identities are pinned by the selection.
            original_sha = binding["source_sha256"]
        finite.require(
            owner["source_sha256"] == binding["effective_sha256"]
            and original_path == path
            and original_sha == release.sha(raw) == binding["source_sha256"],
            "Archived source body differs from the registered original: " + path,
        )
        if exact:
            state["outputs"][path] = raw
        restored.add((revision, path))
    directory = release.new_output(root, output)
    for epoch, state in epochs.items():
        for path, body in state["outputs"].items():
            target = directory / epoch / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(body)
    return {"status": "passed", "view": "exact" if exact else "public",
            "files": sum(len(s["outputs"]) for s in epochs.values()),
            **({"archived_originals": len(restored)} if restored else {})}


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
    parser.add_argument("--supplement", action="store_true", help="use the audited book follow-up selection")
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("entry")
    for command in ("source", "build", "trust", "types", "scoped-kernel"):
        child = commands.add_parser(command)
        child.add_argument("--output", required=True)
        if command == "source":
            child.add_argument("--exact", action="store_true")
            child.add_argument("--private-originals", type=Path)
        elif command != "scoped-kernel":
            child.add_argument("--package", action="append")
    args = parser.parse_args()
    map_path, selection_path = (SUPPLEMENT_MAP, SUPPLEMENT_SELECTION) if args.supplement else (MAP, SELECTION)
    if args.supplement and args.command == "scoped-kernel":
        parser.error("scoped-kernel is the original PF10/PF11 kernel replay")
    try:
        with book_map(map_path):
            if args.command == "entry":
                result = entry(release.ROOT, map_path, selection_path)
            elif args.command == "source":
                result = source(release.ROOT, args.output, exact=args.exact, selection_path=selection_path,
                                private_originals=args.private_originals)
            elif args.command == "types":
                result = whole_ledger.types(args.output, args.package)
            elif args.command == "scoped-kernel":
                result = scoped_kernel(release.ROOT, args.output)
            else:
                result = release.execute(args.command, release.ROOT, map_path, args.output, args.package)
        success = result.get("ok", result.get("status") == "passed")
        print(json.dumps({"command": args.command, "status": "passed" if success else "failed",
                          **{k: v for k, v in result.items() if k in {
                              "families", "selected_roots", "proof_owners", "exact_sources", "resources",
                              "complete_types", "view", "files", "receipt", "kernel",
                              "audited_gaps", "original_supply_receipts", "standalone_readers"}}}, ensure_ascii=False))
        return 0 if success else 1
    except (release.ReleaseError, source_view.ViewError, OSError, ValueError, TypeError, KeyError, StopIteration) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, ensure_ascii=False))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
