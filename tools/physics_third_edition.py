#!/usr/bin/env python3
"""Verify and rebuild the fixed third-edition physics proof selection."""

from __future__ import annotations

import argparse
from collections import defaultdict
from contextlib import contextmanager
import json
from pathlib import Path

import first_release as release
import generated_society as finite
import society_book
import source_view
import whole_ledger


MAP = "docs/physics-third-edition-map.json"
SELECTION = "checks/physics-third-edition-selection.json"
SCHEMA = "h0mework/physics-third-edition-map@1"
CLAIMS = {"phys.P45", "phys.P46", "phys.P47"}


@contextmanager
def physics_map():
    previous = release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP
    release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = SCHEMA, SCHEMA, MAP
    try:
        yield
    finally:
        release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = previous


def entry(root):
    identity = release.verify_map(root, MAP, require_ready=True)
    finite.require(identity["ok"], "Third-edition source map failed: " + str(identity["errors"]))
    data = release.read_json(root / MAP)
    claims = release.selected_claims(data)
    finite.require({claim["id"] for claim in claims} == CLAIMS,
                   "Third-edition selection must cover P45–P47")
    selection, exported, epochs = finite.selected_views(root, selection_path=SELECTION)
    finite.require(data["acceptance"]["selection_sha256"] == release.sha((root / SELECTION).read_bytes()),
                   "Accepted physics selection changed")
    scopes, entries = finite.package_scopes(data, exported, root)
    compiled = {path for scope in scopes.values() for path in scope["files"]}
    owners = {row["target"] for epoch in epochs.values() for row in epoch["modules"].values()}
    inverse = {row["target"]: row for row in exported["modules"]}
    reached = defaultdict(list)
    for row in inverse.values():
        if row["path"] in compiled:
            reached[row["source_path"], row["source_sha256"]].append(row["target"])
    matched = set()
    for target in owners:
        row = inverse[target]
        if row["path"] not in compiled:
            finite.require(any(finite.same_compiled_source(root, inverse, actual, target, matched)
                               for actual in reached[row["source_path"], row["source_sha256"]]),
                           "Third-edition selection has an unbuilt module owner: " + target)
    named, receipts = set(), set()
    for _, role, _, row in release.claim_entries(claims):
        commit, path = row["source_commit"], row["source_path"]
        artifact = release.entry_kind(role, row) == "artifact"
        recovered = epochs[commit]["artifacts" if artifact else "modules"].get(path)
        finite.require(recovered is not None and recovered["path"] == row["public"]["path"],
                       "Claim uses a source outside the fixed selection: " + path)
        (receipts if artifact else named).add((commit, path))
    for package in release.packages(data):
        named.update((row["source_commit"], row["source_path"]) for row in package.get("controls", []))
    expected_roots = {(group["source_commit"], path) for group in selection["selections"]
                      for path in group.get("roots", [])}
    expected_receipts = {(group["source_commit"], path) for group in selection["selections"]
                         for path in group.get("artifacts", [])}
    finite.require(expected_roots <= named and expected_receipts == receipts,
                   "Claim and control bindings do not cover the fixed physics selection")
    for view in ("public", "exact"):
        restored = finite.artifact(root, data["acceptance"]["source_" + view])
        finite.require(restored["status"] == "passed" and restored["view"] == view
                       and restored["selection_sha256"] == data["acceptance"]["selection_sha256"],
                       "Recorded source recovery differs: " + view)
    types = finite.recorded_acceptance(data, scopes, entries, root)
    return {"status": "passed", "claims": len(claims), "proof_owners": len(owners),
            "complete_types": types, "original_artifacts": len(receipts)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("entry")
    for name in ("build", "trust", "types", "source"):
        command = commands.add_parser(name)
        command.add_argument("--output", required=True, type=Path)
        if name == "source":
            command.add_argument("--exact", action="store_true")
            command.add_argument("--private-originals", type=Path)
        else:
            command.add_argument("--package", action="append")
    args = parser.parse_args(argv)
    root = release.ROOT
    try:
        with physics_map():
            if args.command == "entry":
                result = entry(root)
            elif args.command == "source":
                result = society_book.source(root, args.output, exact=args.exact, selection_path=SELECTION,
                                             private_originals=args.private_originals)
                result.update(schema="h0mework/physics-third-edition-source@1",
                              selection_sha256=release.sha((root / SELECTION).read_bytes()))
                (root / args.output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
            elif args.command == "types":
                result = whole_ledger.types(args.output, args.package)
            else:
                result = release.execute(args.command, root, MAP, args.output, args.package)
        passed = result.get("ok", result.get("status") == "passed")
        print(json.dumps({"command": args.command, "status": "passed" if passed else "failed",
                          **{key: result[key] for key in ("claims", "proof_owners", "complete_types",
                              "original_artifacts", "view", "files", "receipt") if key in result}}, ensure_ascii=False))
        return 0 if passed else 1
    except (release.ReleaseError, source_view.ViewError, OSError, ValueError, TypeError, KeyError) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, ensure_ascii=False))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
