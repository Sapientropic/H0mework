#!/usr/bin/env python3
"""Verify and rebuild the fixed public War and Peace proof selection."""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import json
from pathlib import Path

from enforceable_peace_replay import activation_files
import first_release as release
import generated_society as finite
import society_book
import source_view
import whole_ledger


MAP = "docs/enforceable-peace-map.json"
SELECTION = "checks/enforceable-peace-selection.json"
SCHEMA = "h0mework/enforceable-peace-map@1"
CLAIMS = {f"PE{number}" for number in range(1, 34)}


@contextmanager
def peace_map():
    previous = release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP
    release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = SCHEMA, SCHEMA, MAP
    try:
        yield
    finally:
        release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = previous


def entry(root):
    verified = release.verify_map(root, MAP, require_ready=True)
    finite.require(verified["ok"], "Peace source map failed: " + str(verified["errors"]))
    data = release.read_json(root / MAP)
    claims = release.selected_claims(data)
    finite.require({claim["id"] for claim in claims} == CLAIMS,
                   "Peace selection must cover PE1–PE33")
    selection, exported, epochs = finite.selected_views(root, selection_path=SELECTION)
    finite.require(data["acceptance"]["selection_sha256"] == release.sha((root / SELECTION).read_bytes()),
                   "Accepted peace selection changed")
    scopes, entries = finite.package_scopes(data, exported, root)
    compiled = {path for scope in scopes.values() for path in scope["files"]}
    owners = {row["path"] for epoch in epochs.values() for row in epoch["modules"].values()}
    finite.require(owners <= compiled, "Peace selection has unbuilt module owners")
    for claim, role, _, entry_row in release.claim_entries(claims):
        epoch = epochs[entry_row["source_commit"]]
        kind = "artifacts" if release.entry_kind(role, entry_row) == "artifact" else "modules"
        recovered = epoch[kind].get(entry_row["source_path"])
        finite.require(recovered is not None and recovered["path"] == entry_row["public"]["path"],
                       "Peace claim uses an owner outside its fixed selection: " + claim["id"])
    expected = {}
    for group in selection["selections"]:
        epoch = group["source_commit"]
        for name, roles in group.get("claim_roots", {}).items():
            for role, paths in roles.items():
                for path in paths:
                    module = epochs[epoch]["modules"][path]["target"]
                    expected.setdefault(name, set()).add((epoch, path, module, role))
    finite.require(set(expected) == CLAIMS, "Fixed selection is missing a paper claim")
    for claim in claims:
        roots = {(row["source_commit"], row["source_path"], row["public_module"], row["role"])
                 for row in claim["selection_roots"]}
        finite.require(roots == expected[claim["id"]] and claim["direct_consumers"],
                       "Peace claim root or direct consumer differs: " + claim["id"])
    count = finite.recorded_acceptance(data, scopes, entries, root)
    online = {name: finite.artifact(root, reference)
              for name, reference in data["online_evidence"].items()}
    kernel_hashes = {"legacy": online["legacy"]["direct_axioms_sha256"],
                     **{name: online[name]["kernel"]["axioms_sha256"] for name in ("recovery", "handoff")}}
    for name, digest in kernel_hashes.items():
        trace = data["original_kernel_traces"][name]
        raw = release.repo_file(root, trace["path"]).read_bytes()
        finite.require(release.sha(raw) == trace["sha256"] == digest,
                       "Original kernel trace differs: " + name)
    deployment = epochs[data["deployment_epochs"]["handoff"]]
    activation, _ = activation_files(root, data, deployment)
    replay = finite.artifact(root, data["acceptance"]["offline_replay"])
    finite.require(replay["status"] == "passed" and replay["signed_rows"] == 27
                   and replay["native_rows"] == 27 and replay["final_clock"] == "28"
                   and replay["activation_release"] == activation
                   and replay["activation_inventory_sha256"] == data["activation_extraction"]["sha256"]
                   and replay["fixtures"] == {"original_recovery_disjoint_rosters": "passed",
                                              "original_ordered_handoff_disposition": "passed"}
                   and replay["production_node_calls"] == 0,
                   "Independent peace replay did not reach the original signed tip")
    finite.require(replay["inputs"] == {
        name: reference["sha256"] for name, reference in data["online_evidence"].items()
    }, "Offline replay inputs differ from the paper evidence")
    return {"status": "passed", "claims": len(claims), "proof_owners": len(owners),
            "complete_types": count, "signed_rows": replay["signed_rows"], "final_clock": replay["final_clock"]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("entry")
    for name in ("build", "trust", "types", "source", "replay"):
        command = commands.add_parser(name)
        command.add_argument("--output", required=True, type=Path)
        if name in {"build", "trust", "types"}:
            command.add_argument("--package", action="append")
        if name == "source":
            command.add_argument("--exact", action="store_true")
            command.add_argument("--private-originals", type=Path)
    args = parser.parse_args(argv)
    root = release.ROOT
    try:
        with peace_map():
            if args.command == "entry":
                result = entry(root)
            elif args.command == "source":
                result = society_book.source(root, args.output, exact=args.exact, selection_path=SELECTION,
                                             private_originals=args.private_originals)
            elif args.command == "types":
                result = whole_ledger.types(args.output, args.package)
            elif args.command == "replay":
                from enforceable_peace_replay import replay

                result = replay(root, MAP, SELECTION, args.output)
            else:
                result = release.execute(args.command, root, MAP, args.output, args.package)
        passed = result.get("ok", result.get("status") == "passed")
        print(json.dumps({"command": args.command, "status": "passed" if passed else "failed",
                          **{key: result[key] for key in (
                              "claims", "proof_owners", "complete_types", "signed_rows", "final_clock",
                              "view", "files", "receipt"
                          ) if key in result}}, ensure_ascii=False))
        return 0 if passed else 1
    except (release.ReleaseError, source_view.ViewError, OSError, ValueError, TypeError, KeyError) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, ensure_ascii=False))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
