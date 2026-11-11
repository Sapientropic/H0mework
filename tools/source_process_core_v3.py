#!/usr/bin/env python3
"""Verify the third-edition process-core bindings and its MV4 proof package."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import first_release as release
import generated_society as finite
import society_book
import whole_ledger

MAP = "docs/source-process-core-v3-map.json"
SELECTION = "checks/source-process-core-v3-selection.json"
SCHEMA = "h0mework/source-process-core-v3-map@1"
FOUNDATION_CHECK = "checks/source-process-core-v3-t0.lean"


def verify_shared(root, data):
    groups = {}
    for binding in data["shared_claims"]:
        groups.setdefault(binding["map"], set()).add(binding["claim_id"])
    for path, expected in groups.items():
        shared = release.read_json(root / path)
        claims = [c for c in release.selected_claims(shared) if c["id"] in expected]
        finite.require({claim["id"] for claim in claims} == expected,
                       "Shared claim is missing from " + path)
        keys = {(c["id"], role, index) for c, role, index, _ in release.claim_entries(claims)}
        original = release.SCHEMA
        try:
            release.SCHEMA = shared["schema"]
            checked = release.verify_map(root, path, require_ready=True, entry_keys=keys)
        finally:
            release.SCHEMA = original
        finite.require(checked["ok"], "Shared proof acceptance differs: " + path)
        finite.artifact(root, shared["acceptance"]["declaration_types"])


def entry(root):
    data = release.read_json(root / MAP)
    mapped = release.verify_map(root, MAP, require_ready=True)
    finite.require(mapped["ok"], "Process-core proof map is incomplete")
    for prior in data["frozen_proof_maps"]:
        finite.require(release.sha((root / prior["path"]).read_bytes()) == prior["sha256"],
                       "Frozen proof map differs: " + prior["path"])
    ids = {c["id"] for c in data["claims"] + data["shared_claims"]}
    finite.require(ids == {f"C{n}" for n in range(46, 55)}, "Process-core additions differ")
    verify_shared(root, data)

    selection, exported, epochs = finite.selected_views(root, selection_path=SELECTION)
    selection_sha = release.sha((root / SELECTION).read_bytes())
    finite.require(data["selection"]["sha256"] == selection_sha, "Selection digest differs")
    scopes, entries = finite.package_scopes(data, exported, root)
    paths = {path for scope in scopes.values() for path in scope["files"]}
    finite.require({row["path"] for epoch in epochs.values() for row in epoch["modules"].values()} <= paths,
                   "Selected source is outside the actual MV4 build closure")

    mapped_roots, mapped_resources = set(), set()
    for claim, role, _, row in release.claim_entries(data["claims"]):
        revision, source = row["source_commit"], row["source_path"]
        state = epochs[revision]
        if release.entry_kind(role, row) == "lean":
            finite.require(state["modules"][source]["path"] == row["public"]["path"],
                           "Proof binding differs from the fixed selection: " + source)
            mapped_roots.add((revision, source))
            continue
        finite.require(state["artifacts"][source]["path"] == row["public"]["path"],
                       "Receipt binding differs from the fixed selection: " + source)
        mapped_resources.add((revision, source))
        verdict = json.loads(state["outputs"][source])
        origin = row["source_origin"]
        finite.require(verdict["checkpoint"] == origin["checkpoint"]
                       and verdict["fixed_head"] == revision and verdict["verdict"] == "certified",
                       "Original certification identity differs: " + origin["checkpoint"])
    roots = {(group["source_commit"], path) for group in selection["selections"] for path in group.get("roots", [])}
    resources = {(revision, path) for revision, state in epochs.items() for path in state["artifacts"]}
    finite.require(roots == mapped_roots and resources == mapped_resources,
                   "The map omits a selected proof root or original certification")

    acceptance = data["acceptance"]
    build = finite.artifact(root, acceptance["build"])
    accepted_export = build["input_identity"]["sha256"]["export_map"]
    finite.require(build["input_identity"]["sha256"]["claim_map"] == acceptance["execution_map_sha256"],
                   "Process-core execution map differs")
    recovered_count = sum(len(e["outputs"]) for e in epochs.values())
    for view in ("public", "exact"):
        receipt = finite.artifact(root, acceptance["source_" + view])
        finite.require(receipt["status"] == "passed" and receipt["view"] == view
                       and receipt["files"] == recovered_count and receipt["selection_sha256"] == selection_sha
                       and receipt["export_map_sha256"] == accepted_export,
                       "Process-core source recovery differs: " + view)
    t0 = finite.artifact(root, acceptance["t0_axioms"])
    program = (root / FOUNDATION_CHECK).read_bytes()
    requested = {line.removeprefix("#print axioms ") for line in program.decode().splitlines()
                 if line.startswith("#print axioms ")}
    recorded = {name.removeprefix(t0["namespace"] + "."): axioms for name, axioms in t0["roots"].items()}
    finite.require(t0["status"] == "passed" and t0["program"] == FOUNDATION_CHECK
                   and release.sha(program) == t0["program_sha256"] and requested == recorded.keys()
                   and all(axioms == (["propext"] if name == "RootedAccountedUnfolding.cardinalShadow_parallelAt" else [])
                           for name, axioms in recorded.items()), "The recorded foundation axiom check differs")
    return {"status": "passed", "additions": len(ids), "recovered_files": recovered_count,
            "complete_types": finite.recorded_acceptance(data, scopes, entries, root),
            "axiom_free_roots": sum(not axioms for axioms in recorded.values())}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("entry")
    for name in ("build", "trust", "types", "source"):
        child = commands.add_parser(name)
        child.add_argument("--output", type=Path, required=True)
        if name == "source":
            child.add_argument("--exact", action="store_true")
            child.add_argument("--private-originals", type=Path)
    args = parser.parse_args(argv)
    root = release.ROOT
    previous = release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP
    release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = SCHEMA, SCHEMA, MAP
    try:
        if args.command == "entry":
            result = entry(root)
        elif args.command == "source":
            selection_sha = release.sha((root / SELECTION).read_bytes())
            export_sha = release.sha((root / release.EXPORT_MAP).read_bytes())
            result = society_book.source(root, args.output, exact=args.exact, selection_path=SELECTION,
                                         private_originals=args.private_originals)
            finite.require(selection_sha == release.sha((root / SELECTION).read_bytes())
                           and export_sha == release.sha((root / release.EXPORT_MAP).read_bytes()),
                           "Source recovery inputs changed")
            result.update(selection_sha256=selection_sha, export_map_sha256=export_sha)
            (root / args.output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
        elif args.command == "types":
            result = whole_ledger.types(args.output)
        else:
            result = release.execute(args.command, root, MAP, args.output)
        passed = result.get("ok", result.get("status") == "passed")
        fields = ("additions", "recovered_files", "complete_types", "axiom_free_roots", "view", "files", "receipt")
        print(json.dumps({"status": "passed" if passed else "failed",
                          **{name: result[name] for name in fields if name in result}}))
        return 0 if passed else 1
    except (release.ReleaseError, OSError, ValueError, KeyError) as error:
        print(json.dumps({"status": "failed", "error": str(error)}))
        return 1
    finally:
        release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = previous


if __name__ == "__main__":
    raise SystemExit(main())
