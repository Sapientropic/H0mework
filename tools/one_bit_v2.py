#!/usr/bin/env python3
"""Recover and independently check the One Bit second-edition proof additions."""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path

import first_release as release
import generated_society as finite
import society_book
import source_view
import whole_ledger

MAP = "docs/one-bit-v2-map.json"
SELECTION = "checks/one-bit-v2-selection.json"
SCHEMA = "h0mework/one-bit-v2-map@1"
CLAIMS = {"OB2", "OB12", "OB13"}


def entry(root):
    identity = release.verify_map(root, MAP, require_ready=True)
    finite.require(identity["ok"], "One Bit v2 map failed: " + str(identity["errors"] or identity["pending"]))
    data = release.read_json(root / MAP)
    claims = release.selected_claims(data)
    finite.require({claim["id"] for claim in claims} == CLAIMS, "One Bit v2 requires OB2, OB12 and OB13")
    prior = data["prior_proof_map"]
    finite.require(release.sha(release.repo_file(root, prior["path"]).read_bytes()) == prior["sha256"],
                   "Inherited One Bit map changed")
    selection, exported, epochs = finite.selected_views(root, selection_path=SELECTION)
    selection_sha = release.sha((root / SELECTION).read_bytes())
    finite.require(selection_sha == data["acceptance"]["selection_sha256"], "Accepted selection changed")
    scopes, entries = finite.package_scopes(data, exported, root)
    compiled = {path for scope in scopes.values() for path in scope["files"]}
    inverse = {row["target"]: row for row in exported["modules"]}
    reached = defaultdict(list)
    for row in inverse.values():
        if row["path"] in compiled:
            reached[row["source_path"], row["source_sha256"]].append(row["target"])
    modules = {(epoch, path): row for epoch, state in epochs.items() for path, row in state["modules"].items()}
    artifacts = {(epoch, path): row for epoch, state in epochs.items() for path, row in state["artifacts"].items()}
    matched = set()
    for row in modules.values():
        if row["path"] not in compiled:
            finite.require(any(finite.same_compiled_source(root, inverse, actual, row["target"], matched)
                               for actual in reached[row["source_path"], row["source_sha256"]]),
                           "Original module is outside the built closure: " + row["target"])

    mapped_modules, mapped_artifacts = set(), set()
    for _, role, _, row in release.claim_entries(claims):
        key = row["source_commit"], row["source_path"]
        is_artifact = release.entry_kind(role, row) == "artifact"
        recovered = (artifacts if is_artifact else modules).get(key)
        finite.require(recovered is not None and recovered["path"] == row["public"]["path"],
                       "Map entry differs from the fixed selection: " + key[1])
        (mapped_artifacts if is_artifact else mapped_modules).add(key)
    for claim in claims:
        resources = {Path(row["source_path"]).name: row for row in claim.get("resources", [])}
        if resources:
            check_original_receipts(claim, resources, epochs)
    for package in release.packages(data):
        for control in package.get("controls", []):
            key = control["source_commit"], control["source_path"]
            finite.require(modules[key]["path"] == control["public"]["path"], "Firewall owner changed")
            raw = epochs[key[0]]["outputs"][key[1]].decode()
            finite.require(raw.count("\n#guard_msgs in\n") == control["original_guard_commands"]
                           and len(source_view.import_tokens(raw)) == control["original_direct_imports"],
                           "Original firewall guard or import inventory changed")
            mapped_modules.add(key)
    roots = {(group["source_commit"], path)
             for group in selection["selections"] for path in group.get("roots", [])}
    finite.require(roots <= mapped_modules and artifacts.keys() == mapped_artifacts,
                   "Map omits a selected root or original receipt")
    for view in ("public", "exact"):
        receipt = finite.artifact(root, data["acceptance"]["source_" + view])
        finite.require(receipt["status"] == "passed" and receipt["view"] == view
                       and receipt["selection_sha256"] == selection_sha
                       and receipt["files"] == len(modules) + len(artifacts), "Source recovery differs: " + view)
    types = finite.recorded_acceptance(data, scopes, entries, root)
    return {"status": "passed", "claims": len(claims), "source_identities": len(modules),
            "proof_owners": len({row["target"] for row in modules.values()}),
            "original_artifacts": len(artifacts), "complete_types": types}


def check_original_receipts(claim, resources, epochs):
    certificate = resources["publication-certificate.json"]
    outputs = epochs[certificate["source_commit"]]["outputs"]
    original = json.loads(outputs[certificate["source_path"]])
    verdict = json.loads(outputs[resources["verdict.json"]["source_path"]])
    finite.require(original["verdict"] == "PASS" and verdict["verdict"] == "certified",
                   "Original certification status differs: " + claim["id"])
    for field, name in (("source_verdict", "verdict.json"), ("same_occurrence_chain", "same-chain.json")):
        finite.require(original[field]["sha256"] == resources[name]["source_sha256"],
                       "Original certificate child digest differs: " + claim["id"] + "/" + name)
    proofs = {row["source_path"]: row["source_sha256"]
              for role in ("producers", "direct_consumers") for row in claim[role]}
    for candidate in original["candidates"]:
        binding = candidate["source"]
        _, marker, suffix = binding["path"].partition("/source-root/")
        finite.require(marker and proofs.get("Lean/" + suffix) == binding["sha256"],
                       "Original certificate source binding differs: " + claim["id"] + "/" + suffix)


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
    previous = release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP
    release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = SCHEMA, SCHEMA, MAP
    try:
        if args.command == "entry":
            result = entry(root)
        elif args.command == "source":
            result = society_book.source(root, args.output, exact=args.exact, selection_path=SELECTION,
                                         private_originals=args.private_originals)
            result.update(schema="h0mework/one-bit-v2-source@1",
                          selection_sha256=release.sha((root / SELECTION).read_bytes()))
            (root / args.output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
        elif args.command == "types":
            result = whole_ledger.types(args.output, args.package)
        else:
            result = release.execute(args.command, root, MAP, args.output, args.package)
        passed = result.get("ok", result.get("status") == "passed")
        fields = ("claims", "source_identities", "proof_owners", "original_artifacts",
                  "complete_types", "view", "files", "receipt")
        print(json.dumps({"status": "passed" if passed else "failed",
                          **{key: result[key] for key in fields if key in result}}, ensure_ascii=False))
        return 0 if passed else 1
    except (release.ReleaseError, source_view.ViewError, OSError, ValueError, TypeError, KeyError) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, ensure_ascii=False))
        return 1
    finally:
        release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = previous


if __name__ == "__main__":
    raise SystemExit(main())
