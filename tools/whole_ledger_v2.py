#!/usr/bin/env python3
"""Recover and independently verify the whole-ledger second-edition additions."""

from __future__ import annotations

import argparse
from io import BytesIO
import json
from pathlib import Path
from zipfile import ZipFile

import first_release as release
import generated_society as finite
import society_book
import whole_ledger

MAP = "docs/whole-ledger-v2-map.json"
SELECTION = "checks/whole-ledger-v2-selection.json"
SCHEMA = "h0mework/whole-ledger-v2-map@1"
ADDITIONS = {"WA43", "WA44", "WA45"}


def verify_certifications(root, data, modules, artifacts, epochs):
    certifications = data["original_certifications"]
    expected = {cp for claim in data["claims"] for cp in claim.get("original_certifications", [])}
    finite.require(set(certifications) == expected, "Original checkpoint inventory differs")
    for checkpoint, record in certifications.items():
        commit, certificate = record["source_commit"], record["certificate"]
        outputs = epochs[commit]["outputs"]
        payload = json.loads(outputs[certificate])
        identity = artifacts[commit, certificate]
        finite.require(payload["checkpoint"] == checkpoint and payload["verdict"] == "certified"
                       and identity["source_sha256"] == record["source_sha256"]
                       and identity["path"] == record["public_certificate"],
                       "Original certification identity differs: " + checkpoint)
        for item in record["native_codegen"]:
            source = artifacts[commit, item["source_path"]]
            finite.require(source["source_sha256"] == item["source_sha256"]
                           == payload["native_codegen"][item["certificate_field"]],
                           "Original generated material differs: " + checkpoint)
        directory = certificate.rsplit("/", 1)[0]
        manifest = json.loads(outputs[directory + "/manifest.json"])
        expected_members = {source: artifacts[commit, source]["source_sha256"] for source in record["artifacts"]}
        for member in record["compiled_members"]:
            row = modules[member["source_commit"], member["source_path"]]
            finite.require(row["path"] == member["public_path"] and row["source_sha256"] == member["source_sha256"],
                           "Original gate source differs: " + checkpoint)
            expected_members[member["source_path"]] = member["source_sha256"]
        for member in manifest.get("members", manifest.get("files", [])):
            path = directory + "/" + member["path"]
            finite.require(expected_members.get(path) == member["sha256"],
                           "Original certification member differs: " + path)
        archive = record.get("historical_source_archive")
        if archive is not None:
            raw = release.repo_file(root, archive["path"]).read_bytes()
            finite.require(release.sha(raw) == archive["sha256"], "Historical source archive differs: " + checkpoint)
            inputs = json.loads(outputs[directory + "/inputs.json"])
            sources = {"Lean/" + item["module"].replace(".", "/") + ".lean": item["source_sha256"]
                       for item in inputs["science"]}
            with ZipFile(BytesIO(raw)) as bundle:
                meta = json.loads(bundle.read("source-manifest.json"))
                finite.require(meta["source_commit"] == commit and meta["certification"] == certificate
                               and meta["files"] == archive["files"] and
                               set(bundle.namelist()) == {*sources, "source-manifest.json"},
                               "Historical source inventory differs: " + checkpoint)
                for member in meta["files"]:
                    raw = bundle.read(member["path"])
                    finite.require(len(raw) == member["bytes"] and release.sha(raw) == member["sha256"]
                                   == sources[member["path"]], "Historical source differs: " + member["path"])


def entry(root):
    data = release.read_json(root / MAP)
    identity = release.verify_map(root, MAP, require_ready=True)
    finite.require(identity["ok"], "Whole-ledger v2 map failed: " + str(identity["errors"] or identity["pending"]))
    claims = release.selected_claims(data)
    finite.require({claim["id"] for claim in claims} == {"WA4", "WA41", "WA42", *ADDITIONS},
                   "Whole-ledger v2 claim inventory differs")
    for prior in data["prior_proof_maps"]:
        finite.require(release.sha(release.repo_file(root, prior["path"]).read_bytes()) == prior["sha256"],
                       "Inherited proof map changed: " + prior["path"])
    selection, exported, epochs = finite.selected_views(root, selection_path=SELECTION)
    selection_sha = release.sha((root / SELECTION).read_bytes())
    finite.require(data["selection"]["sha256"] == selection_sha, "Whole-ledger v2 selection differs")
    scopes, entries = finite.package_scopes(data, exported, root)
    compiled = {path for scope in scopes.values() for path in scope["files"]}
    modules = {(epoch, path): row for epoch, state in epochs.items() for path, row in state["modules"].items()}
    artifacts = {(epoch, path): row for epoch, state in epochs.items() for path, row in state["artifacts"].items()}
    finite.require({row["path"] for row in modules.values()} <= compiled,
                   "An original module is outside the compiled package closure")
    mapped_modules, mapped_artifacts = set(), set()
    for claim, role, _, row in release.claim_entries(claims):
        if claim["id"] not in ADDITIONS:
            continue
        key = row["source_commit"], row["source_path"]
        resource = release.entry_kind(role, row) == "artifact"
        recovered = (artifacts if resource else modules).get(key)
        finite.require(recovered is not None and recovered["path"] == row["public"]["path"],
                       "Map entry differs from its fixed selection: " + key[1])
        (mapped_artifacts if resource else mapped_modules).add(key)
    roots = {(group["source_commit"], path) for group in selection["selections"] for path in group.get("roots", [])}
    finite.require(roots == mapped_modules and artifacts.keys() == mapped_artifacts,
                   "Map omits a selected proof root or original artifact")
    verify_certifications(root, data, modules, artifacts, epochs)
    acceptance = data["acceptance"]
    build_receipt = finite.artifact(root, acceptance["build"])
    accepted_inputs = build_receipt["input_identity"]["sha256"]
    accepted_export = accepted_inputs["export_map"]
    finite.require(accepted_inputs["claim_map"] == acceptance["execution_map_sha256"],
                   "Whole-ledger v2 execution map differs")
    for view in ("public", "exact"):
        receipt = finite.artifact(root, acceptance["source_" + view])
        finite.require(receipt["status"] == "passed" and receipt["view"] == view
                       and receipt["selection_sha256"] == selection_sha
                       and receipt["export_map_sha256"] == accepted_export
                       and receipt["files"] == len(modules) + len(artifacts), "Source recovery differs: " + view)
    cache = finite.artifact(root, acceptance["cache_preservation"])
    finite.require(cache["default_build_coverage"] == "passed" and not cache["invalidated_shards"]
                   and cache["source_identity_audit"]["export_map_sha256"] == accepted_export,
                   "Whole-ledger v2 CI cache preservation differs")
    science = [finite.artifact(root, receipt) for receipt in acceptance["first_release_scientific_cache"]]
    finite.require({receipt["kind"] for receipt in science} == {"bell", "quantum"}
                   and all(receipt["status"] == "reused" and receipt["current_map_sha256"] == accepted_export
                           for receipt in science), "First-release scientific reuse differs")
    canonical = finite.artifact(root, acceptance["cp532_canonical_application"])
    finite.require(canonical["schema"] == "cp532-canonical-shared-method-application/v1"
                   and canonical["accepted"] is True and canonical["kernel_add_decl_calls"] == 1
                   and canonical["Meta_calls"] == 0 and canonical["new_proof_premises"] == 0
                   and len(canonical["conjoined_claims"]) == 3, "CP532 canonical method replay differs")
    types = finite.recorded_acceptance(data, scopes, entries, root)
    return {"status": "passed", "claims": len(claims), "source_identities": len(modules),
            "proof_owners": len({row["target"] for row in modules.values()}),
            "original_artifacts": len(artifacts), "complete_types": types}


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
            selection_sha = release.sha((root / SELECTION).read_bytes())
            export_sha = release.sha((root / release.EXPORT_MAP).read_bytes())
            result = society_book.source(root, args.output, exact=args.exact, selection_path=SELECTION,
                                         private_originals=args.private_originals)
            finite.require(selection_sha == release.sha((root / SELECTION).read_bytes())
                           and export_sha == release.sha((root / release.EXPORT_MAP).read_bytes()),
                           "Source recovery inputs changed during execution")
            result.update(schema="h0mework/whole-ledger-v2-source@1",
                          selection_sha256=selection_sha, export_map_sha256=export_sha)
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
    except (release.ReleaseError, OSError, ValueError, KeyError) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, ensure_ascii=False))
        return 1
    finally:
        release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = previous


if __name__ == "__main__":
    raise SystemExit(main())
