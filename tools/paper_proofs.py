#!/usr/bin/env python3
"""Verify, build and recover the observation and certified Go proof selections."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import first_release as release
import generated_society as finite
import society_book
import source_view
import whole_ledger
import whole_ledger_export

ROOT = release.ROOT
PAPERS = {
    "observation-dynamics": ({f"O{i}" for i in range(1, 67)} - {"O25"}) | {"ForgettingBridge"},
    "certified-go": {f"GO{i}" for i in range(1, 9)},
}


def build_selected_roots(root, paper, selection_path, output):
    selection_raw = (root / selection_path).read_bytes()
    export_path = root / release.EXPORT_MAP
    export_hash = release.sha(export_path.read_bytes())
    selection = whole_ledger_export.load_selection(root / selection_path)
    owners = whole_ledger_export.public_owners(selection)
    with finite.source_root(root):
        _, index, _, _ = source_view.load_map()
    targets = set()
    for group in selection["selections"]:
        epoch = group["source_commit"]
        for path in group.get("roots", []):
            rows = index.get(path, [])
            fixed = owners.get(whole_ledger_export.source_key(epoch, path))
            if fixed is not None:
                rows = [row for row in rows if row["target"] == fixed]
            row = source_view.pick(rows, path, None, epoch)
            finite.require(row is not None, f"Selected root has no public owner: {path} at {epoch}")
            targets.add(row["target"])
    finite.require(targets, "Selection has no Lean roots")
    modules = sorted(targets)
    directory = release.new_output(root, output)
    env = release.build_environment()
    args = ["build", *("+" + module for module in modules)]
    build = release.run_process(["lake", *args], root, directory / "build.log", env)
    freshness = (release.run_process(["lake", "--no-build", *args], root, directory / "freshness.log", env)
                 if build["exit_code"] == 0 else None)
    stable = ((root / selection_path).read_bytes() == selection_raw
              and release.sha(export_path.read_bytes()) == export_hash)
    result = {"schema": "h0mework/paper-selected-root-build@1", "paper": paper,
              "status": "passed" if freshness and freshness["exit_code"] == 0 and stable else "failed",
              "selection_sha256": release.sha(selection_raw), "export_map_sha256": export_hash,
              "targets": modules, "build": build, "freshness": freshness, "inputs_unchanged": stable}
    (directory / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def entry(paper, map_path, selection_path):
    identity = release.verify_map(ROOT, map_path, require_ready=True)
    finite.require(identity["ok"], f"Source binding failed: {identity['errors']}")
    data, exported = release.load_maps(ROOT, map_path)
    claims = release.selected_claims(data)
    finite.require({claim["id"] for claim in claims} == PAPERS[paper], "Claim scope differs")
    scopes, entries = finite.package_scopes(data, exported, ROOT)
    complete_types = finite.recorded_acceptance(data, scopes, entries, ROOT)
    selection = release.read_json(ROOT / selection_path)
    executed_map = data["acceptance"]["claim_map_at_execution"]
    executed_scope = finite.artifact(ROOT, executed_map)
    finite.require({claim["id"] for claim in release.selected_claims(executed_scope)} == PAPERS[paper],
                   "Execution used a different claim scope")
    for kind in ("build", "trust", "declaration_types"):
        receipt = finite.artifact(ROOT, data["acceptance"][kind])
        finite.require(receipt["input_identity"]["sha256"]["claim_map"] == executed_map["payload_sha256"],
                       f"Execution used a different source map for {kind}")
    for key in ("source_public", "source_exact"):
        receipt = finite.artifact(ROOT, data["acceptance"][key])
        finite.require(receipt["status"] == "passed"
                       and receipt["selection_sha256"] == release.sha((ROOT / selection_path).read_bytes()),
                       f"Recorded source recovery differs for {key}")
    built = finite.artifact(ROOT, data["acceptance"]["standalone_build"])
    modules = {row["public"]["module"] for claim in claims for role in ("standalone_consumers", "compiled_controls")
               for row in claim.get(role, [])}
    finite.require(built["status"] == "passed" and built["inputs_unchanged"]
                   and built["build"]["exit_code"] == 0 and built["freshness"]["exit_code"] == 0
                   and modules <= set(built["targets"]), "Standalone compiler coverage differs")
    exported_modules = {row["target"]: row for row in exported["modules"]}
    built_sources = set()
    for target in built["targets"]:
        row = exported_modules[target]
        for original in (row, *row.get("source_aliases", [])):
            built_sources.update((epoch, original["source_path"])
                                 for epoch in original.get("source_revisions", [original["source_revision"]]))
    roots = {(group["source_commit"], path) for group in selection["selections"] for path in group.get("roots", [])}
    finite.require(roots <= built_sources, "A selected original source root was not built")
    finite.require(built["selection_sha256"] == release.sha((ROOT / selection_path).read_bytes()),
                   "Standalone build used a different selection")
    built_proof = finite.artifact(ROOT, data["acceptance"]["build"])
    finite.require(built["export_map_sha256"] == built_proof["input_identity"]["sha256"]["export_map"],
                   "Standalone build used a different export map")
    for claim in claims:
        for role in ("standalone_consumers", "compiled_controls"):
            for row in claim.get(role, []):
                file = release.repo_file(ROOT, row["public"]["path"])
                finite.require(release.sha(file.read_bytes()) == row["public"]["sha256"],
                               f"Standalone source changed: {file.name}")
    cache = finite.artifact(ROOT, data["acceptance"]["cache_preservation"])
    finite.require(cache["status"] == "passed", "CI cache comparison failed")
    if paper == "certified-go":
        replay = finite.artifact(ROOT, data["acceptance"]["original_source_h11"])
        row, = (row for claim in claims for row in claim.get("standalone_consumers", [])
                if row["source_path"].endswith("/ElevenAssembly.lean"))
        log = replay["log"]
        inputs = replay["input"]
        finite.require(replay["status"] == "passed" and replay["exit_code"] == 0
                       and inputs["original_source_epoch"] == row["source_commit"]
                       and inputs["original_runner_sha256"] == row["source_sha256"]
                       and inputs["public_module"] == row["public"]["module"]
                       and release.sha(release.repo_file(ROOT, log["path"]).read_bytes()) == log["sha256"],
                       "Original Go assembly replay identity differs")
        result = replay["results"]
        assembly = result["assembled_current_producers"]
        predecessor = result["actual_predecessor"]
        finite.require(assembly["original_white_ports"] == assembly["retained_children"] == 351
                       and assembly["complete_certificate"] and assembly["outstanding_source_ports"] == []
                       and predecessor["source_plies"] == 10 and predecessor["history_length"] == 11
                       and predecessor["complete_certificate"], "Go replay did not close the actual predecessor")
    return {"status": "passed", "claims": len(claims), "packages": len(scopes),
            "checked_types": complete_types, "standalone": len(modules), "mapped": identity["mapped"]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paper", choices=PAPERS)
    parser.add_argument("command", choices=("entry", "verify-map", "build", "roots", "trust", "types", "source"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--package", action="append", help="Run only the given proof package")
    parser.add_argument("--exact", action="store_true")
    parser.add_argument("--private-originals", type=Path)
    args = parser.parse_args(argv)
    if args.command in {"build", "roots", "trust", "types", "source"} and args.output is None:
        parser.error("--output is required for execution and source recovery")
    if args.command != "source" and (args.exact or args.private_originals):
        parser.error("--exact and --private-originals apply to source recovery")
    if args.package and args.command not in {"build", "trust", "types"}:
        parser.error("--package applies to proof execution")

    paper = args.paper
    map_path = f"docs/{paper}-map.json"
    selection_path = f"checks/{paper}-selection.json"
    release.SCHEMA = whole_ledger.SCHEMA = f"h0mework/{paper}-map@1"
    whole_ledger.MAP = map_path
    try:
        if args.command == "entry":
            result = entry(paper, map_path, selection_path)
        elif args.command == "roots":
            receipt = build_selected_roots(ROOT, paper, selection_path, args.output)
            result = {"status": receipt["status"], "targets": len(receipt["targets"]),
                      "receipt": str(args.output / "result.json")}
        elif args.command == "verify-map":
            identity = release.verify_map(ROOT, map_path)
            result = {"status": "passed" if identity["identity_ready"] else "failed",
                      "claims": identity["claims"], "mapped": identity["mapped"], "errors": identity["errors"]}
        elif args.command == "source":
            result = society_book.source(ROOT, args.output, exact=args.exact, selection_path=selection_path,
                                         private_originals=args.private_originals)
            result["selection_sha256"] = release.sha((ROOT / selection_path).read_bytes())
            (ROOT / args.output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
        else:
            receipt = (whole_ledger.types(args.output, args.package) if args.command == "types" else
                       release.execute(args.command, ROOT, map_path, args.output, args.package))
            result = {"status": "passed" if receipt.get("ok", receipt.get("status") == "passed") else "failed",
                      "receipt": str(args.output / "result.json")}
        print(json.dumps(result, ensure_ascii=False))
        return int(result["status"] != "passed")
    except (OSError, ValueError, KeyError, TypeError, release.ReleaseError, source_view.ViewError,
            whole_ledger_export.ExportError) as error:
        parser.exit(1, f"{paper}: {args.command} failed: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
