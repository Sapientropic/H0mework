#!/usr/bin/env python3
"""Build, audit and restore the pinned Exact Realization proof selection."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import first_release as release
import generated_society as finite
import society_book
import source_view
import whole_ledger

ROOT = release.ROOT
MAP = "docs/exact-realization-map.json"
SCHEMA = "h0mework/exact-realization-map@1"
SELECTION = "checks/exact-realization-selection.json"


def entry():
    identity = release.verify_map(ROOT, MAP, require_ready=True)
    finite.require(identity["ok"], f"Exact Realization source binding failed: {identity['errors']}")
    data, exported = release.load_maps(ROOT, MAP)
    claims = {claim["id"] for claim in release.selected_claims(data)}
    expected = {f"R{index}" for index in range(1, 63)} | {"I", "II", "III", "IV", "V"}
    finite.require(claims == expected, "Exact Realization claim scope differs")
    for receipt in data.get("historical_public_artifacts", {}).values():
        raw = release.repo_file(ROOT, receipt["public_path"]).read_bytes()
        provenance = release.read_json(release.repo_file(ROOT, receipt["provenance"]))
        finite.require(release.sha(raw) == receipt["source_sha256"] == provenance["source_sha256"]
                       and len(raw) == provenance["source_bytes"]
                       and receipt["source_commit"] == provenance["source_commit"]
                       and receipt["source_path"] == provenance["source_path"],
                       "Historical archive receipt has changed")
    scopes, entries = finite.package_scopes(data, exported, ROOT)
    types = finite.recorded_acceptance(data, scopes, entries, ROOT)
    executed_map = data["acceptance"]["claim_map_at_execution"]
    accepted_claims = finite.artifact(ROOT, executed_map)
    finite.require({claim["id"] for claim in release.selected_claims(accepted_claims)} == claims,
                   "Recorded execution used a different claim scope")
    for kind in ("build", "trust", "declaration_types"):
        receipt = finite.artifact(ROOT, data["acceptance"][kind])
        finite.require(receipt["input_identity"]["sha256"]["claim_map"] == executed_map["payload_sha256"],
                       "Recorded execution used a different claim map: " + kind)
    for kind in ("source_public", "source_exact"):
        receipt = finite.artifact(ROOT, data["acceptance"][kind])
        finite.require(receipt["status"] == "passed"
                       and receipt["selection_sha256"] == release.sha((ROOT / SELECTION).read_bytes()),
                       "Recorded source recovery differs: " + kind)
    cache = finite.artifact(ROOT, data["acceptance"]["cache_preservation"])
    finite.require(cache["status"] == "passed", "The CI cache comparison did not pass")
    return {"status": "passed", "claims": len(claims), "packages": len(scopes),
            "complete_types": types, "selected_entries": identity["mapped"]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("entry", "verify-map", "build", "trust", "types", "source"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--package", action="append", help="restrict a proof execution to a registered epoch")
    parser.add_argument("--exact", action="store_true")
    parser.add_argument("--private-originals", type=Path)
    args = parser.parse_args(argv)
    if args.command in {"build", "trust", "types", "source"} and args.output is None:
        parser.error("--output is required for execution and recovery")
    if args.command != "source" and (args.exact or args.private_originals):
        parser.error("--exact and --private-originals apply to source recovery")
    if args.package and args.command not in {"build", "trust", "types"}:
        parser.error("--package applies to proof execution")
    release.SCHEMA = whole_ledger.SCHEMA = SCHEMA
    whole_ledger.MAP = MAP
    try:
        if args.command == "entry":
            result = entry()
        elif args.command == "verify-map":
            report = release.verify_map(ROOT, MAP)
            result = {"status": "passed" if report["identity_ready"] else "failed",
                      "claims": report["claims"], "mapped": report["mapped"], "errors": report["errors"]}
        elif args.command == "source":
            result = society_book.source(ROOT, args.output, exact=args.exact, selection_path=SELECTION,
                                         private_originals=args.private_originals)
            result["selection_sha256"] = release.sha((ROOT / SELECTION).read_bytes())
            (ROOT / args.output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
        else:
            receipt = (whole_ledger.types(args.output, args.package) if args.command == "types" else
                       release.execute(args.command, ROOT, MAP, args.output, args.package))
            passed = receipt.get("ok", receipt.get("status") == "passed")
            result = {"status": "passed" if passed else "failed",
                      "receipt": str(args.output / "result.json")}
        print(json.dumps(result, ensure_ascii=False))
        return int(result["status"] != "passed")
    except (OSError, ValueError, TypeError, KeyError, release.ReleaseError, source_view.ViewError) as error:
        parser.exit(1, f"Exact Realization check failed: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
