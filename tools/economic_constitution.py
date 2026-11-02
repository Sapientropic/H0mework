#!/usr/bin/env python3
"""Recover the economic constitution's finite sources and verify its own acceptance.

ECN arguments cite precise formal interfaces at their actual epochs. Historical
executions stay separate from the public port's build, trust and complete types.
"""
from __future__ import annotations

import argparse
import json

import first_release as release
import generated_society as finite
import source_view
import whole_ledger
import whole_ledger_export

MAP = "docs/economic-constitution-map.json"
SCHEMA = "h0mework/economic-constitution-map@1"
SELECTION = "checks/economic-constitution-selection.json"
CLAIMS = {f"ECN{i}" for i in range(1, 9)}
PUBLIC_FUNCTION_EPOCH = "6c24593364cd7763e3cdccf8f3654996a6dc8b5f"
ORIGINAL_LEDGER = "Lean/docs/audits/public-source-final-acceptance.json"
ORIGINAL_LEDGER_SHA = "e78e39e5c01671fca2dde2acf2f2910b9db9ee411c3d832859a544c4f567d10f"
ORIGINAL_EVIDENCE = "Verification/economic-constitution/public-function/original/"


def document(root=release.ROOT):
    data = release.read_json(root / MAP)
    finite.require(data.get("schema") == SCHEMA, "Economic constitution map schema differs")
    claims = release.selected_claims(data)
    finite.require(len(claims) == len(CLAIMS) and {c["id"] for c in claims} == CLAIMS,
                   "Economic constitution must retain ECN1–ECN8")
    for claim in claims:
        finite.require(bool(claim.get("producers")) and bool(claim.get("direct_consumers")),
                       "Economic interface needs its actual producer and direct consumer: " + claim["id"])
    return data


def selected_views(root, *, exact=False, private_originals=None):
    previous = finite.SELECTION
    try:
        finite.SELECTION = SELECTION
        return finite.selected_views(root, exact=exact, private_originals=private_originals)
    finally:
        finite.SELECTION = previous


def original_bindings(ledger, state):
    """Bind the historical ledger to recovered bytes without executing its programs."""
    for path, digest in ledger["sources"].items():
        source = state["modules"].get(path) or state["artifacts"].get(path)
        finite.require(source is not None and source.get("source_sha256") == digest,
                       "Original public-function source binding differs: " + path)
    for path, digest in ledger["evidence"].items():
        source = state["artifacts"].get(ORIGINAL_EVIDENCE + path)
        finite.require(source is not None and source.get("source_sha256") == digest,
                       "Original public-function receipt binding differs: " + path)
    return {"original_sources": len(ledger["sources"]), "original_receipts": len(ledger["evidence"])}


def evidence(output, *, root=release.ROOT):
    _, _, epochs = selected_views(root)
    state = epochs.get(PUBLIC_FUNCTION_EPOCH, {})
    original = state.get("artifacts", {}).get(ORIGINAL_LEDGER)
    finite.require(original is not None and original.get("source_sha256") == ORIGINAL_LEDGER_SHA,
                   "Public-function original final ledger identity differs")
    ledger = json.loads(state["outputs"][ORIGINAL_LEDGER])
    counts = original_bindings(ledger, state)
    finite.require(counts == {"original_sources": 1200, "original_receipts": 58},
                   "Original public-function finite evidence selection is incomplete")
    finite.require(ledger.get("adopted_route") == "current-frame"
                   and ledger.get("unadopted_candidate", {}).get("route") == "execution-frame",
                   "Original adopted and unadopted routes differ")
    result = {"schema": "h0mework/economic-constitution-original-evidence@1", "status": "passed",
              "selection_sha256": release.sha((root / SELECTION).read_bytes()),
              "original_ledger_source_commit": PUBLIC_FUNCTION_EPOCH,
              "original_ledger_source_sha256": ORIGINAL_LEDGER_SHA, **counts,
              "adopted_route": ledger["adopted_route"], "historical_actual": ledger["actual"],
              "historical_continuation": ledger["future"],
              "unadopted_candidate": ledger["unadopted_candidate"],
              "verification_scope": "public source and original receipt identities; original verdicts retained",
              "scientific_recalculation": False, "actual_programs_executed": False,
              "private_source_reads": 0}
    directory = release.new_output(root, output)
    (directory / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


def entry(output, *, require_ready=False, root=release.ROOT):
    data = document(root)
    previous = release.SCHEMA
    try:
        release.SCHEMA = SCHEMA
        identity = release.verify_map(root, MAP, require_ready)
    finally:
        release.SCHEMA = previous
    finite.require(identity["ok"] and identity["identity_ready"],
                   "Economic selected identity failed: " + str(identity["errors"]))
    _, exported, epochs = selected_views(root)
    scopes, entries = finite.package_scopes(data, exported, root)
    proof_paths = {path for scope in scopes.values() for path in scope["files"]}
    for state in epochs.values():
        finite.require({row["path"] for row in state["modules"].values()} <= proof_paths,
                       "Economic selection contains modules outside the actual built package closures")
    for _, role, _, row in release.claim_entries(release.selected_claims(data)):
        state = epochs.get(row["source_commit"], {})
        kind = "artifacts" if release.entry_kind(role, row) == "artifact" else "modules"
        finite.require(row["source_path"] in state.get(kind, {}),
                       "Mapped economic interface is outside the finite selection: " + row["source_path"])
    count = finite.recorded_acceptance(data, scopes, entries, root) if require_ready else None
    result = {"schema": "h0mework/economic-constitution-entry@1", "status": "passed",
              "claim_map_sha256": release.sha((root / MAP).read_bytes()),
              "selection_sha256": release.sha((root / SELECTION).read_bytes()),
              "claims": len(release.selected_claims(data)), "mapped_entries": identity["mapped"],
              "epochs": len(epochs),
              "complete_proof_owners_recovered": len({r["target"] for s in epochs.values() for r in s["modules"].values()}),
              "resources_verified": len({r["path"] for s in epochs.values() for r in s["artifacts"].values()}),
              "packages": {name: {"source_scope_sha256": scope["digest"], "modules": scope["modules"]}
                           for name, scope in scopes.items()},
              "recorded_readiness_required": require_ready, "recorded_complete_types_verified": count,
              "historical_certifications": "retained original records; independent of this H0 acceptance",
              "formal_scope": "exact selected technical support; ECN normative conclusions keep their own arguments",
              "private_source_reads": 0, "scientific_recalculation": False}
    directory = release.new_output(root, output)
    (directory / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


def source(output, *, exact=False, private_originals=None, root=release.ROOT):
    _, _, epochs = selected_views(root, exact=exact, private_originals=private_originals)
    directory = release.new_output(root, output)
    for epoch, state in epochs.items():
        for path, raw in state["outputs"].items():
            target = directory / epoch / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
    result = {"schema": "h0mework/economic-constitution-source-view@1", "status": "passed",
              "selection_sha256": release.sha((root / SELECTION).read_bytes()),
              "view": "exact" if exact else "public",
              "epochs": {epoch: {"modules": len(s["modules"]), "resources": len(s["artifacts"]),
                                  "source_scope_sha256": release.sha(json.dumps(
                                      {p: release.sha(raw) for p, raw in s["outputs"].items()}, sort_keys=True).encode())}
                         for epoch, s in epochs.items()},
              "private_originals_supplied": private_originals is not None}
    (directory / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def types(output, ids=None):
    previous = whole_ledger.MAP, whole_ledger.SCHEMA
    try:
        whole_ledger.MAP, whole_ledger.SCHEMA = MAP, SCHEMA
        return whole_ledger.types(output, ids)
    finally:
        whole_ledger.MAP, whole_ledger.SCHEMA = previous


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("entry", "source", "types", "evidence"))
    parser.add_argument("--output", required=True)
    parser.add_argument("--require-ready", action="store_true")
    parser.add_argument("--exact", action="store_true")
    parser.add_argument("--private-originals")
    parser.add_argument("--package", action="append")
    args = parser.parse_args(argv)
    try:
        if args.command == "entry":
            result = entry(args.output, require_ready=args.require_ready)
        elif args.command == "source":
            result = source(args.output, exact=args.exact, private_originals=args.private_originals)
        elif args.command == "evidence":
            result = evidence(args.output)
        else:
            result = types(args.output, args.package)
        print(json.dumps({k: v for k, v in result.items() if k not in {"declarations", "runs"}},
                         ensure_ascii=False, indent=2))
        return 0 if result["status"] == "passed" else 1
    except (release.ReleaseError, source_view.ViewError, whole_ledger_export.ExportError,
            OSError, ValueError, TypeError, KeyError, StopIteration) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, ensure_ascii=False))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
