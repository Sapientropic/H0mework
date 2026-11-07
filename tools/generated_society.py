#!/usr/bin/env python3
"""Recover the society selection and verify its separate H0 acceptance.

Historical strict receipts remain resources at their actual epochs. New proof
builds and metadata audits use the existing edition runner and type codec.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import gzip
import json
import posixpath

import first_release as release
import source_view
import whole_ledger
import whole_ledger_export

MAP = "docs/generated-society-map.json"
SCHEMA = "h0mework/generated-society-map@1"
SELECTION = "checks/generated-society-selection.json"
CORE_CLAIMS = {"G2a", *(f"G{i}" for i in range(10)), *(f"G{i}" for i in range(13, 28))}
INTERFACES = {"G10", "G11", "G12"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise release.ReleaseError(message)


def document(root=release.ROOT):
    data = release.read_json(root / MAP)
    require(data.get("schema") == SCHEMA, "Society map schema differs")
    claims = release.selected_claims(data)
    ids = {claim["id"] for claim in claims}
    require(CORE_CLAIMS <= ids <= CORE_CLAIMS | INTERFACES,
            "Society must retain G0–G9, G2a and G13–G27; G10–G12 are explicit interfaces")
    for claim in claims:
        if claim["id"] in INTERFACES:
            require(claim.get("interface_only") is True,
                    "Society interface must be explicitly interface_only: " + claim["id"])
        require(bool(claim.get("direct_consumers")), "Society claim has no direct consumer: " + claim["id"])
    return data


def artifact(root, reference):
    raw = release.repo_file(root, reference["path"]).read_bytes()
    require(release.sha(raw) == reference.get("sha256"), "Acceptance artifact changed: " + reference["path"])
    if reference.get("compression") == "gzip":
        raw = gzip.decompress(raw)
    if reference.get("payload_sha256"):
        require(release.sha(raw) == reference["payload_sha256"], "Acceptance payload changed")
    return json.loads(raw)


@contextmanager
def source_root(root):
    previous = source_view.ROOT, source_view.EXPORT_MAP
    try:
        source_view.ROOT, source_view.EXPORT_MAP = root, root / release.EXPORT_MAP
        yield
    finally:
        source_view.ROOT, source_view.EXPORT_MAP = previous


def selected_views(root, *, exact=False, private_originals=None, selection_path=None):
    """Traverse original imports at each epoch, then recover public/exact bytes."""
    selection = whole_ledger_export.load_selection(root / (selection_path or SELECTION))
    with source_root(root):
        exported, modules, artifacts, inverse = source_view.load_map()
        epochs = {}
        for selected in selection["selections"]:
            epoch = selected["source_commit"]
            state = epochs.setdefault(epoch, {"outputs": {}, "modules": {}, "artifacts": {}})
            todo = list(selected.get("roots", []))
            resource_paths = set(selected.get("artifacts", []))
            while todo:
                path = todo.pop()
                if path in state["modules"]:
                    continue
                row = source_view.pick(modules.get(path, []), path, None, epoch)
                require(row is not None, "Selected original module is not exported at its epoch: " + path)
                public, original = source_view.module_views(row, inverse)
                state["modules"][path] = row
                state["outputs"][path] = original if exact else public
                for _, _, name in source_view.import_tokens(original.decode()):
                    if name.split(".")[0] in source_view.EXTERNAL:
                        continue
                    suffix = name.replace(".", "/") + ".lean"
                    choices = ["Lean/" + suffix, posixpath.join(posixpath.dirname(path), suffix)]
                    dependency = next((p for p in choices if source_view.pick(modules.get(p, []), p, None, epoch)), None)
                    require(dependency is not None, "Original import closure is incomplete: " + path + " -> " + name)
                    todo.append(dependency)
                resource_paths.update(rule["source_artifact"] for rule in row.get("resource_rewrites", []))
            for path in sorted(resource_paths):
                row = source_view.pick(artifacts.get(path, []), path, None, epoch)
                require(row is not None, "Selected original resource is not exported at its epoch: " + path)
                public, original = source_view.artifact_views(row, private_originals)
                require(not exact or original is not None,
                        "Exact resource reconstruction requires --private-originals: " + path)
                state["artifacts"][path] = row
                state["outputs"][path] = original if exact else public
    return selection, exported, epochs


def package_scopes(data, exported, root):
    claims, cache, scopes, assigned = release.selected_claims(data), {}, {}, {}
    expected = {(c["id"], role, i) for c, role, i, e in release.claim_entries(claims)
                if release.entry_kind(role, e) == "lean"}
    entries_by_package = {}
    for package in release.packages(data):
        name = package["id"]
        entries = release.package_entries(claims, package)
        entries_by_package[name] = entries
        scopes[name] = release.package_inputs(root, exported, package, entries, parse_cache=cache)
        for claim, role, index, entry in entries:
            key = claim["id"], role, index
            require(key not in assigned, "Selected proof entry belongs to multiple packages: " + str(key))
            require(entry.get("verification", {}).get("proof_package") == name,
                    "Selected proof entry names a different acceptance package: " + str(key))
            assigned[key] = name
    require(set(assigned) == expected, "Society proof packages do not cover all selected producers and consumers")
    return scopes, entries_by_package


def recorded_acceptance(data, scopes, entries, root):
    acceptance = data.get("acceptance", {})
    require(acceptance.get("status") == "passed", "Society H0 acceptance remains pending")
    summaries = {name: {"source_scope_sha256": scope["digest"], "modules": scope["modules"]}
                 for name, scope in scopes.items()}
    packages = release.packages(data)
    for package in packages:
        require(package.get("accepted_source_scope_sha256") == scopes[package["id"]]["digest"],
                "Accepted society package source scope changed: " + package["id"])
    configured = release.settings(root)
    accepted_lakefiles = set()
    for kind in ("build", "trust"):
        receipt = artifact(root, acceptance[kind])
        require(receipt.get("ok") is True and receipt.get("inputs_unchanged") is True
                and receipt.get("input_identity") == receipt.get("input_identity_after"),
                "Society H0 execution did not pass with stable inputs: " + kind)
        require(receipt["input_identity"]["package_inputs"] == {name: scope["digest"] for name, scope in scopes.items()},
                "Society H0 execution package scope changed: " + kind)
        input_hashes = receipt["input_identity"]["sha256"]
        lakefile_digest = input_hashes.get("lakefile")
        if lakefile_digest not in accepted_lakefiles:
            release.verify_build_configuration(root, lakefile_digest, data=data, scopes=scopes)
            accepted_lakefiles.add(lakefile_digest)
        for key, path in (("toolchain", "Lean/lean-toolchain"), ("manifest", "Lean/lake-manifest.json")):
            require(receipt["input_identity"]["sha256"].get(key) == release.sha(release.repo_file(root, path).read_bytes()),
                    "Society H0 execution build input changed: " + key)
        for key in ("package_moreLeanArgs", "package_weakLeanArgs"):
            require(receipt.get("settings", {}).get(key) == configured[key], "Society proof flags changed: " + key)
        if kind == "build":
            require(bool(receipt.get("results")) and all(r.get("exit_code") == 0 for r in receipt["results"]),
                    "Society build has no complete successful execution")
        else:
            runs = receipt.get("results", [])
            require(len(runs) == len(packages) and {r.get("package") for r in runs} == set(scopes),
                    "Society trust does not cover all proof packages")
            require(receipt.get("preflight", {}).get("exit_code") == 0, "Society trust freshness preflight failed")
            for package in packages:
                run = next(r for r in runs if r["package"] == package["id"])
                _, expected = release.audit_source(package, entries[package["id"]])
                require(run.get("exit_code") == 0 and run.get("status") == "passed"
                        and run.get("audit_scope", {}).get("token") == expected["token"],
                        "Society trust roots differ from the actual selected declarations")
                release.trust_report("FIRST_RELEASE_TRUST " + json.dumps(run.get("audit", {})), expected)
    count = whole_ledger.verify_recorded_types(data, summaries, root=root)
    types_receipt = artifact(root, acceptance["declaration_types"])
    for row in types_receipt["declarations"]:
        require(row.get("unsafe") is False and row.get("partial") is False
                and set(row.get("axioms", [])) <= ALLOWED_AXIOMS,
                "Society declaration type has a nonstandard trust dependency")
    return count


def entry(output, *, require_ready=False, root=release.ROOT):
    data = document(root)
    original_schema = release.SCHEMA
    try:
        release.SCHEMA = SCHEMA
        identity = release.verify_map(root, MAP, require_ready)
    finally:
        release.SCHEMA = original_schema
    require(identity["ok"] and identity["identity_ready"], "Society selected identity failed: " + str(identity["errors"]))
    selection, exported, epochs = selected_views(root)
    scopes, entries = package_scopes(data, exported, root)
    proof_paths = {path for scope in scopes.values() for path in scope["files"]}
    for state in epochs.values():
        require({row["path"] for row in state["modules"].values()} <= proof_paths,
                "Society selection contains modules outside its actual built package closures")
    for _, role, _, entry_row in release.claim_entries(release.selected_claims(data)):
        epoch, path = entry_row["source_commit"], entry_row["source_path"]
        state = epochs.get(epoch, {})
        kind = "artifacts" if release.entry_kind(role, entry_row) == "artifact" else "modules"
        require(path in state.get(kind, {}), "Mapped society entry is outside the finite selection: " + path)
    count = recorded_acceptance(data, scopes, entries, root) if require_ready else None
    directory = release.new_output(root, output)
    result = {"schema": "h0mework/generated-society-entry@1", "status": "passed",
              "claim_map_sha256": release.sha((root / MAP).read_bytes()),
              "selection_sha256": release.sha((root / SELECTION).read_bytes()),
              "claims": len(release.selected_claims(data)), "mapped_entries": identity["mapped"],
              "epochs": len(epochs), "complete_proof_owners_recovered": len({row["target"] for state in epochs.values() for row in state["modules"].values()}),
              "resources_verified": len({row["path"] for state in epochs.values() for row in state["artifacts"].values()}),
              "packages": {name: {"source_scope_sha256": scope["digest"], "modules": scope["modules"]} for name, scope in scopes.items()},
              "recorded_readiness_required": require_ready, "recorded_complete_types_verified": count,
              "historical_certifications": "retained original resources; separate from this H0 acceptance",
              "private_source_reads": 0, "scientific_recalculation": False}
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
    result = {"schema": "h0mework/generated-society-source-view@1", "status": "passed",
              "selection_sha256": release.sha((root / SELECTION).read_bytes()), "view": "exact" if exact else "public",
              "epochs": {epoch: {"modules": len(state["modules"]), "resources": len(state["artifacts"]),
                                  "source_scope_sha256": release.sha(json.dumps({p: release.sha(raw) for p, raw in state["outputs"].items()}, sort_keys=True).encode())}
                         for epoch, state in epochs.items()},
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
    parser.add_argument("command", choices=("entry", "source", "types"))
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
        else:
            result = types(args.output, args.package)
        print(json.dumps({key: value for key, value in result.items() if key not in {"declarations", "runs"}},
                         ensure_ascii=False, indent=2))
        return 0 if result["status"] == "passed" else 1
    except (release.ReleaseError, source_view.ViewError, whole_ledger_export.ExportError,
            OSError, ValueError, TypeError, KeyError, StopIteration) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, ensure_ascii=False))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
