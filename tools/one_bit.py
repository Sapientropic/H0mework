#!/usr/bin/env python3
"""Check the One Bit selection by reusing accepted scopes and its new control.

Existing proof environments stay separate. Only the ghost control is compiled
and audited by the One Bit edition runner; this reader entry checks the exact
source scopes, original receipts and independently recoverable public bytes.
"""
from __future__ import annotations

import argparse
import gzip
import json

import first_release as release
import publication
import source_view
import whole_ledger

MAP = "docs/one-bit-map.json"
SCHEMA = "h0mework/one-bit-map@1"
CONTROL_MAP = "checks/one-bit-control-map.json"
CONTROL_SCHEMA = "h0mework/one-bit-control-map@1"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise release.ReleaseError(message)


def document(root=release.ROOT):
    data = release.read_json(root / MAP)
    require(data.get("schema") == SCHEMA, "One Bit map schema differs")
    claims = data.get("claims", [])
    require(len(claims) == 11 and {c.get("id") for c in claims} == {f"OB{i}" for i in range(1, 12)},
            "One Bit must retain OB1–OB11 exactly")
    return data


def artifact(root, reference):
    raw = release.repo_file(root, reference["path"]).read_bytes()
    require(release.sha(raw) == reference["sha256"], "Referenced bytes changed: " + reference["path"])
    if reference.get("compression") == "gzip":
        raw = gzip.decompress(raw)
    if reference.get("payload_sha256"):
        require(release.sha(raw) == reference["payload_sha256"], "Referenced payload changed")
    return json.loads(raw)


def trusted(run):
    report = run.get("audit", {})
    require(run.get("exit_code") == 0 and report.get("full_metadata") is True
            and report.get("unsafe") == 0 and report.get("partial") == 0
            and set(report.get("axioms", [])) <= ALLOWED_AXIOMS,
            "Original complete metadata trust gate did not pass")


def verify_identity(root, path, schema, *, entry_keys=None, require_ready=True):
    original = release.SCHEMA
    try:
        release.SCHEMA = schema
        result = release.verify_map(root, path, require_ready, entry_keys=entry_keys)
    finally:
        release.SCHEMA = original
    require(result["ok"] and result["identity_ready"], "Selected identity failed: " + str(result["errors"]))
    return result


def verify_types(root, control, scope):
    receipt = artifact(root, control["acceptance"]["declaration_types"])
    require(receipt.get("status") == "passed" and receipt.get("inputs_unchanged") is True,
            "Control types have no stable actual acceptance")
    expected = {(entry["public"]["module"], release.declaration_name(d))
                for _, _, _, entry in release.claim_entries(release.selected_claims(control))
                for d in entry["declarations"]}
    rows = receipt.get("declarations", [])
    require({(r["module"], r["qualified_name"]) for r in rows} == expected and len(rows) == len(expected),
            "Complete control type inventory differs")
    package = control["proof_packages"][0]["id"]
    require(receipt.get("source_scopes", {}).get(package) == {
        "source_scope_sha256": scope["digest"], "modules": scope["modules"]}, "Control type source scope changed")
    accepted = receipt["input_identity"]["sha256"]
    for key, path in (("lakefile", "Lean/lakefile.toml"), ("toolchain", "Lean/lean-toolchain"),
                      ("manifest", "Lean/lake-manifest.json")):
        require(release.sha(release.repo_file(root, path).read_bytes()) == accepted[key],
                "Control type environment changed: " + key)
    for row in rows:
        whole_ledger.validate_complete_type(row)
        require(row.get("package") == package and row.get("unsafe") is False and row.get("partial") is False
                and set(row.get("axioms", [])) <= ALLOWED_AXIOMS, "Control type trust differs")
    for _, _, _, entry in release.claim_entries(release.selected_claims(control)):
        for declaration in entry["declarations"]:
            reference = declaration.get("complete_type", {})
            index = reference.get("declaration_index")
            require(type(index) is int and 0 <= index < len(rows), "Control declaration has no complete type index")
            row = rows[index]
            require(row["module"] == entry["public"]["module"]
                    and row["qualified_name"] == release.declaration_name(declaration)
                    and reference.get("type_sha256") == release.sha(row["type"].encode()),
                    "Control declaration complete type binding changed")
    return len(rows)


def entry(output, *, require_ready=False, root=release.ROOT):
    data = document(root)
    exported = release.read_json(root / release.EXPORT_MAP)
    parse_cache, scopes, reused, declarations, resources = {}, {}, [], set(), set()
    configured = release.settings(root)
    for authority in data["authorities"]:
        source = artifact(root, authority["map"])
        claims = release.selected_claims(source)
        selected_ids = set(authority["claim_ids"])
        selected = [c for c in claims if c["id"] in selected_ids]
        require({c["id"] for c in selected} == selected_ids, "Referenced authority claim is missing")
        keys = {(c["id"], role, i) for c, role, i, _ in release.claim_entries(selected)}
        verify_identity(root, authority["map"]["path"], source["schema"], entry_keys=keys)
        receipt = artifact(root, authority["trust"])
        require(receipt.get("inputs_unchanged") is True
                and (receipt.get("status") == "passed" or receipt.get("ok") is True),
                "Original trust execution failed")
        for key in ("package_moreLeanArgs", "package_weakLeanArgs"):
            require(receipt["settings"][key] == configured[key], "Inherited proof flags changed: " + key)
        all_entries = list(release.claim_entries(selected))
        chosen = set()
        for package in release.packages(source):
            relevant = [item for item in release.package_entries(claims, package)
                        if item[0]["id"] in selected_ids]
            if not relevant:
                continue
            chosen.update((c["id"], role, i) for c, role, i, _ in relevant)
            scope = release.package_inputs(root, exported, package, release.package_entries(claims, package),
                                           parse_cache=parse_cache)
            name = package["id"]
            if authority["kind"] == "whole-ledger":
                run = next(r for r in receipt["results"] if r["package"] == name)
                accepted_scope = package["accepted_source_scope_sha256"]
            else:
                run = next(r for r in receipt["packages"] if r["package"] == name)
                accepted_scope = run["input_digest"]
            require(scope["digest"] == accepted_scope, "Inherited source/import scope changed: " + name)
            trusted(run)
            for _, _, _, e in relevant:
                for d in e["declarations"]:
                    qualified = release.declaration_name(d)
                    require(run["audit_scope"]["declarations"].get(qualified) == e["public"]["module"],
                            "Selected declaration has no same-owner original audit root: " + qualified)
                    declarations.add((name, e["public"]["module"], qualified))
            scopes[name] = scope
            reused.append({"package": name, "source_scope_sha256": scope["digest"], "modules": scope["modules"],
                           "original_trust_receipt": authority["trust"], "new_lean_execution": False})
        required = {(c["id"], role, i) for c, role, i, e in all_entries if release.entry_kind(role, e) == "lean"}
        require(chosen == required, "Inherited selected proof entries have incomplete package coverage")
        for _, role, _, e in all_entries:
            if role == "resources":
                resources.add(e["public"]["path"])
    by_path = {row["path"]: row for row in exported["modules"]}
    inverse = {row["target"]: row for row in exported["modules"]}
    recovered = []
    for binding in data["source_bindings"]:
        row = by_path.get(binding["public"]["path"])
        require(row is not None, "Selected source has no export owner")
        record = source_view.source_record(row, binding["source_path"], binding["source_commit"])
        require(record is not None and source_view.row_at(record, binding["source_commit"])
                and record["source_sha256"] == binding["source_sha256"]
                and row["target"] == binding["public"]["module"]
                and row["target_sha256"] == binding["public"]["sha256"], "Selected source epoch or byte identity changed")
        view, exact = source_view.module_views(row, inverse)
        require(release.sha(exact) == record["source_sha256"], "Selected source exact inverse changed")
        recovered.append({"source_commit": binding["source_commit"], "source_path": binding["source_path"],
                          "source_sha256": release.sha(exact), "public_sha256": release.sha(view)})
    control = release.read_json(root / CONTROL_MAP)
    verify_identity(root, CONTROL_MAP, CONTROL_SCHEMA, require_ready=require_ready)
    package = release.packages(control)[0]
    control_scope = release.package_inputs(root, exported, package,
                    release.package_entries(release.selected_claims(control), package), parse_cache=parse_cache)
    checked_types = None
    if require_ready:
        acceptance = control.get("acceptance", {})
        require(acceptance.get("status") == "passed", "Control acceptance remains pending")
        require(acceptance.get("source_scope_sha256") == control_scope["digest"], "Accepted control source scope changed")
        for kind in ("build", "trust"):
            receipt = artifact(root, acceptance[kind])
            require(receipt.get("ok") is True and receipt.get("inputs_unchanged") is True,
                    "Control execution failed: " + kind)
            require(receipt["input_identity"]["package_inputs"][package["id"]] == control_scope["digest"],
                    "Control execution source scope changed")
            if kind == "trust":
                run = receipt["results"][0]
                trusted(run)
                _, expected = release.audit_source(package, release.package_entries(release.selected_claims(control), package))
                require(run["audit_scope"]["token"] == expected["token"], "Control audit root scope changed")
        checked_types = verify_types(root, control, control_scope)
    directory = release.new_output(root, output)
    result = {"schema": "h0mework/one-bit-entry@1", "status": "passed", "claims": 11,
              "claim_map_sha256": release.sha((root / MAP).read_bytes()), "reused_packages": reused,
              "reused_explicit_audit_roots": len(declarations), "resources_verified": len(resources),
              "selected_sources_recovered": recovered, "new_control_source_scope_sha256": control_scope["digest"],
              "new_control_modules": control_scope["modules"], "recorded_control_types_verified": checked_types,
              "recorded_readiness_required": require_ready, "private_source_reads": 0,
              "scientific_recalculation": False}
    (directory / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


def types(output):
    original = whole_ledger.MAP, whole_ledger.SCHEMA
    try:
        whole_ledger.MAP, whole_ledger.SCHEMA = CONTROL_MAP, CONTROL_SCHEMA
        return whole_ledger.types(output)
    finally:
        whole_ledger.MAP, whole_ledger.SCHEMA = original


def source(output, *, root=release.ROOT):
    control = release.read_json(root / CONTROL_MAP)
    package = release.packages(control)[0]
    exported = release.read_json(root / release.EXPORT_MAP)
    scope = release.package_inputs(root, exported, package,
                                  release.package_entries(release.selected_claims(control), package))
    rows = {row["path"]: row for row in exported["modules"]}
    expected = {}
    for path in scope["files"]:
        row = rows[path]
        record = source_view.source_record(row, row["source_path"], package["source_commit"])
        require(record is not None and source_view.row_at(record, package["source_commit"]),
                "Control dependency has no original epoch binding: " + path)
        expected[record["source_path"]] = record["source_sha256"]
    outputs, skipped = source_view.reconstruct(list(expected), [], [], package["source_commit"], [], True, None)
    require(not skipped and set(outputs) == set(expected), "Original control source closure differs")
    require(all(release.sha(outputs[path]) == digest for path, digest in expected.items()),
            "Original control dependency bytes differ")
    directory = release.new_output(root, output)
    for path, raw in outputs.items():
        target = directory / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
    result = {"schema": "h0mework/one-bit-source-view@1", "status": "passed",
              "source_commit": package["source_commit"], "source_files": len(outputs),
              "source_scope_sha256": scope["digest"], "view": "exact", "private_source_reads": 0}
    (directory / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("entry", "types", "source"))
    parser.add_argument("--output", required=True)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.command == "entry":
            result = entry(args.output, require_ready=args.require_ready)
        elif args.command == "types":
            result = types(args.output)
        else:
            result = source(args.output)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0 if result["status"] == "passed" else 1
    except (release.ReleaseError, source_view.ViewError, publication.PublicationError,
            OSError, ValueError, KeyError, TypeError, StopIteration) as error:
        print(json.dumps({"schema": "h0mework/one-bit-check@1", "status": "failed", "error": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
