#!/usr/bin/env python3
"""Check the two second-edition low-energy papers in their separate Lean environments."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import json
from pathlib import Path

import edition_release
import first_release as release
import generated_society as finite
import society_book
import source_view
import whole_ledger

ROOT = release.ROOT
MAP = "docs/low-energy-v2-map.json"
SCHEMA = "h0mework/low-energy-v2-map@1"
SELECTION = "checks/low-energy-v2-selection.json"
BASE_MAP, BASE_SCHEMA = edition_release.EDITIONS["low-energy"]
PAPERS = ("low-energy-phenomenology", "low-energy-loop-response")
CLAIMS = {"low1.L26", "low1.L27", "low1.L28", "low1.L29", "low2.Q7"}
require = finite.require


@contextmanager
def using_map(path, schema):
    previous = release.SCHEMA, whole_ledger.MAP, whole_ledger.SCHEMA
    release.SCHEMA = whole_ledger.SCHEMA = schema
    whole_ledger.MAP = path
    try:
        yield
    finally:
        release.SCHEMA, whole_ledger.MAP, whole_ledger.SCHEMA = previous


def inherited_acceptance(reference):
    """Verify the fresh execution against the frozen first-edition map."""
    with using_map(BASE_MAP, BASE_SCHEMA):
        identity = release.verify_map(ROOT, BASE_MAP)
        require(identity["identity_ready"], "First-edition public identity failed")
        data, exported = release.load_maps(ROOT, BASE_MAP)
        require(release.sha((ROOT / BASE_MAP).read_bytes()) == reference["map_sha256"],
                "Frozen first-edition claim map differs")
        packages = release.packages(data)
        claims = release.selected_claims(data)
        scope, roots, cache = {}, {}, {}
        covered = set()
        for package in packages:
            name = package["id"]
            entries = release.package_entries(claims, package)
            scope[name] = release.package_inputs(ROOT, exported, package, entries, parse_cache=cache)
            _, roots[name] = release.audit_source(package, entries)
            covered.update((claim["id"], role, index) for claim, role, index, _ in entries)
        require(covered == {(claim["id"], role, index)
                            for claim, role, index, entry in release.claim_entries(claims)
                            if release.entry_kind(role, entry) == "lean"}, "First-edition proof coverage differs")
        digests = {name: row["digest"] for name, row in scope.items()}
        for kind in ("build", "trust", "declaration_types"):
            receipt = finite.artifact(ROOT, reference[kind])
            passed = receipt.get("ok") is True if kind != "declaration_types" else receipt.get("status") == "passed"
            require(passed and receipt["inputs_unchanged"]
                    and receipt["input_identity"] == receipt["input_identity_after"]
                    and receipt["input_identity"]["package_inputs"] == digests,
                    "First-edition execution differs: " + kind)
            fixed = receipt["input_identity"]["sha256"]
            require(fixed["claim_map"] == reference["map_sha256"], "First-edition execution map differs")
            for name, path in (("toolchain", "Lean/lean-toolchain"), ("manifest", "Lean/lake-manifest.json")):
                require(fixed[name] == release.sha((ROOT / path).read_bytes()),
                        "First-edition build input differs: " + path)
            release.verify_build_configuration(ROOT, fixed["lakefile"], data=data, scopes=scope)
            if kind == "trust":
                require({run["package"] for run in receipt["results"]} == set(scope),
                        "First-edition trust coverage differs")
                for run in receipt["results"]:
                    expected = roots[run["package"]]
                    require(run["audit_scope"]["token"] == expected["token"], "First-edition trust roots differ")
                    release.trust_report("FIRST_RELEASE_TRUST " + json.dumps(run["audit"]), expected)
            if kind == "declaration_types":
                seen = set()
                for row in receipt["declarations"]:
                    whole_ledger.validate_complete_type(row)
                    seen.add((row["package"], row["qualified_name"]))
                    require(not row["unsafe"] and not row["partial"]
                            and set(row["axioms"]) <= finite.ALLOWED_AXIOMS, "First-edition type trust differs")
                for package in packages:
                    name = package["id"]
                    require(all((name, release.declaration_name(declaration)) in seen
                                for _, _, _, entry in release.package_entries(claims, package)
                                for declaration in entry["declarations"]), "First-edition type coverage differs: " + name)
        return {"claims": len(claims), "packages": len(scope), "complete_types": len(receipt["declarations"])}


def entry():
    identity = release.verify_map(ROOT, MAP, require_ready=True)
    require(identity["ok"], "Second-edition proof map failed: " + str(identity["errors"]))
    data, exported = release.load_maps(ROOT, MAP)
    claims = release.selected_claims(data)
    require({row["id"] for row in claims} == CLAIMS, "Second-edition claim inventory differs")
    scopes, entries = finite.package_scopes(data, exported, ROOT)
    types = finite.recorded_acceptance(data, scopes, entries, ROOT)
    selection, _, epochs = finite.selected_views(ROOT, selection_path=SELECTION)
    covered = {path for scope in scopes.values() for path in scope["files"]}
    selected_owners = {row["path"] for epoch in epochs.values() for row in epoch["modules"].values()}
    # A shared source epoch can select a different already-installed owner
    # with the same actual compile layout. The delta owners themselves are exact.
    require(set(data["new_owner_paths"]) <= selected_owners & covered, "Second-edition build misses a new owner")
    for kind in ("source_public", "source_exact"):
        receipt = finite.artifact(ROOT, data["acceptance"][kind])
        require(receipt.get("status") == "passed"
                and receipt.get("selection_sha256") == release.sha((ROOT / SELECTION).read_bytes()),
                "Second-edition source recovery differs: " + kind)
    cache = finite.artifact(ROOT, data["acceptance"]["cache_preservation"])
    require(cache["status"] == "passed" and not cache["invalidated"]
            and sum(row["expected_compiled_modules"] for row in cache["added"].values()) == len(data["new_owner_paths"]),
            "Second-edition cache preservation differs")
    return {"status": "passed", "expanded_claims": len(claims), "new_owners": len(data["new_owner_paths"]),
            "reusable_linux_shards": len(cache["reused"]), "selected_roots": sum(len(group.get("roots", [])) for group in selection["selections"]),
            "delta_complete_types": types, "inherited": inherited_acceptance(data["inherited"])}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("entry", "build", "trust", "types", "source"))
    parser.add_argument("--paper", choices=PAPERS)
    parser.add_argument("--inherited", action="store_true", help="execute the frozen first-edition proof packages")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--exact", action="store_true")
    parser.add_argument("--private-originals", type=Path)
    args = parser.parse_args(argv)
    if args.command != "entry" and args.output is None:
        parser.error("--output is required for execution and recovery")
    if args.inherited and args.command not in {"build", "trust", "types"}:
        parser.error("--inherited applies to proof execution")
    if args.command != "source" and (args.exact or args.private_originals):
        parser.error("--exact and --private-originals apply to source recovery")
    path, schema = (BASE_MAP, BASE_SCHEMA) if args.inherited else (MAP, SCHEMA)
    try:
        with using_map(path, schema):
            if args.command == "entry":
                result = entry()
            elif args.command == "source":
                result = society_book.source(ROOT, args.output, exact=args.exact, selection_path=SELECTION,
                                             private_originals=args.private_originals)
                result["selection_sha256"] = release.sha((ROOT / SELECTION).read_bytes())
                (ROOT / args.output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
            else:
                data = release.read_json(ROOT / path)
                packages = [p["id"] for p in release.packages(data)
                            if args.paper is None or p["paper"] == args.paper]
                if args.command == "types":
                    receipt = whole_ledger.types(args.output, packages)
                else:
                    receipt = release.execute(args.command, ROOT, path, args.output, packages)
                passed = receipt.get("ok", receipt.get("status") == "passed")
                result = {"status": "passed" if passed else "failed",
                          "packages": len(packages), "receipt": str(args.output / "result.json")}
        print(json.dumps(result, ensure_ascii=False))
        return int(result["status"] != "passed")
    except (OSError, ValueError, TypeError, KeyError, release.ReleaseError, source_view.ViewError) as error:
        parser.exit(1, f"Low-energy second-edition check failed: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
