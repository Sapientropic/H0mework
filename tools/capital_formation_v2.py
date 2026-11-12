#!/usr/bin/env python3
"""Verify the second-edition publication and both fixed proof scopes."""

from __future__ import annotations

import argparse
from copy import deepcopy
import json
from pathlib import Path
import zipfile

import capital_formation as first
import first_release as release
import generated_society as finite
import society_book
import source_view
from whole_ledger_export import ExportError, FixedGit

ROOT = first.ROOT
MAP = "docs/capital-formation-v2-map.json"
RELEASE = "papers/capital-formation/2026-11-12-v2"
ARCHIVE = RELEASE + "/editable/capital-formation-v2-editable.zip"
RISK_MEMBER = first.MEMBER + "records/cf17-source-binding.json"
RISK_SOURCE = "7c228ac7fd77350d3fe761c24b887cbf2f6e5afc"
RISK_PROOF = "fd6147f8c337d88ebf72d91ddadef0aa601e6c2e"
RISK_PACKAGE = "risk-compensation"
RISK_CLAIM = "capital-risk-compensation"
RISK_ROOT = "H0mework.Papers.SocietyBookRiskCompensation"
ACCEPTANCE = "evidence/capital-formation-v2/acceptance/index.json"
SOURCE_PREFIX = "Lean/SaturationMonoid/ProcessGame/Society/Institutions/Capitalism/"
sha, require = first.sha, first.require


def risk_sources(binding, claim, scope, inverse, public_git, private_git):
    rows = {}
    for selected in claim["selection_roots"]:
        path, module = selected["source_path"], selected["public_module"]
        owner = source_view.source_record(inverse[module], path, RISK_SOURCE)
        require(selected["source_commit"] == RISK_SOURCE and owner is not None
                and source_view.row_at(owner, RISK_SOURCE), "Missing CF17 owner at the declared epoch")
        require(path not in rows and owner["path"] in scope["files"], "CF17 selection is outside the built closure")
        require(sha(public_git.read(RISK_PROOF, owner["path"])) == scope["files"][owner["path"]],
                "CF17 public owner changed since its proof snapshot")
        view, original = source_view.module_views(owner, inverse)
        if private_git is not None:
            require(original == private_git.read(RISK_SOURCE, path), "Exact CF17 source differs from Homework: " + path)
        rows[path] = (owner, view, original)

    selected_pricing = {path for path in rows if path.startswith(SOURCE_PREFIX + "Universal/Abolition/Innovation/Contribution/Pricing/")}
    indexed = {SOURCE_PREFIX + entry["relative_path"]: entry for entry in binding["entries"]}
    require(len(indexed) == len(binding["entries"]) == binding["module_count"] == 55
            and set(indexed) == selected_pricing, "CF17 pricing inventory differs from the compiled selection")
    by_module = {path[5:-5].replace("/", "."): path for path in indexed}
    consumers = {path: [] for path in indexed}
    for path, entry in indexed.items():
        owner, _, original = rows[path]
        require(entry["homework_commit"] == RISK_SOURCE and entry["h0_commit"] == RISK_PROOF
                and entry["source_sha256"] == sha(original) and entry["public_module"] == owner["target"]
                and entry["public_path"] == owner["path"] and entry["public_sha256"] == owner["target_sha256"],
                "CF17 archive and reversible owner disagree: " + path)
        imports = [by_module[name] for _, _, name in source_view.import_tokens(original.decode()) if name in by_module]
        require([name.removeprefix(SOURCE_PREFIX) for name in imports] == entry["direct_pricing_imports"],
                "CF17 direct imports differ: " + path)
        for dependency in imports:
            consumers[dependency].append(entry["relative_path"])
    for path, entry in indexed.items():
        require(sorted(consumers[path]) == entry["direct_pricing_consumers"], "CF17 consumers differ: " + path)

    return {
        "selected_roots": len(rows), "pricing_modules": len(indexed),
        "source_declaration_locations": sum(len(entry["declarations"]) for entry in indexed.values()),
        "public_views_sha256": sha(first.encode({path: sha(rows[path][1]) for path in sorted(rows)})),
        "exact_sources_sha256": sha(first.encode({path: sha(rows[path][2]) for path in sorted(rows)})),
    }


def risk_proof(binding, private_repo=None):
    require(binding["homework_commit"] == RISK_SOURCE and binding["h0_supplement_commit"] == RISK_PROOF
            and binding["public_target_module"] == RISK_ROOT, "CF17 archive names the wrong proof epoch or root")
    public_git = FixedGit(ROOT)
    private_git = FixedGit(private_repo) if private_repo is not None else None
    try:
        fixed = public_git.read(RISK_PROOF, society_book.MAP)
        require(sha(fixed) == binding["society_book_map_sha256"], "CF17 archive does not bind the fixed society map")
        fixed = json.loads(fixed)
        claim, = [row for row in fixed["claims"] if row["id"] == RISK_CLAIM]
        package, = [row for row in fixed["proof_packages"] if row["id"] == RISK_PACKAGE]
        require(package["lean_target"] == RISK_ROOT and package["source_commit"] == RISK_SOURCE,
                "CF17 fixed package scope differs")
        exported, _, _, inverse = source_view.load_map()
        entries = release.package_entries([claim], package)
        scope = release.package_inputs(ROOT, exported, package, entries)
        path = release.module_path(RISK_ROOT)
        require(binding["public_target_path"] == path
                and sha(public_git.read(RISK_PROOF, path)) == scope["files"][path] == binding["public_target_sha256"],
                "CF17 root identity differs")
        summary = risk_sources(binding, claim, scope, inverse, public_git, private_git)
    finally:
        public_git.close()
        if private_git is not None:
            private_git.close()

    raw = (ROOT / ACCEPTANCE).read_bytes()
    acceptance = json.loads(raw)
    historical = acceptance["historical_research_receipt"]
    require(historical["status"] == "T1"
            and historical["original_sha256"] == binding["independent_t1_receipt"]["sha256"]
            and set(historical["public_axioms"]) == finite.ALLOWED_AXIOMS,
            "CF17 historical receipt identity differs")
    types = finite.artifact(ROOT, acceptance["declaration_types"])
    type_rows = types["declarations"]
    positions = {(row["module"], row["qualified_name"]): i for i, row in enumerate(type_rows)}
    for _, _, _, entry in entries:
        for declaration in entry["declarations"]:
            index = positions[entry["public"]["module"], declaration["qualified_name"]]
            digest = sha(type_rows[index]["type"].encode())
            require(digest == declaration["complete_type"]["type_sha256"], "CF17 complete type differs from the fixed receipt")
            declaration["complete_type"] = {"declaration_index": index, "type_sha256": digest}
    scoped = {"claims": [claim], "proof_packages": [package], "acceptance": acceptance}
    count = finite.recorded_acceptance(scoped, {RISK_PACKAGE: scope}, {RISK_PACKAGE: entries}, ROOT)
    require(count == len(positions) == 17, "CF17 declared type inventory differs")
    require(set(finite.artifact(ROOT, acceptance["trust"])["results"][0]["audit"]["axioms"]) == finite.ALLOWED_AXIOMS,
            "CF17 trust scope differs from the standard three axioms")
    require(summary["selected_roots"] == 58
            and summary["source_declaration_locations"] == binding["declaration_count"] == 398,
            "CF17 source inventory counts differ")
    return {
        "proof_commit": RISK_PROOF, "source_commit": RISK_SOURCE, "lean_target": RISK_ROOT,
        "package": package, "claim": claim, "acceptance": {"path": ACCEPTANCE, "sha256": sha(raw)},
        "summary": {**summary, "compiled_closure_modules": scope["modules"], "complete_types": count},
    }


def derive(payload, private_repo=None):
    first.publication(require_ready=True)
    first_payload = first.archive_inputs()
    inherited = first.derive(first_payload)
    require((ROOT / first.MAP).read_bytes() == first.encode(inherited), "Frozen capital map differs")
    members = (inherited["inputs"]["binding_member"], inherited["inputs"]["selection_member"])
    require(all(payload[member] == first_payload[member] for member in members), "Inherited source selection differs")
    binding = json.loads(payload[RISK_MEMBER])
    risk = risk_proof(binding, private_repo)
    results = {lang: first.numbered_results(payload[first.MEMBER + f"manuscript{suffix}.md"], lang, count=19)
               for lang, suffix in (("zh", ""), ("en", "-en"))}
    prior = {row["number"]: row for row in inherited["claims"]}
    claims = []
    for number in range(1, 20):
        old = None if number == 12 else prior[number - int(number > 12)]
        row = deepcopy(old) if old else {"kind": "theorem", "source_ids": []}
        row.update(id=f"R{number}", number=number, inherited_result=old["id"] if old else None,
                   title={lang: results[lang][number]["title"] for lang in results},
                   written={lang: results[lang][number]["location"] for lang in results})
        if number in (1, 12):
            row["risk_claim"] = RISK_CLAIM
        claims.append(row)
    return {
        "schema": "capital-formation/claim-map@2", "paper": first.PAPER, "edition": "v2",
        "inputs": {**inherited["inputs"], "archive": ARCHIVE, "risk_binding_member": RISK_MEMBER,
                   "risk_binding_sha256": sha(payload[RISK_MEMBER]),
                   "manuscripts": {first.MEMBER + name: sha(payload[first.MEMBER + name]) for name in first.TEXTS}},
        "inherited": {"map": first.MAP, "map_sha256": sha(first.encode(inherited)), "proof_commit": first.PROOF,
                      "source_commit": first.SOURCE, "summary": inherited["summary"]},
        "risk_compensation": risk, "claims": claims,
    }


def published_files():
    manifest = json.loads((ROOT / RELEASE / "manifest.json").read_bytes())
    paper, = manifest["papers"]
    require(manifest["published"] is True and paper["is_published"] is True and paper["is_draft"] is False
            and paper["paper"] == first.PAPER and paper["version"] == "v2" and paper["source_commit"] == RISK_PROOF
            and paper["previous_doi"] == "10.5281/zenodo.23927949", "Missing verified second-edition publication")
    expected = {f"{first.PAPER}{suffix}.pdf" for suffix in ("", "-en", "-supplement", "-supplement-en")}
    expected.add(Path(ARCHIVE).name)
    files, downloads = paper["files"], paper["anonymous_verification"]
    require(len(files) == len(downloads) == 5 and {row["key"] for row in files} == {row["key"] for row in downloads} == expected,
            "Second-edition file inventory differs")
    for item in files:
        name = item["path"]
        first.safe_relative(name)
        raw = (ROOT / RELEASE / name).read_bytes()
        require(Path(name).name == item["key"] and len(raw) == item["bytes"] and sha(raw) == item["sha256"],
                "Published file differs: " + name)
    require(all(item["HTTP_status"] == 200 and item["sha256_matches_local_file"] is True
                and item["md5_matches_Zenodo"] is True for item in downloads),
            "Publication has no complete anonymous read-back")
    return paper["doi"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help="derive the map from a checked local editorial archive")
    plan.add_argument("--archive", type=Path, required=True)
    plan.add_argument("--homework-repository", type=Path)
    plan.add_argument("--output", type=Path, required=True)
    entry = commands.add_parser("entry", help="check the published files, exact source views and recorded acceptance")
    entry.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        if args.command == "plan":
            mapping = derive(first.archive_inputs(args.archive.resolve()), args.homework_repository)
            args.output.write_bytes(first.encode(mapping))
            doi = None
        else:
            doi = published_files()
            mapping = derive(first.archive_inputs(ARCHIVE))
            require((ROOT / MAP).read_bytes() == first.encode(mapping), "Second-edition map differs")
        report = {"status": "passed", "edition": "v2", "doi": doi, "claims": len(mapping["claims"]),
                  "inherited_complete_types": mapping["inherited"]["summary"]["existing_complete_type_observations_in_selected_modules"],
                  **mapping["risk_compensation"]["summary"]}
        if args.command == "entry" and args.output is not None:
            args.output.mkdir(parents=True, exist_ok=True)
            (args.output / "result.json").write_bytes(first.encode(report))
        print(json.dumps(report, ensure_ascii=False))
    except (OSError, ValueError, KeyError, TypeError, StopIteration, zipfile.BadZipFile,
            ExportError, release.ReleaseError, source_view.ViewError) as error:
        parser.exit(1, f"Capital second-edition check failed: {error}\n")


if __name__ == "__main__":
    main()
