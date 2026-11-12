#!/usr/bin/env python3
"""Verify the third-edition economic constitution and its exact proof sources."""

from __future__ import annotations

import argparse
from contextlib import ExitStack, closing
import json
from pathlib import Path
import zipfile

import economic_constitution as inherited
import first_release as release
import generated_society as finite
import source_view
import whole_ledger
from whole_ledger_export import ExportError, FixedGit

ROOT = release.ROOT
MAP = "docs/economic-constitution-v3-map.json"
SCHEMA = "h0mework/economic-constitution-v3-map@1"
SLUG = "economic-constitution"
EDITION = f"papers/{SLUG}/2026-11-13-v3"
ARCHIVE = f"editable/{SLUG}-v3-editable.zip"
BINDING = f"papers/{SLUG}/records/v3-source-binding.json"
V2_ARCHIVE = f"papers/society-economic/2026-11-03-v2/editable/{SLUG}-v2-editable.zip"
PREVIOUS_DOI = "10.5281/zenodo.23917902"
require = finite.require


def source_identities(data, homework=None):
    with ExitStack() as stack:
        stack.enter_context(finite.source_root(ROOT))
        git = stack.enter_context(closing(FixedGit(ROOT)))
        private = stack.enter_context(closing(FixedGit(homework))) if homework else None
        _, _, _, index = source_view.load_map()
        checked = set()
        for _, role, _, entry in release.claim_entries(release.selected_claims(data)):
            if release.entry_kind(role, entry) != "lean":
                continue
            public = entry["public"]
            path = public["path"]
            revision = data["proof_snapshots"][data["source_snapshots"][path]]
            source = entry["source_path"]
            epoch = entry["source_commit"]
            key = path, epoch, source
            if key in checked:
                continue
            row = source_view.source_record(index[public["module"]], source, epoch)
            require(row is not None and source_view.row_at(row, epoch), "Original epoch differs for " + path)
            require(release.sha(git.read(revision, path)) == public["sha256"], "Fixed public bytes differ for " + path)
            _, raw = source_view.module_views(row, index)
            require(release.sha(raw) == entry["source_sha256"], "Exact inverse differs for " + source)
            if private:
                require(raw == private.read(epoch, source), "Original Homework bytes differ for " + source)
            checked.add(key)
    return len(checked)


def result_bindings(data, archived):
    results = data["results"]
    require([row["number"] for row in results] ==
            ["1.2", "2.1", "2.2", "2.3", "3.1", "4.1", "4.2", "4.3", "5.1", "6.1",
             "7.1", "7.2", "7.3", "7.4", "8.1", "9.1", "9.2", "9.3"],
            "Third-edition formal result inventory differs")
    references = {row["record_id"] for group in archived["by_key"].values() for row in group}
    claims = {row["id"] for row in data["claims"]}
    used_references, used_claims = set(), set()
    for row in results:
        old, new = set(row["inherited_interface_ids"]), set(row["proof_claims"])
        require(old <= references and new <= claims and (old or new),
                "Unknown or empty source binding for result " + row["number"])
        used_references |= old
        used_claims |= new
    require(used_references == references and used_claims == claims, "A selected interface is unused")


def published_files(data, archived_raw):
    folder = ROOT / EDITION
    manifest = release.read_json(folder / "manifest.json")
    paper, = manifest["papers"]
    require(manifest["published"] is True and paper["is_published"] is True and paper["is_draft"] is False
            and paper["paper"] == SLUG and paper["version"] == "v3" and paper["previous_doi"] == PREVIOUS_DOI
            and paper["proof_commits"] == data["proof_snapshots"], "Third-edition publication binding differs")
    expected = {f"pdf/{SLUG}{suffix}.pdf" for suffix in ("", "-en", "-supplement", "-supplement-en")}
    expected.add(ARCHIVE)
    files, downloads = paper["files"], paper["anonymous_verification"]
    require(len(files) == len(downloads) == len(expected) and {row["path"] for row in files} == expected
            and {row["key"] for row in downloads} == {Path(path).name for path in expected},
            "Third-edition publication inventory differs")
    for row in files:
        raw = (folder / row["path"]).read_bytes()
        require(len(raw) == row["bytes"] and release.sha(raw) == row["sha256"], "Published bytes differ for " + row["path"])
    require(all(row["HTTP_status"] == 200 and row["sha256_matches_local_file"] and row["md5_matches_Zenodo"]
                for row in downloads), "Anonymous read-back is incomplete")
    with zipfile.ZipFile(folder / ARCHIVE) as archive:
        require(archive.read(data["inherited"]["binding_path"]) == archived_raw,
                "Published inherited binding differs")
        raw = archive.read(BINDING)
        require(release.sha(raw) == data["source_binding_sha256"], "Third-edition binding hash differs")
        binding = json.loads(raw)
        require(binding["proof_snapshots"] == data["proof_snapshots"] and binding["results"] == data["results"]
                and binding["proof_claims"] == data["claims"] and binding["source_snapshots"] == data["source_snapshots"],
                "Published formal result bindings differ")
    return paper["doi"]


def entry(output, *, proof_only=False, homework=None):
    identity = release.verify_map(ROOT, MAP, require_ready=True)
    require(identity["ok"], "Third-edition source map failed: " + str(identity["errors"]))
    data, exported = release.load_maps(ROOT, MAP)
    scopes, entries = finite.package_scopes(data, exported, ROOT)
    count = finite.recorded_acceptance(data, scopes, entries, ROOT)
    recovered = source_identities(data, homework)
    directory = release.new_output(ROOT, output)
    baseline = inherited.entry(directory / "inherited", require_ready=True)
    require(baseline["recorded_complete_types_verified"] == data["inherited"]["complete_types"],
            "Inherited type count differs")
    with zipfile.ZipFile(ROOT / V2_ARCHIVE) as archive:
        archived = archive.read(data["inherited"]["binding_path"])
    result_bindings(data, json.loads(archived))
    result = {
        "status": "passed", "edition": "v3", "doi": None if proof_only else published_files(data, archived),
        "formal_results": len(data["results"]), "inherited_principles": baseline["claims"],
        "inherited_complete_types": baseline["recorded_complete_types_verified"],
        "checked_complete_types": count, "recovered_source_owners": recovered,
        "packages": {name: scope["modules"] for name, scope in scopes.items()},
    }
    (directory / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("build", "trust", "types", "entry"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--proof-only", action="store_true", help="check proof receipts before publication")
    parser.add_argument("--homework-repository", type=Path, help="also compare exact original bytes with Homework")
    args = parser.parse_args()
    release.SCHEMA = whole_ledger.SCHEMA = SCHEMA
    whole_ledger.MAP = MAP
    try:
        if args.command == "entry":
            print(json.dumps(entry(args.output, proof_only=args.proof_only, homework=args.homework_repository), ensure_ascii=False))
            return
        if args.command == "types":
            result = whole_ledger.types(args.output)
            passed = result["status"] == "passed"
        else:
            result = release.execute(args.command, ROOT, MAP, args.output)
            passed = result["ok"]
        print(json.dumps({"status": "passed" if passed else "failed", "result": str(args.output / "result.json")}))
        if not passed:
            raise SystemExit(1)
    except (OSError, ValueError, TypeError, KeyError, ExportError, release.ReleaseError,
            source_view.ViewError, zipfile.BadZipFile) as error:
        parser.exit(1, f"Economic constitution third-edition check failed: {error}\n")


if __name__ == "__main__":
    main()
