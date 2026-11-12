#!/usr/bin/env python3
"""Check the third edition against the inherited society proofs and the added selection."""

from __future__ import annotations

import argparse
from contextlib import ExitStack, closing, contextmanager
import json
from pathlib import Path
import zipfile

import first_release as release
import generated_society as finite
import source_view
import whole_ledger
from whole_ledger_export import ExportError, FixedGit

ROOT = release.ROOT
MAP = "docs/generated-society-v3-map.json"
SCHEMA = "h0mework/generated-society-v3-map@1"
EDITION = "papers/generated-society/2026-11-12-v3"
ARCHIVE = "editable/generated-society-v3-editable.zip"
BINDING = "papers/generated-society/records/m7-source-binding-v3.json"
MAIN_PROOF = "2d6fbc96e33b7c4c3cfd91104fda74e3caeda045"
GO_PROOF = "fd6147f8c337d88ebf72d91ddadef0aa601e6c2e"
sha, require = release.sha, finite.require


@contextmanager
def edition_map():
    previous = release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP
    release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = SCHEMA, SCHEMA, MAP
    try:
        yield
    finally:
        release.SCHEMA, whole_ledger.SCHEMA, whole_ledger.MAP = previous


def source_identities(data, homework=None):
    require(data["proof_snapshots"] == {"main": MAIN_PROOF, "cross_domain": GO_PROOF},
            "Third-edition proof snapshots differ")
    with ExitStack() as stack:
        stack.enter_context(finite.source_root(ROOT))
        git = stack.enter_context(closing(FixedGit(ROOT)))
        private = stack.enter_context(closing(FixedGit(homework))) if homework is not None else None
        _, _, _, inverse = source_view.load_map()
        checked = set()
        for claim, _, _, entry in release.claim_entries(release.selected_claims(data)):
            proof = GO_PROOF if claim["id"] == "cross-domain-actors" else MAIN_PROOF
            target = entry["public"]
            module, path = target["module"], target["path"]
            epoch, source = entry["source_commit"], entry["source_path"]
            key = proof, module, epoch, source
            if key in checked:
                continue
            owner = source_view.source_record(inverse[module], source, epoch)
            require(owner is not None and source_view.row_at(owner, epoch),
                    "No original epoch for " + path)
            require(sha(git.read(proof, path)) == target["sha256"], "Fixed public source differs: " + path)
            public_view, original = source_view.module_views(owner, inverse)
            require(bool(public_view) and sha(original) == entry["source_sha256"], "Original bytes differ: " + source)
            if private is not None:
                require(original == private.read(epoch, source), "Exact Homework bytes differ: " + source)
            checked.add(key)
    return len(checked)


def published_files(data):
    folder = ROOT / EDITION
    manifest = release.read_json(folder / "manifest.json")
    paper, = manifest["papers"]
    require(manifest["published"] is True and paper["is_published"] is True and paper["is_draft"] is False
            and paper["paper"] == "generated-society" and paper["version"] == "v3"
            and paper["previous_doi"] == "10.5281/zenodo.23917896"
            and paper["source_commit"] == MAIN_PROOF, "Missing verified third-edition publication")
    expected = {f"pdf/generated-society{suffix}.pdf" for suffix in ("", "-en", "-supplement", "-supplement-en")}
    expected.add(ARCHIVE)
    files, downloads = paper["files"], paper["anonymous_verification"]
    require(len(files) == len(downloads) == len(expected) and {row["path"] for row in files} == expected
            and {row["key"] for row in downloads} == {Path(path).name for path in expected},
            "Third-edition publication inventory differs")
    for item in files:
        raw = (folder / item["path"]).read_bytes()
        require(len(raw) == item["bytes"] and sha(raw) == item["sha256"], "Published file differs: " + item["path"])
    require(all(item["HTTP_status"] == 200 and item["sha256_matches_local_file"] is True
                and item["md5_matches_Zenodo"] is True for item in downloads), "Anonymous read-back is incomplete")
    with zipfile.ZipFile(folder / ARCHIVE) as archive:
        raw = archive.read(BINDING)
        require(sha(raw) == data["source_binding_sha256"], "Publication source binding differs")
        binding = json.loads(raw)
        mapped = {entry["public"]["path"]: entry
                  for claim, _, _, entry in release.claim_entries(release.selected_claims(data))
                  if claim["id"] != "cross-domain-actors"}
        for key in ("m7_modules", "m8_m10_modules", "m9_modules"):
            for row in binding[key]:
                entry = mapped[row["h0mework_path"]]
                compiled = row["compiled_source"]
                require((compiled["commit"], compiled["path"], compiled["sha256"], row["h0mework_sha256"]) ==
                        (entry["source_commit"], entry["source_path"], entry["source_sha256"], entry["public"]["sha256"]),
                        "Publication source identity differs: " + row["h0mework_path"])
    return paper["doi"]


def entry(output, *, proof_only=False, homework=None):
    identity = release.verify_map(ROOT, MAP, require_ready=True)
    require(identity["ok"], "Third-edition source map failed: " + str(identity["errors"]))
    data, exported = release.load_maps(ROOT, MAP)
    scopes, entries = finite.package_scopes(data, exported, ROOT)
    count = finite.recorded_acceptance(data, scopes, entries, ROOT)
    recovered = source_identities(data, homework)
    directory = release.new_output(ROOT, output)
    inherited = finite.entry(directory / "inherited", require_ready=True)
    result = {
        "status": "passed",
        "edition": "v3",
        "doi": None if proof_only else published_files(data),
        "inherited_claims": inherited["claims"],
        "inherited_complete_types": inherited["recorded_complete_types_verified"],
        "added_claims": identity["claims"],
        "recovered_source_owners": recovered,
        "checked_complete_types": count,
        "packages": {name: scope["modules"] for name, scope in scopes.items()},
    }
    (directory / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("build", "trust", "types", "entry"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--proof-only", action="store_true", help="validate proof receipts before publication")
    parser.add_argument("--homework-repository", type=Path, help="also compare original bytes with fixed Homework blobs")
    args = parser.parse_args()
    try:
        with edition_map():
            if args.command in {"build", "trust"}:
                result = release.execute(args.command, ROOT, MAP, args.output)
                passed = result["ok"]
            elif args.command == "types":
                result = whole_ledger.types(args.output)
                passed = result["status"] == "passed"
            else:
                result = entry(args.output, proof_only=args.proof_only, homework=args.homework_repository)
                print(json.dumps(result, ensure_ascii=False))
                return
        print(json.dumps({"status": "passed" if passed else "failed", "result": str(args.output / "result.json")}))
        if not passed:
            raise SystemExit(1)
    except (OSError, ValueError, KeyError, TypeError, ExportError, release.ReleaseError,
            source_view.ViewError, zipfile.BadZipFile) as error:
        parser.exit(1, f"Society third-edition check failed: {error}\n")


if __name__ == "__main__":
    main()
