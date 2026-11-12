#!/usr/bin/env python3
"""Check the capital paper's publication and reused, fixed SourceDF proof scope.

This reads public release bytes and existing Git/acceptance records. It does not
compile Lean, rerun scientific programs, or require the private research repo.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import zipfile

from first_release_cache import VIEW_ENGINES, load_view_engines
from whole_ledger_export import FixedGit

ROOT = Path(__file__).resolve().parents[1]
PAPER = "capital-formation"
SOURCE = "df421ff600085cbc290a7ae946193961bed7c83b"
PROOF = "2d6fbc96e33b7c4c3cfd91104fda74e3caeda045"
RELEASE = "papers/capital-formation/2026-11-04"
ARCHIVE = RELEASE + "/editable/capital-formation-v1-editable.zip"
MAP = "docs/capital-formation-map.json"
MEMBER = "papers/capital-formation/"
PACKAGE = "economic-constitution-source-df"
LEAN_ROOT = "H0mework.Papers.EconomicConstitutionSourceDF"
TEXTS = ("manuscript.md", "manuscript-en.md", "supplement.md", "supplement-en.md")


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def encode(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def require(condition, message: str) -> None:
    if not condition:
        raise ValueError(message)


def safe_relative(name: str) -> None:
    path = PurePosixPath(name)
    require(bool(name) and str(path) == name and not path.is_absolute()
            and ".." not in path.parts and "\\" not in name,
            "Unsafe release or archive path")


def archive_inputs(path=ARCHIVE) -> dict[str, bytes]:
    with zipfile.ZipFile(ROOT / path) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)), "Repeated ZIP member")
        for info in archive.infolist():
            safe_relative(info.filename)
            require(not stat.S_ISLNK(info.external_attr >> 16), "ZIP symlink")
        payload = {name: archive.read(name) for name in names}
        require(archive.testzip() is None, "ZIP CRC mismatch")
    manifest = json.loads(payload["PACKAGE-MANIFEST.json"])
    expected = {"PACKAGE-MANIFEST.json"}
    for entry in manifest["members"]:
        name = entry["path"]
        require(name not in expected and name in payload, "Repeated or missing package input")
        expected.add(name)
        require(len(payload[name]) == entry["bytes"] and sha(payload[name]) == entry["sha256"],
                "Package input identity mismatch: " + name)
    require(set(payload) == expected, "Unregistered package input")
    return payload


def numbered_results(raw: bytes, language: str, count=18) -> dict[int, dict]:
    text = raw.decode()
    words = "定理|命题" if language == "zh" else "Theorem|Proposition"
    pattern = re.compile(r"^\*\*(" + words + r")\s*(\d+)\s*[（(]([^\n]*?)[）)]\s*[。.]?\*\*", re.M)
    results = {}
    for match in pattern.finditer(text):
        number = int(match[2])
        require(number not in results, "Repeated numbered result")
        headings = list(re.finditer(r"^#{2,4}\s+(\d+(?:\.\d+)*)\s", text[:match.start()], re.M))
        require(bool(headings), "Result has no paper section")
        section = headings[-1][1]
        results[number] = {"kind": match[1], "title": match[3], "section": section,
                           "location": f"§{section} {match[1]} {number}"}
    require(set(results) == set(range(1, count + 1)), f"The paper must retain all {count} numbered results")
    for number, result in results.items():
        require(result["kind"] == (("命题" if language == "zh" else "Proposition") if number == 10
                                   else ("定理" if language == "zh" else "Theorem")),
                "Theorem/proposition classification changed")
    return results


def derive(payload: dict[str, bytes]) -> dict:
    binding_raw = payload[MEMBER + "records/public-source-binding.json"]
    selection_raw = payload[MEMBER + "records/source-selection.json"]
    binding, selection = json.loads(binding_raw), json.loads(selection_raw)
    require(binding["public_commit"] == PROOF and binding["source_commit"] == SOURCE,
            "Fixed source epoch changed")
    require(binding["source_selection_sha256"] == sha(selection_raw), "Source selection mismatch")
    require(selection["public_commit"] == PROOF and selection["source_commit"] == SOURCE,
            "Selection epoch mismatch")
    require(len(binding["entries"]) == len(selection["entries"]) == 105, "Source inventory changed")
    for entry, original in zip(binding["entries"], selection["entries"]):
        for key, value in original.items():
            if key == "consumers":
                require(len(entry[key]) == len(value), "Consumer inventory changed")
                require(all(all(actual.get(k) == v for k, v in row.items())
                            for actual, row in zip(entry[key], value)), "Consumer source metadata changed")
            else:
                require(entry.get(key) == value, "Selected source metadata changed: " + key)
    git = FixedGit(ROOT)
    try:
        read = lambda path: git.read(PROOF, path)
        evidence = binding["evidence"]
        engines = {path: read(path) for path in VIEW_ENGINES}
        for path, digest in evidence["verified_helper_bytes"].items():
            raw = engines[path] if path in engines else read(path)
            require(sha(raw) == digest, "Pinned source-view helper bytes changed")
        sv, _ = load_view_engines(engines, ROOT)
        for ref in (evidence["claim_map"], evidence["export_map"], evidence["acceptance_summary"]):
            require(sha(read(ref["path"])) == ref["sha256"], "Pinned evidence identity mismatch")
        old_map = json.loads(read(evidence["claim_map"]["path"]))
        require(old_map["acceptance"]["status"] == "passed", "SourceDF acceptance is not passed")
        package = next(p for p in old_map["proof_packages"] if p["id"] == PACKAGE)
        require(package == binding["accepted_package"] and package["lean_target"] == LEAN_ROOT,
                "Accepted package contract changed")
        receipts = {}
        for kind, ref in evidence["receipts"].items():
            raw = read(ref["path"])
            require(sha(raw) == ref["sha256"], "Receipt compressed hash mismatch")
            raw = gzip.decompress(raw) if ref.get("compression") == "gzip" else raw
            require(sha(raw) == ref["payload_sha256"], "Receipt payload hash mismatch")
            receipt = json.loads(raw)
            require(receipt.get("ok", receipt.get("status") == "passed") is True
                    and receipt["inputs_unchanged"] is True
                    and receipt["input_identity"] == receipt["input_identity_after"],
                    "Existing acceptance is not a stable successful run")
            receipts[kind] = receipt
        types = receipts["declaration_types"]["declarations"]
        require(len(types) == 3313, "Existing complete-type inventory changed")
        exported = json.loads(read(evidence["export_map"]["path"]))
        rows = {row["target"]: row for row in exported["modules"]}
        imports, paths, contents = {}, {}, {}
        def module(target):
            if target not in contents:
                path = rows[target]["path"] if target in rows else "Lean/" + target.replace(".", "/") + ".lean"
                raw = read(path)
                if target in rows:
                    require(sha(raw) == rows[target]["target_sha256"], "Published module bytes changed")
                contents[target], paths[target] = raw, path
                imports[target] = [name for _, _, name in sv.import_tokens(raw.decode())]
            return contents[target]
        closure, todo = set(), [LEAN_ROOT]
        while todo:
            target = todo.pop()
            if target in closure:
                continue
            closure.add(target)
            module(target)
            todo.extend(name for name in imports[target] if name in rows and name not in closure)
        require(len(closure) == 2825, "SourceDF recursive import closure changed")
        layouts, active = {}, set()
        def layout(target):
            if target not in layouts:
                require(target not in active, "Cyclic import layout")
                active.add(target)
                row = rows[target]
                layouts[target] = sv.layout_identity(row["source_path"], row["source_sha256"], row.get("source_origin"),
                                                     [layout(name) for name in imports[target] if name in rows])
                active.remove(target)
            return layouts[target]
        consumer_owners, observed, adopted = {}, set(), set()
        lexical_relationships = sum(not consumer.get("public_module") for entry in binding["entries"]
                                    for consumer in entry.get("consumers", []))
        for entry in binding["entries"]:
            if not entry["public"]:
                ref = entry["preserved_source"]
                require(sha(payload[MEMBER + ref["path"]]) == ref["sha256"] == entry["source_sha256"],
                        "Auxiliary source identity mismatch")
                continue
            public, target = entry["public"], entry["public"]["module"]
            require(target in closure, "Selected owner is outside the accepted closure")
            adopted.add(target)
            row = rows[target]
            record = sv.source_record(row, entry["path"], SOURCE)
            require(record is not None and sv.row_at(record, SOURCE)
                    and record["source_sha256"] == entry["source_sha256"], "Source alias/epoch mismatch")
            require(paths[target] == public["path"] and sha(module(target)) == public["target_sha256"]
                    and imports[target] == public["actual_imports"]
                    and layout(target) == public["recursive_layout_sha256"], "Public owner environment mismatch")
            require(public["source_record"] == {key: record.get(key) for key in (
                        "source_path", "source_revision", "source_revisions", "source_sha256", "source_origin")},
                    "Stored source alias metadata differs from the fixed owner")
            chain = public["import_chain_from_accepted_root"]
            require(chain[0] == LEAN_ROOT and chain[-1] == target
                    and all(child in imports[parent] for parent, child in zip(chain, chain[1:])),
                    "Recorded import path is not actual")
            for observation in entry["type_observations"]:
                index = observation["declaration_index"]
                item = types[index]
                require(item["package"] == PACKAGE and item["module"] == target
                        and item["qualified_name"] == observation["qualified_name"]
                        and sha(item["type"].encode()) == observation["type_sha256"]
                        and item["kernel_equivalent"] is True and not item["unsafe"] and not item["partial"]
                        and item["axioms"] == observation["axioms"]
                        and set(item["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"},
                        "Existing complete-type observation mismatch")
                observed.add(index)
            by_name = {observation["qualified_name"]: observation for observation in entry["type_observations"]}
            for declaration in entry["previous_claim_map_declarations"]:
                observation = by_name[declaration["qualified_name"]]
                require(declaration["complete_type"]["declaration_index"] == observation["declaration_index"]
                        and declaration["complete_type"]["type_sha256"] == observation["type_sha256"],
                        "Adopted declaration and existing type observation differ")
                source_line = declaration["source_line"]
                lines = module(target).decode().splitlines()
                require(0 < source_line <= len(lines)
                        and declaration["qualified_name"].split(".")[-1] in lines[source_line - 1],
                        "Declaration source line no longer identifies the public declaration")
            for consumer in entry.get("consumers", []):
                owner = consumer.get("public_module")
                if not owner:
                    continue
                require(owner in closure and target in imports[owner], "Consumer is not an actual accepted direct import")
                rec = sv.source_record(rows[owner], consumer["path"], SOURCE)
                require(rec is not None and sv.row_at(rec, SOURCE)
                        and rec["source_sha256"] == consumer["source_sha256"], "Consumer epoch/alias mismatch")
                consumer_owners[owner] = {"public": {"module": owner, "path": paths[owner], "sha256": sha(module(owner))},
                                          "source_path": consumer["path"], "source_sha256": consumer["source_sha256"]}
        require(len(adopted) == 100 and len(observed) == 160, "Adopted owner/type scope changed")
        require(len(consumer_owners.keys() - adopted) == 63 and lexical_relationships == 31,
                "Direct-consumer classification changed")
    finally:
        git.close()
    results = {language: numbered_results(payload[MEMBER + "manuscript" + ("-en" if language == "en" else "") + ".md"], language)
               for language in ("zh", "en")}
    claims = []
    for number in range(1, 19):
        ids = [entry["id"] for entry in binding["entries"]
               if any(re.fullmatch(r"(?:Theorem|Proposition) " + str(number), at) for at in entry["manuscript"])]
        require(bool(ids), "Numbered result has no selected sources")
        claims.append({"id": "R" + str(number), "number": number,
                       "kind": "proposition" if number == 10 else "theorem", "source_ids": ids,
                       "title": {language: results[language][number]["title"] for language in results},
                       "written": {language: results[language][number]["location"] for language in results}})
    return {"schema": "capital-formation/claim-map@1", "paper": PAPER, "source_commit": SOURCE, "proof_commit": PROOF,
            "inputs": {"archive": ARCHIVE, "binding_member": MEMBER + "records/public-source-binding.json",
                       "binding_sha256": sha(binding_raw), "selection_member": MEMBER + "records/source-selection.json",
                       "selection_sha256": sha(selection_raw),
                       "manuscripts": {MEMBER + name: sha(payload[MEMBER + name]) for name in TEXTS}},
            "acceptance": {"status": "passed", "basis": "reused fixed SourceDF acceptance",
                           "proof_commit": PROOF, "package": PACKAGE, "evidence": evidence,
                           "new_Lean_execution": False, "new_scientific_execution": False},
            "summary": {**binding["summary"], "public_direct_consumer_owners": len(consumer_owners),
                        "additional_public_direct_consumer_owners": len(consumer_owners.keys() - adopted),
                        "public_support_owners": len(adopted | consumer_owners.keys()),
                        "source_only_consumer_relationships": lexical_relationships},
            "public_consumers": dict(sorted(consumer_owners.items())), "claims": claims}


def publication(require_ready: bool) -> None:
    manifest = json.loads((ROOT / RELEASE / "manifest.json").read_bytes())
    paper = next(p for p in manifest["papers"] if p["paper"] == PAPER)
    require(paper["source_commit"] == PROOF and bool(re.fullmatch(r"10\.\d{4,9}/\S+", paper["doi"])),
            "Publication has no fixed proof source and DOI")
    require(len(paper["files"]) == 5, "Publication must contain four PDFs and one editable package")
    for entry in paper["files"]:
        safe_relative(entry["path"])
        raw = (ROOT / RELEASE / entry["path"]).read_bytes()
        require(len(raw) == entry["bytes"] and sha(raw) == entry["sha256"], "Published file identity mismatch")
    if require_ready:
        require(manifest.get("published") is True and paper.get("is_published") is True
                and paper.get("is_draft") is False, "Publication is still a draft")
        downloads = paper.get("anonymous_verification", [])
        require(len(downloads) == 5 and {item["key"] for item in downloads} == {item["key"] for item in paper["files"]}
                and all(item["HTTP_status"] == 200 and item["sha256_matches_local_file"] is True
                        and item["md5_matches_Zenodo"] is True for item in downloads),
                "Published files have no complete successful anonymous read-back")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("command", choices=("plan", "entry", "verify-map"))
    ap.add_argument("--require-ready", action="store_true")
    ap.add_argument("--output", type=Path, help="For plan: JSON map file; for entry: receipt directory")
    args = ap.parse_args()
    try:
        # Check the committed outer-file identities before decompressing editable inputs.
        publication(args.require_ready)
        payload = archive_inputs()
        mapping = derive(payload)
        if args.command == "plan":
            require(args.output is not None, "plan requires an output map path")
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_bytes(encode(mapping))
            print(json.dumps({"status": "planned", "claims": len(mapping["claims"]), **mapping["summary"]}, ensure_ascii=False))
            return
        require((ROOT / MAP).read_bytes() == encode(mapping), "Capital claim map is stale")
        binding = json.loads(payload[MEMBER + "records/public-source-binding.json"])
        for entry in binding["entries"]:
            if entry.get("preserved_source"):
                ref = entry["preserved_source"]
                require(sha((ROOT / RELEASE / ref["path"]).read_bytes()) == ref["sha256"],
                        "Public auxiliary source bytes changed")
        report = {"status": "passed", "scope": "publication and fixed proof-source identity; existing acceptance reused",
                  "claims": len(mapping["claims"]), "proof_commit": PROOF, **mapping["summary"],
                  "new_Lean_execution": False, "new_scientific_execution": False}
        if args.output:
            args.output.mkdir(parents=True, exist_ok=True)
            (args.output / "result.json").write_bytes(encode(report))
        print(json.dumps(report, ensure_ascii=False))
    except (OSError, ValueError, KeyError, TypeError, StopIteration, zipfile.BadZipFile) as error:
        ap.exit(1, "Capital publication check failed: " + str(error) + "\n")


if __name__ == "__main__":
    main()
