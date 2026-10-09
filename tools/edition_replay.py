#!/usr/bin/env python3
"""Replay the registered Bell consumers from a verified edition source view."""
from __future__ import annotations

import argparse
from contextlib import redirect_stderr, redirect_stdout
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import sysconfig
import time
import traceback
import uuid

import edition_materials
from edition_release import EDITIONS
import first_release as release
import first_release_replay as replay
import source_view


BASE = replay.BELL + "/munich/readout-domain/"
VIEW = "second-edition-physics-registered-forcing"
CHECKS = {
    "v2-bell-shared-background": ("shared_background_intake_rha0030.py", "shared-background-first-rha0030.json"),
    "v2-bell-registered-duhamel": ("registered_duhamel_run_rha0031.py", "registered-duhamel-first-rha0031.json"),
    "v2-bell-first-registered-forcing": ("registered_forcing_run_rha0034.py", "registered-forcing-first-rha0034.json"),
}


def file_sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def verified_inputs(edition, view_root):
    map_name, schema = EDITIONS[edition]
    document = release.read_json(release.ROOT / map_name)
    replay.require(document.get("schema") == schema, "Edition map schema differs")
    configuration = document.get("runtime_views", {}).get(VIEW)
    replay.require(isinstance(configuration, dict), "Bell source view is not registered in this edition")
    identity = replay.read_json(view_root / "view-identity.json")
    replay.require(identity.get("schema") == "h0mework/edition-material-view@1" and
                   identity.get("edition") == edition and identity.get("view") == VIEW and
                   identity.get("source_commit") == configuration["source_commit"],
                   "Restored source-view identity differs")
    original, skipped = source_view.reconstruct(paths=configuration["paths"], at=configuration["source_commit"])
    replay.require(not skipped and set(original) == set(configuration["paths"]) == set(identity["source_files"]),
                   "Restored source-view selectors differ")
    _, modules, artifacts, _ = source_view.load_map()
    bindings = {}
    for name, raw in original.items():
        digest = replay.sha(raw)
        replay.require(identity["source_files"][name] == digest and file_sha(replay.inside(view_root, name)) == digest,
                       "Restored source input changed: " + name)
        row = source_view.pick(modules.get(name, []) + artifacts.get(name, []), name, None,
                               configuration["source_commit"])
        replay.require(row is not None, "Source input is absent from the export map: " + name)
        bindings[name] = {"view_sha256": digest, "source_sha256": row["source_sha256"],
                          "source_revision": row["source_revision"],
                          "source_revisions": row.get("source_revisions", [row["source_revision"]])}
    source_names = set(bindings)
    exported = release.read_json(release.ROOT / release.EXPORT_MAP)
    exported_artifacts = {row["path"]: row for row in exported["artifacts"]}
    expected_resources = []
    for bundle in configuration.get("resource_bundles", []):
        name = replay.relative(bundle["destination"])
        replay.require(name not in bindings, "Frozen resource conflicts with a source input")
        row = exported_artifacts.get(bundle["artifact"])
        replay.require(row is not None, "Frozen resource is absent from the export map")
        source_view.artifact_views(row)
        path = replay.inside(view_root, name)
        replay.require(path.is_file() and path.stat().st_size == bundle["bytes"] and file_sha(path) == bundle["sha256"],
                       "Restored frozen resource changed: " + name)
        bindings[name] = {"view_sha256": bundle["sha256"], "source_sha256": bundle["sha256"],
                          "source_revision": configuration["source_commit"],
                          "source_revisions": [configuration["source_commit"]]}
        expected_resources.append({"artifact": bundle["artifact"], "destination": name, "bytes": bundle["bytes"],
                                   "sha256": bundle["sha256"], "status": "verified"})
    replay.require(identity.get("resources") == expected_resources, "Restored resource inventory differs")
    registered = {row["id"] for claim in document["claims"] for row in claim.get("runtime_contracts", [])
                  if row.get("runtime_view") == VIEW}
    replay.require(set(CHECKS) <= registered, "Bell consumers are not registered in the edition map")
    return replay.PublicInputs(view_root, bindings), source_names, {
        "source_commit": configuration["source_commit"], "claim_map_sha256": file_sha(release.ROOT / map_name),
        "export_map_sha256": file_sha(release.ROOT / release.EXPORT_MAP),
        "source_files": len(source_names), "frozen_resources": len(expected_resources),
        "restored_resource_bytes": sum(row["bytes"] for row in expected_resources)}


class BellBindings(replay.RecordedSourceBindings):
    """Replace only private Git blob lookup with receipt-registered byte lookup."""
    def __init__(self, inputs, source_names):
        # Large generated resources contain numerical trees, not Git labels.
        # Read labels from their small original receipts, preserving every byte.
        metadata = replay.PublicInputs(inputs.root, {name: inputs.bindings[name] for name in source_names})
        super().__init__(metadata)
        self.inputs = inputs

    def collect(self, value):
        if isinstance(value, dict):
            freeze = value.get("scientific_freeze_commit")
            if isinstance(freeze, str):
                for field in ("source_bindings", "checked_prefix_execution_dependencies"):
                    rows = value.get(field)
                    if not isinstance(rows, dict):
                        continue
                    for name, digest in rows.items():
                        row = self.inputs.bindings.get(name)
                        if row is not None and digest == row["source_sha256"]:
                            self.records.setdefault(name, set()).add((freeze, digest))
        super().collect(value)

    def patch_module(self, module):
        # The original mathematical functions and source hashes run unchanged.
        self.name(module.__file__)

    def git_blob(self, command, *args, **kwargs):
        replay.require(not args and not kwargs and isinstance(command, (list, tuple)) and len(command) == 5 and
                       list(command[:2]) == ["git", "-C"] and Path(command[2]).resolve() == self.inputs.root and
                       command[3] == "show", "Original consumer requested an unsupported process")
        # The accepted command is exactly git -C <view> show <label>:<path>.
        commit, separator, name = command[4].partition(":")
        replay.require(separator and name in self.inputs.bindings, "Git blob lookup is outside the verified view")
        path = self.inputs.path(name)
        row = self.inputs.bindings[name]
        replay.require(row["view_sha256"] == row["source_sha256"], "Git blob requires exact original source bytes")
        self.binding(path, row["source_revision"] if commit == "HEAD" else commit)
        return path.read_bytes()


def compare_receipt(actual, frozen, ignored=()):
    replay.require({key: value for key, value in actual.items() if key not in ignored} ==
                   {key: value for key, value in frozen.items() if key not in ignored},
                   "Fresh scientific result differs from the original frozen receipt")


def compare_forcing_output(inputs, original, destination):
    actual = replay.read_json(destination / "summary.json")
    # The registered receipt adds scope notes to the original producer output.
    # Compare the rerun with that byte-bound output and retain the receipt notes.
    summary_binding = original["producer_summary"]
    summary = inputs.path(summary_binding["path"])
    replay.require(summary.stat().st_size == summary_binding["bytes"] and
                   file_sha(summary) == summary_binding["sha256"], "Original producer summary changed")
    compare_receipt(actual, replay.read_json(summary), {"seconds", "forcing_DAG"})
    compare_receipt(actual["forcing_DAG"], original["forcing_DAG"], {"path"})
    fresh_path = destination / "forcing-DAG.json"
    replay.require(fresh_path.stat().st_size == actual["forcing_DAG"]["bytes"] and
                   file_sha(fresh_path) == actual["forcing_DAG"]["sha256"], "Fresh complete forcing DAG identity changed")
    fresh = replay.read_json(fresh_path)
    original_dag = replay.read_json(inputs.path(original["forcing_DAG"]["path"]))
    replay.require(fresh == original_dag, "Complete original forcing DAG changed")
    replay.require(actual["independent_report"] == original["independent_report"],
                   "Original DAG independent compiler differs")
    return {"status": "passed", "scientific_freeze_commit": original["scientific_freeze_commit"],
            "full_frozen_result_equal": True, "original_DAG_independently_checked": True,
            "independent_check_argument": "fresh DAG with exact original bytes",
            "original_producer_summary_sha256": summary_binding["sha256"],
            "independent_report": actual["independent_report"]}


def execute_check(inputs, provider, check_id, work):
    program, receipt = CHECKS[check_id]
    old = replay.read_json(inputs.path(BASE + receipt))
    module = inputs.load(BASE + program, "_h0_edition_" + check_id.replace("-", "_"))
    if check_id == "v2-bell-shared-background":
        actual = module.consume()
        replay.require(actual["evidence_valid"] is True and actual["all_encoder_branches_and_complete_quadtree_checked"] is True,
                       "Original shared-background intake did not accept the whole domain")
        replay.write_json(work / "intake.json", actual)
        return {"status": "passed", "original_receipt_sha256": replay.sha(inputs.path(BASE + receipt).read_bytes()),
                "result": actual}
    if check_id == "v2-bell-registered-duhamel":
        path = work / "registered-duhamel.json"
        module.execute(old["scientific_freeze_commit"], path)
        actual = replay.read_json(path)
        compare_receipt(actual, old, {"seconds", "status"})
        return {"status": "passed", "scientific_freeze_commit": old["scientific_freeze_commit"],
                "full_frozen_result_equal": True, "independent_report": actual["independent_report"]}
    destination = work / "forcing"
    module.execute(old["scientific_freeze_commit"], destination)
    return compare_forcing_output(inputs, old, destination)


def run(edition, check_ids, output, source_root=None):
    destination = release.new_output(release.ROOT, output)
    view_root = (Path(source_root).resolve() if source_root else destination / "view")
    if source_root is None:
        edition_materials.restore(edition, VIEW, view_root)
    inputs, names, identity = verified_inputs(edition, view_root)
    provider = BellBindings(inputs, names)
    work_root = view_root / "runtime-replay" / uuid.uuid4().hex
    work_root.mkdir(parents=True)
    libraries = [sysconfig.get_path(key) for key in ("stdlib", "platstdlib", "purelib", "platlib")]
    scope = replay.RuntimeInputs([view_root, destination, release.ROOT / "tools", *filter(None, libraries)])
    sys.addaudithook(scope.audit)
    started = time.monotonic()
    report = {"schema": "h0mework/edition-replay@1", "edition": edition, "view": VIEW, **identity,
              "checks": [], "python_version": sys.version.split()[0],
              "Git_ancestry_replayed": False, "new_pump_or_free_curve_solves": 0}
    with (destination / "replay.log").open("x") as log, redirect_stdout(log), redirect_stderr(log):
        with replay.original_source_metadata(provider):
            subprocess.check_output = provider.git_blob
            for check_id in check_ids:
                print("Running " + check_id, flush=True)
                work = work_root / check_id
                work.mkdir()
                try:
                    result = execute_check(inputs, provider, check_id, work)
                    result["work_output"] = work.relative_to(view_root).as_posix()
                    report["checks"].append({"id": check_id, **result})
                except Exception as error:
                    traceback.print_exc()
                    report["checks"].append({"id": check_id, "status": "failed", "reason": str(error)})
                    break
    inputs.verify_all()
    report.update(status="passed" if len(report["checks"]) == len(check_ids) and
                  all(row["status"] == "passed" for row in report["checks"]) else "failed",
                  inputs_unchanged=True, seconds=time.monotonic() - started,
                  source_bindings=list(provider.used.values()),
                  loaded_dependencies={name: sys.modules[name].__version__ for name in ("numpy", "sympy", "mpmath")
                                       if name in sys.modules})
    replay.write_json(destination / "report.json", report)
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edition", choices=EDITIONS, required=True)
    parser.add_argument("--check", choices=CHECKS, action="append")
    parser.add_argument("--source-view", help="reuse a previously restored view after verifying its complete identity")
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv)
    sys.dont_write_bytecode = True
    try:
        report = run(args.edition, args.check or list(CHECKS), args.output, args.source_view)
    except (OSError, ValueError, KeyError, release.ReleaseError, replay.ReplayError, source_view.ViewError) as error:
        print(json.dumps({"status": "failed", "reason": str(error)}))
        return 1
    print(json.dumps({"status": report["status"], "checks": [{"id": row["id"], "status": row["status"]}
                                                            for row in report["checks"]],
                      "seconds": report["seconds"]}, indent=2))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
