#!/usr/bin/env python3
"""Verify an actual default source_view restoration from current public metadata."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
import source_view

parser = argparse.ArgumentParser()
parser.add_argument("--view", required=True)
parser.add_argument("--output", required=True)
args = parser.parse_args()
view = (ROOT / args.view).resolve()
output = (ROOT / args.output).resolve()
assert view.is_dir() and view.is_relative_to(ROOT / ".local")
assert output.is_relative_to(ROOT / ".local") and not output.exists()
metadata_path = Path(__file__).resolve().parent / "new-cap-reader-coverage/metadata-coverage.json"
metadata = json.loads(metadata_path.read_bytes())
assert not metadata["metadata_checks"]["errors"]
assert not metadata["metadata_checks"]["missing_source_prefix_coverage"]
assert not metadata["metadata_checks"]["missing_resource_prefix_coverage"]

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def snapshot():
    return {"head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            "files": {p: sha((ROOT / p).read_bytes()) for p in metadata["authority_files"]}}

before = snapshot()
assert before["head"] == metadata["actual_head"]
assert before["files"] == metadata["authority_files"]
_, modules, artifacts, _ = source_view.load_map()
cap = metadata["source_cap"]
sources = {}
errors = []
for name in metadata["union_original_layout_paths"]:
    row = source_view.pick(modules[name], name, None, cap)
    assert row is not None
    expected = row.get("view_sha256", row["source_sha256"])
    file = view / name
    actual = sha(file.read_bytes()) if file.is_file() else None
    sources[name] = {"expected_view_sha256": expected, "actual_sha256": actual,
                     "pinned_original_sha256": row["source_sha256"], "ok": actual == expected}
    if actual != expected:
        errors.append({"kind": "source", "path": name, "expected": expected, "actual": actual})
resource_names = {r["original_path"] for r in metadata["resources"]}
restored_artifacts = {}
for entry in metadata["command_expected_artifacts"]:
    name = entry["source"]
    row = source_view.pick(artifacts[name], name, None, cap)
    assert row is not None
    # This is the production verifier for gzip and published scientific payloads.
    # No private unnormalized receipt bytes are needed by a default public view.
    raw, _ = source_view.artifact_views(row)
    expected = sha(raw)
    file = view / name
    actual = sha(file.read_bytes()) if file.is_file() else None
    restored_artifacts[name] = {"expected_public_sha256": expected, "actual_sha256": actual,
                                "pinned_original_sha256": row["source_sha256"],
                                "bytes": len(raw), "include_str_resource": name in resource_names,
                                "publication_kind": row.get("publication", {}).get("kind"),
                                "ok": actual == expected}
    if actual != expected:
        errors.append({"kind": "artifact", "path": name, "expected": expected, "actual": actual})
assert resource_names <= set(restored_artifacts)
after = snapshot()
record = {"schema": "h0mework/private-actual-public-source-view-verification@1",
          "actual_head": before["head"], "source_cap": cap,
          "finished_at": datetime.now(timezone.utc).isoformat(),
          "metadata_path": str(metadata_path.relative_to(ROOT)),
          "metadata_sha256": sha(metadata_path.read_bytes()),
          "view_path": str(view.relative_to(ROOT)),
          "input_before": before, "input_after": after, "inputs_unchanged": before == after,
          "source_layout_count": len(sources), "artifact_count": len(restored_artifacts),
          "include_str_resource_count": len(resource_names),
          "source_checks": sources, "artifact_checks": restored_artifacts,
          "errors": errors, "ok": not errors and before == after,
          "source_view": "default public source layout",
          "original_receipt_absolute_paths_replayed": False,
          "scientific_recalculation": False, "Lean_recompiled": False, "public_mutation": False}
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({k: record[k] for k in ("ok", "inputs_unchanged", "source_layout_count",
                                        "artifact_count", "include_str_resource_count")}, ensure_ascii=False))
sys.exit(0 if record["ok"] else 1)
