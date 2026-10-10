from pathlib import Path
from datetime import datetime, timezone
import copy
import hashlib
import json
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "tools"))
import source_view as sv


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    freeze_path = ROOT / ".local/acceptance-execution-20261010/cohort-freeze.json"
    freeze_raw = freeze_path.read_bytes()
    freeze = json.loads(freeze_raw)
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip() == freeze["head"]
    assert {p: sha((ROOT / p).read_bytes()) for p in freeze["files"]} == freeze["files"]
    exported, _, _, inverse = sv.load_map()
    index = {r["path"]: r for r in exported["modules"]}
    old_plan = json.loads((ROOT / ".local/mixed-spectator-instance-fix/plan.json").read_bytes())
    candidate_dir = BASE / "candidate-sources"
    candidate_dir.mkdir(exist_ok=True)
    prefix = "Lean/H0mework/Versions/R9c73a630/ReleaseMaterials/Scratch/LowEnergyRetardedCouncil/NamedColorQtNext/Charge/"
    records = []
    retained_r71e = []
    with tempfile.TemporaryDirectory(prefix="module-view-inverse-", dir=BASE) as temporary:
        shadow = Path(temporary)
        for old in old_plan["records"]:
            stem = Path(old["path"]).stem
            path = prefix + stem + ".lean"
            if stem in ("MixedSpectatorYukawaColumn", "MixedSpectatorYukawaMatrix"):
                assert path not in index
                prior = index[old["path"]]
                assert prior["local_instance_names"] == old["local_instance_names"]
                assert sha((ROOT / old["path"]).read_bytes()) == prior["target_sha256"]
                retained_r71e.append({"path": old["path"], "target_sha256": prior["target_sha256"],
                                      "source_sha256": prior["source_sha256"],
                                      "local_instance_names": prior["local_instance_names"]})
                continue
            row = index[path]
            assert row["source_revision"] == "9c73a630ce05bea062ec889b188f5105c0afb796"
            assert row["source_sha256"] == old["source_sha256"]
            assert not row.get("local_instance_names")
            view, original = sv.module_views(row, inverse)
            raw = (ROOT / path).read_bytes()
            assert sha(raw) == row["target_sha256"]
            rules = [{"source_declaration": rule["source_declaration"],
                      "target_name": "h0R9c73a630" + stem + "Local" + str(i)}
                     for i, rule in enumerate(old["local_instance_names"], 1)]
            candidate = sv.name_local_instances(raw.decode(), rules).encode()
            assert sv.name_local_instances(candidate.decode(), rules, reverse=True).encode() == raw
            assert sv.import_tokens(raw.decode()) == sv.import_tokens(candidate.decode())
            options = lambda text: re.findall(r"(?m)^set_option[^\n]*", text)
            assert options(raw.decode()) == options(candidate.decode())
            candidate_path = candidate_dir / (stem + ".lean")
            candidate_path.write_bytes(candidate)
            derived = copy.deepcopy(row)
            derived["local_instance_names"] = rules
            derived["target_sha256"] = sha(candidate)
            shadow_path = shadow / path
            shadow_path.parent.mkdir(parents=True, exist_ok=True)
            shadow_path.write_bytes(candidate)
            sv.ROOT = shadow
            assert sv.module_views(derived, inverse) == (view, original)
            sv.ROOT = ROOT
            records.append({"path": path, "target": row["target"], "source_path": row["source_path"],
                            "source_revision": row["source_revision"],
                            "source_revisions": row.get("source_revisions", [row["source_revision"]]),
                            "source_sha256": row["source_sha256"], "source_origin": row.get("source_origin"),
                            "before_public_sha256": row["target_sha256"],
                            "candidate_public_sha256": sha(candidate), "view_sha256": sha(view),
                            "candidate_path": candidate_path.relative_to(ROOT).as_posix(),
                            "local_instance_names": rules, "imports_unchanged": True,
                            "options_unchanged": True, "public_bytes_exact_inverse": True,
                            "original_source_exact_inverse": True, "proof_value_bodies_unchanged": True,
                            "same_original_source_as_paid_r71e": old["path"]})
    assert len(records) == 9 and sum(len(r["local_instance_names"]) for r in records) == 11
    selected = json.loads((BASE.parent / "physics-runtime-overlap-plan-c762e780.json").read_bytes())
    selected_files = next(p["source_files"] for p in selected["packages"] if p["id"] == "v2-9c73-charged-transfer")
    family_paths = {r["path"] for r in records}
    noncolliding = []
    for path in selected_files:
        if not path.startswith(prefix):
            continue
        text = (ROOT / path).read_text()
        declarations = re.findall(r"(?m)^local instance[^\n]*", text)
        if not declarations:
            continue
        namespaces = re.findall(r"(?m)^namespace[^\n]*", text)
        if namespaces == ["namespace LowEnergy.MixedSpectatorCandidate"]:
            assert path in family_paths, path
        else:
            assert path not in family_paths and len(namespaces) == 1
            noncolliding.append({"path": path, "namespace": namespaces[0], "declarations": declarations,
                                 "target_sha256": sha((ROOT / path).read_bytes())})
    assert len(noncolliding) == 6 and len({p["namespace"] for p in noncolliding}) == 6
    assert freeze_path.read_bytes() == freeze_raw
    assert {p: sha((ROOT / p).read_bytes()) for p in freeze["files"]} == freeze["files"]
    out = {"schema": "h0mework/private-new9-mixed-spectator-local-instance-plan@1", "formal_acceptance": False,
           "observed_at": datetime.now(timezone.utc).isoformat(), "head": freeze["head"],
           "cohort_freeze_sha256": sha(freeze_raw), "rows": records, "local_instance_rules": 11,
           "retained_already_named_r71e_yukawa": retained_r71e,
           "retained_distinct_namespace_locals": noncolliding,
           "actual_failure_log": ".local/physics-acceptance-20261010/new9-charged-forcing-build-c762e780/build.log",
           "api": "tools/source_view.py:name_local_instances",
           "source_view_sha256": sha((ROOT / "tools/source_view.py").read_bytes()),
           "scope": "Exact same original source bytes as paid R71e instance family. Only explicit local instance names change; original types, values, mathematical declarations, proof bodies and options remain."}
    path = BASE / "plan.json"
    path.write_text(json.dumps(out, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"plan": path.relative_to(ROOT).as_posix(), "rows": len(records),
                      "rules": out["local_instance_rules"], "exact_inverse_all": True,
                      "head": freeze["head"]}), flush=True)


if __name__ == "__main__":
    main()
