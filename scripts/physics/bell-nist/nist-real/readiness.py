"""Fail-closed theory-readiness assessment; no dataset paths or data-reader API."""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(HERE.parent))
import real_family as rf
from checks import control_loop

PRODUCTION = "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/RealFamily.lean"
CERTIFICATION = "Lean/docs/audits/physics/stage10-bell/RealFamilyCertification.lean"
REGISTRY_KEYS = {"preparation", "angles_and_pulses", "eta", "assignment", "background",
                 "pair_probability", "visibility", "model_tv", "epoch_and_drift",
                 "trial_format", "joint_coverage", "nominal_optimum"}
GEOMETRY_KEYS = ("matrix_matches_all_cells", "mirror_geometry", "real_shape",
                 "rare_vertical_transmission", "primed_destructive_structure",
                 "wrong_basis_rejected", "wrong_bob_sign_rejected")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_lean():
    path = HERE / "evidence/lean-certification.json"
    initial = {p: digest(ROOT / p) for p in (PRODUCTION, CERTIFICATION)}
    path.write_text(json.dumps({"status": "running", "source_sha256": initial}) + "\n")
    commands = [
        ["lake", "build", "SaturationMonoid.PhysicsCore.Stage10.Bell.RealFamily"],
        ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true", PRODUCTION[5:]],
        ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true", CERTIFICATION[5:]],
    ]
    results = []
    for command in commands:
        start = time.monotonic()
        try:
            run = subprocess.run(command, cwd=ROOT / "Lean", text=True,
                                 capture_output=True, timeout=180)
            results.append({"command": command, "returncode": run.returncode,
                            "seconds": round(time.monotonic()-start, 3),
                            "output": (run.stdout+run.stderr)[-6000:]})
        except subprocess.TimeoutExpired:
            results.append({"command": command, "returncode": -1, "output": "timeout"})
        if results[-1]["returncode"] != 0:
            break
    unchanged = initial == {p: digest(ROOT / p) for p in initial}
    passed = unchanged and len(results) == 3 and all(r["returncode"] == 0 for r in results)
    path.write_text(json.dumps({"status": "passed" if passed else "failed",
                               "source_sha256": initial, "commands": results}, indent=2)+"\n")

def assess():
    instrument = json.loads((HERE / "instrument.json").read_text())
    request = json.loads((HERE / "request.json").read_text())
    registry = json.loads((HERE / "calibration-registry.json").read_text())["entries"]
    proof_path = HERE / "evidence/lean-certification.json"
    proof = json.loads(proof_path.read_text()) if proof_path.exists() else {}
    expected = {p: digest(ROOT / p) for p in (PRODUCTION, CERTIFICATION)}
    commands = proof.get("commands", [])
    proof_ok = (proof.get("status") == "passed" and proof.get("source_sha256") == expected
                and len(commands) == 3 and all(c.get("returncode") == 0 for c in commands)
                and "REAL_FAMILY_CERTIFIED" in commands[-1].get("output", ""))
    tests = subprocess.run([sys.executable, str(HERE / "test_real_family.py"), "-v"],
                           text=True, capture_output=True, timeout=60)
    loop = control_loop(instrument)
    registered = set(registry) == REGISTRY_KEYS and all(
        row.get("responsible_role") and row.get("required_evidence") for row in registry.values())
    budget = rf.error_budget(request["error_budget"])
    protocol = all((HERE / name).is_file() for name in
                   ("protocol.md", "controller-capsule.md", "access-record.md"))
    components = {"lean_family_and_certification": proof_ok,
                  "predictor_and_synthetic_regressions": tests.returncode == 0,
                  "nominal_control_geometry": all(loop[k] for k in GEOMETRY_KEYS),
                  "no_click_and_calibration_responsibilities": bool(registered),
                  "protocol_and_budget_draft": protocol,
                  "nominal_apparatus_optimum": loop["apparatus_optimum_verified"]}
    return {"schema": "nist-real-readiness/v1", "components": components,
            "r0003_nist_ready": all(components.values()),
            "status": "ready" if all(components.values()) else "blocked_at_nominal_optimum_gate"}


def main():
    parser = argparse.ArgumentParser(
        description="Fail-closed theory-readiness assessment; exit 1 unless fully ready.")
    parser.add_argument("--reuse-lean-receipt", action="store_true",
                        help="skip fresh Lean verification and reuse evidence/lean-certification.json")
    args = parser.parse_args()
    if not args.reuse_lean_receipt:
        verify_lean()
    result = assess()
    (HERE / "evidence").mkdir(exist_ok=True)
    (HERE / "evidence/readiness.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result["r0003_nist_ready"] else 1


if __name__ == "__main__":
    sys.exit(main())
