#!/usr/bin/env python3
"""Strict replay of the source boson Schur, elimination order and low-momentum inverse remainder."""
import json
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
LEAN = ROOT / "Lean"
FILES = ["Schur", "Order", "Taylor", "Analytic", "Readback", "Metric"]
PREFIX = "SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective."


def main():
    logs = HERE / "logs"
    logs.mkdir(exist_ok=True)
    (LEAN / ".lake/build/lib/lean/SaturationMonoid/PhysicsCore/LowEnergy/BosonEffective").mkdir(parents=True, exist_ok=True)
    declarations = []
    for name in FILES:
        source = (LEAN / "SaturationMonoid/PhysicsCore/LowEnergy/BosonEffective" / f"{name}.lean").read_text()
        declarations.extend(("Metric." if name=="Metric" else "")+decl for decl in re.findall(r"^(?:theorem|def|abbrev) ([\w.]+)", source, re.M))
    audit = HERE / "Audit.lean"
    audit.write_text("import SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Order\nimport SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Analytic\nimport SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Readback\nimport SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric\n\n" +
        "\n".join(f"#print axioms {PREFIX}{name}" for name in declarations) + "\n")
    entries = [(name, f"SaturationMonoid/PhysicsCore/LowEnergy/BosonEffective/{name}.lean") for name in FILES]
    entries += [("Consumer", str(HERE / "Consumer.lean")), ("Audit", str(audit))]
    records = []
    for name, path in entries:
        command = ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true"]
        if name in FILES:
            command += ["-o", f".lake/build/lib/lean/SaturationMonoid/PhysicsCore/LowEnergy/BosonEffective/{name}.olean"]
        command += [path]
        started = time.monotonic()
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, timeout=120)
        output = result.stdout + result.stderr
        (logs / f"{name}.log").write_text(output)
        record = {"name": name, "exit_code": result.returncode,
            "seconds": round(time.monotonic()-started, 3), "command": command}
        records.append(record)
        print(json.dumps(record), flush=True)
        if result.returncode:
            print(output, flush=True)
            break
    passed = len(records)==len(entries) and all(record["exit_code"]==0 for record in records)
    axioms = set()
    if passed:
        output = (logs/"Audit.log").read_text()+(logs/"Consumer.log").read_text()
        for block in re.findall(r"depends on axioms: \[([^]]*)\]", output, re.S):
            axioms.update(word.strip() for word in block.split(",") if word.strip())
        assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms
    status = {"scope": "ORIGINAL55_BOSON_SCHUR_AND_LIGHT6_HEAVY42_LOW_MOMENTUM_KERNEL",
        "passed": passed, "trust": 0, "warningAsError": True, "default_limits": True,
        "public_declarations": len(declarations), "direct_consumers": 7,
        "axioms": sorted(axioms), "records": records}
    (HERE/"focused.json").write_text(json.dumps(status, indent=2)+"\n")
    raise SystemExit(not passed)


if __name__ == "__main__":
    main()
