#!/usr/bin/env python3
"""Strict focused replay of the source-selected light kernel and its characteristics."""
import json
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
LEAN = ROOT / "Lean"
FILES = ["Graph", "Jet", "Source", "Scaling", "Characteristic", "Metric"]
PREFIX = "SaturationMonoid.PhysicsCore.LowEnergy.LightKernel."


def main():
    logs = HERE / "logs"
    logs.mkdir(exist_ok=True)
    output_dir = LEAN / ".lake/build/lib/lean/SaturationMonoid/PhysicsCore/LowEnergy/LightKernel"
    output_dir.mkdir(parents=True, exist_ok=True)
    declarations = []
    for name in FILES:
        source = (LEAN / "SaturationMonoid/PhysicsCore/LowEnergy/LightKernel" / f"{name}.lean").read_text()
        declarations += re.findall(r"^(?:theorem|def|abbrev) ([\w.]+)", source, re.M)
    audit = HERE / "Audit.lean"
    audit.write_text("import SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.Graph\nimport SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.Jet\nimport SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.Characteristic\nimport SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.Metric\n\n" +
        "\n".join(f"#print axioms {PREFIX}{name}" for name in declarations) + "\n")
    entries = [(name, f"SaturationMonoid/PhysicsCore/LowEnergy/LightKernel/{name}.lean") for name in FILES]
    entries += [("Consumer", str(HERE / "Consumer.lean")), ("Audit", str(audit))]
    records = []
    for name, path in entries:
        command = ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true"]
        if name in FILES:
            command += ["-o", str(output_dir / f"{name}.olean")]
        command.append(path)
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
    status = {"scope": "SOURCE_TRUE_LIGHT5_KERNEL_AND_PROPAGATION_CHARACTERISTICS",
        "passed": passed, "trust": 0, "warningAsError": True, "default_limits": True,
        "public_declarations": len(declarations), "direct_consumers": 7,
        "axioms": sorted(axioms), "records": records}
    (HERE/"focused.json").write_text(json.dumps(status, indent=2)+"\n")
    raise SystemExit(not passed)


if __name__ == "__main__":
    main()
