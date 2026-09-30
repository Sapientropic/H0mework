"""Focused CountedObservation build, source audit and original consumer controls."""

import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2] / "Lean"
STEM = Path("SaturationMonoid/NoIslandNoMagic/CanonicalArithmeticState/ParticleWave/Fock/Runtime/SourceHistory")
NAMES = "Array Entry Action Representation Table Simulation Runtime Consumer Value Source Continuation Conditional Mixture Field Complete Material".split()
OWNED = [STEM / "Conditional/CountedObservation" / f"{name}.lean" for name in NAMES]
OWNED[-1:-1] = [STEM / "Conditional/CountedRecovery" / f"{name}.lean" for name in ["Energy", "Table", "Field"]]
OWNED[-1:-1] = [STEM / "Conditional/CountedPosterior" / f"{name}.lean" for name in
                ["Margin", "Restore", "Coordinate", "Source", "Continuation", "Field", "Consumer"]]
OWNED[-1:-1] = [STEM / "Conditional/CountedAdvance" / f"{name}.lean" for name in
                ["State", "Continuation", "Model", "ModelContinuation", "Field", "Consumer"]]
OWNED[-1:-1] = [STEM / "Conditional/CountedMerge" / f"{name}.lean" for name in
                ["Table", "Representation", "Action", "Margin", "Source", "Field", "Consumer"]]
OWNED += [STEM / "Conditional/NativeKeys/Material.lean"]
CONSUMERS = [STEM / f"{name}.lean" for name in (
    "Copy/Graph/NativeModelStep/Calculation", "Copy/Graph/NativeModelStep/Observation",
    "Copy/Observation/Consumer", "Copy/Graph/Consumer",
)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="Refresh the owned and direct consumer modules first.")
    parser.add_argument("--library", type=Path, help="Prepend an isolated library to LEAN_PATH.")
    parser.add_argument("--source-root", type=Path, default=ROOT,
                        help="Source tree for an isolated build or audit; defaults to Lean/.")
    parser.add_argument("--output", type=Path, help="Audit artifacts; defaults to a fresh temporary directory.")
    args = parser.parse_args()
    args.source_root = args.source_root.resolve()
    if args.library:
        args.library = args.library.resolve()
    output = args.output or Path(tempfile.mkdtemp(prefix="counted-observation-audit-"))
    output.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["COUNTED_AUDIT_DIR"] = str(output.resolve())
    leanpath = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    if args.library:
        env["LEAN_PATH"] = str(args.library.resolve()) + os.pathsep + leanpath
    else:
        env["LEAN_PATH"] = leanpath
    banned = re.compile(r"\b(sorry|admit|native_decide|unsafe|partial)\b|set_option\s+(maxHeartbeats|maxRecDepth)|^import\s+scratch\.", re.M)
    for relative in OWNED:
        if banned.search((args.source_root / relative).read_text()):
            raise RuntimeError(f"untrusted source construct: {relative}")

    def run(label, extra):
        with (output / f"{label}.log").open("w") as log:
            result = subprocess.run(["lake", "env", "env", "LEAN_PATH=" + env["LEAN_PATH"],
                                     "lean", "--trust=0", "-DwarningAsError=true", *extra],
                                    cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, text=True)
        if result.returncode:
            print((output / f"{label}.log").read_text())
            raise SystemExit(result.returncode)
        print(f"PASS {label}", flush=True)

    if args.build:
        for index, relative in enumerate(OWNED + CONSUMERS):
            target = (args.library or ROOT / ".lake/build/lib/lean") / relative.with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            run(f"build-{index:02d}", ["-R", str(args.source_root), "-o", str(target), str(args.source_root / relative)])
    for name in ["Gate", "Controls", "Reachability", "Execution", "RecoveryControls", "RecoveryExecution", "PosteriorExecution", "AdvanceExecution", "MergeExecution"]:
        run(name, [str(HERE / f"{name}.lean")])
    print((output / "Gate.log").read_text().strip())
    print((output / "Execution.log").read_text().strip())
    print((output / "RecoveryExecution.log").read_text().strip())
    print((output / "PosteriorExecution.log").read_text().strip())
    print((output / "AdvanceExecution.log").read_text().strip())
    print((output / "MergeExecution.log").read_text().strip())
    print(f"Artifacts: {output}")


if __name__ == "__main__":
    main()
