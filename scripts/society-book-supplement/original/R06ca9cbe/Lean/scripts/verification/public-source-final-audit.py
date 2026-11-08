"""Replay accepted public-source evidence without repeating the actual computation."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


def main() -> None:
    root = Path(__file__).resolve().parents[3]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-root", type=Path,
                        default=root / ".agents/tmp/public-autonomous-origin-20261101")
    parser.add_argument("--check-main", action="store_true")
    args = parser.parse_args()
    evidence = args.evidence_root.absolute()
    accepted = json.loads((root / "Lean/docs/audits/public-source-final-acceptance.json").read_text())

    def digest(path: Path) -> str:
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def load(path: Path):
        return json.loads(path.read_text())

    def require(condition: bool, message: str) -> None:
        if not condition:
            raise RuntimeError(message)

    for path, wanted in accepted["evidence"].items():
        require(digest(evidence / path) == wanted, f"evidence changed: {path}")
    for path, wanted in accepted["sources"].items():
        require(digest(root / path) == wanted, f"accepted source changed: {path}")

    for route in accepted["actual_routes"]:
        box = evidence / route
        actual = load(box / "actual-run.json")
        require(actual["exit"] == 0 and actual["actual_cases"] == 12,
                f"actual call not accepted: {route}")
        require(actual["output"] == (box / "actual-run.log").read_text(),
                f"actual output differs: {route}")
        require(actual["output"].count("\nPASS ") == 12
                and "DEFAULT ACTUAL CONTINUATION CONSUMER PASS: 12/12" in actual["output"]
                and "DEFAULT RETURN rounds=2 sourceWords=1 bases=2 pending=4" in actual["output"]
                and "FAIL " not in actual["output"] and "PANIC" not in actual["output"],
                f"incomplete actual output: {route}")
        subprocess.run([sys.executable, str(box / "verify_actual.py")], cwd=root, check=True)
        require(load(box / "finish-status.json")["exit"] == 0,
                f"production finish not accepted: {route}")
    print("ORIGINAL LITERAL RECEIPTS PASS: 7 routes; each actual two-round 12/12; no actual call repeated", flush=True)

    adopted = evidence / accepted["adopted_route"]
    for verifier in [adopted / "verify_installed.py", adopted / "verify_linkage.py",
                     evidence / "final-audit/verify.py"]:
        subprocess.run([sys.executable, str(verifier)], cwd=root, check=True)

    continuation = evidence / "continuation"
    strict = load(continuation / "strict.json")
    require(strict["exit"] == 0 and digest(root / strict["source"]) == strict["source_sha256"],
            "continuation strict source differs")
    artifact = continuation / "lib" / Path(strict["source"]).relative_to("Lean").with_suffix(".olean")
    require(digest(artifact) == strict["artifact_sha256"], "continuation artifact differs")
    for name, marker in [("contract", "PUBLIC UNBOUNDED CONTINUATION CONTRACT PASS: 17/17"),
                         ("kernel", "PUBLIC UNBOUNDED CONTINUATION KERNEL PASS:")]:
        record = load(continuation / (name + ".json"))
        require(record["exit"] == 0 and marker in record["output"]
                and record["output"] == (continuation / (name + ".log")).read_text()
                and digest(root / record["source"]) == record["source_sha256"],
                f"continuation {name} differs")
    axioms = re.search(r"axioms=\[([^]]*)\]", load(continuation / "kernel.json")["output"])
    require(axioms is not None and {item.strip() for item in axioms[1].split(",")}
            == {"propext", "Classical.choice", "Quot.sound"}, "unexpected continuation axioms")
    print("UNBOUNDED CONTINUATION PASS: 17 contracts; exact segments; reviewed typed outcomes; fresh empty-kernel replay", flush=True)

    retired = load(evidence / "execution-frame/disposition.json")
    require(retired["disposition"] == "not_adopted"
            and not retired["production_installed"] and not retired["actual_execution_started"],
            "unaccepted execution candidate was promoted")

    if args.check_main:
        for parent in accepted["provenance_parents"]:
            subprocess.run(["git", "merge-base", "--is-ancestor", parent, "refs/heads/main"],
                           cwd=root, check=True)
        for path, wanted in accepted["sources"].items():
            content = subprocess.check_output(["git", "show", "refs/heads/main:" + path], cwd=root)
            require(hashlib.sha256(content).hexdigest() == wanted, f"main source differs: {path}")
        print("MAIN INTEGRATION PASS: accepted source closure and scientific provenance retained", flush=True)
    print("PUBLIC SOURCE ORIGINAL SIX CONTRACTS PASS", flush=True)


if __name__ == "__main__":
    main()
