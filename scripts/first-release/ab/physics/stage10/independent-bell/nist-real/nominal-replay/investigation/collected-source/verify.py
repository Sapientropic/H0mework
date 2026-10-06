"""Run two independent processes after checking the committed criterion; save a compact receipt."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
FREEZE = "40a278fec1"


def freeze_check():
    root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], cwd=HERE, text=True).strip())
    relative = (HERE/"criterion.md").relative_to(root).as_posix()
    commit = subprocess.check_output(["git", "rev-parse", FREEZE], cwd=HERE, text=True).strip()
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=HERE, check=True)
    blob = subprocess.check_output(["git", "show", commit+":"+relative], cwd=HERE)
    if blob != (HERE/"criterion.md").read_bytes():
        raise ValueError("criterion differs from pre-execution commit")
    return {"commit": commit, "sha256": hashlib.sha256(blob).hexdigest()}


def distance(a, b):
    if isinstance(a, dict):
        if a.keys() != b.keys():
            raise ValueError("mismatched object keys")
        return max((distance(a[k], b[k]) for k in a), default=0)
    if isinstance(a, list):
        if len(a) != len(b):
            raise ValueError("mismatched lengths")
        return max((distance(x, y) for x, y in zip(a, b)), default=0)
    if isinstance(a, (int, float)) and not isinstance(a, bool):
        import math
        if not math.isfinite(a) or not math.isfinite(b):
            raise ValueError("nonfinite output")
        return abs(a-b)
    if a != b:
        raise ValueError("mismatched identity")
    return 0


def main():
    freeze = freeze_check()
    # Both producers finish before either result is compared. Neither reads the other's output.
    results = [json.loads(subprocess.check_output([sys.executable, str(HERE/name)], text=True))
               for name in ("model.py", "independent.py")]
    delta = distance(*results)
    from model import frozen, OpticalSource, encode
    spec = frozen()
    if delta > spec["tolerance"] or len(results[0]) != 70:
        raise ValueError("independent forward comparison failed")
    tests = subprocess.run([sys.executable, str(HERE/"tests.py"), "-v"], capture_output=True, text=True)
    print(tests.stderr, end="")
    if tests.returncode:
        raise RuntimeError("controls failed")
    observations = {}
    for recipe in spec["fixtures"]:
        source = OpticalSource(recipe)
        observations[recipe["name"]] = {
            "statistics": encode(source.statistics()),
            "r_half_shape": encode(source.collected_shape(0.5)),
            "balanced_rates": source.rates(1, **spec["rates"]),
            "r_half_rates": source.rates(0.5, **spec["rates"])}
    files = ("criterion.md", "model.py", "independent.py", "verify.py", "tests.py")
    receipt = {"schema": "p23-collected-source-verification/v1", "freeze": freeze,
               "status": "PASS", "classification": "synthetic subordinate single-pair optical source",
               "family_points": 70, "analyzer_pairs_per_point": 25,
               "max_abs_difference": delta, "tolerance": spec["tolerance"],
               "controls_output": tests.stderr, "observations": observations,
               "identity": spec["identity"],
               "sha256": {f: hashlib.sha256((HERE/f).read_bytes()).hexdigest() for f in files}}
    (HERE/"verification.json").write_text(json.dumps(receipt, indent=2, sort_keys=True, allow_nan=False)+"\n")
    print(f"PASS: {len(results[0])} family points, 1750 analyzer pairs, max delta={delta:.3g}")
    print("PASS: frozen criterion, independent full-mode consumer, optical controls")


if __name__ == "__main__":
    main()
