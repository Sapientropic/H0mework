"""Read-only receipt intake; no archive, numerical solver or statistical replay."""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import subprocess

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[5]
FIRST = BASE / "mode-prefix-first-mp0001.json"
ATTEMPT = BASE / "mode-prefix-first-mp0001-attempt.json"
SCHEMA = "stage10-shared-raw-model-joint-evidence/v1"
REQUIRED = {"criterion-mp0001.md", "mode_prefix_run.py", "mode_forward_run.py", "atomic_modes.py",
            "atomic_full_forward.py", "atomic_dipole.py", "raw_command_family.py",
            "interval_prefix.py", "interval_prefix_independent.py", "mode-forward-mi0001.json.gz",
            "hardware-inverse-first-hi0002.json", "primary-first-c0002.json"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def frozen(path, commit="HEAD"):
    raw = path.read_bytes()
    relative = path.relative_to(ROOT).as_posix()
    bound = subprocess.check_output(["git", "-C", str(ROOT), "show", commit + ":" + relative])
    require(raw == bound, "frozen evidence changed: " + relative)
    return raw


def consume(first_path=FIRST):
    raw = frozen(FIRST)
    require(Path(first_path).read_bytes() == raw, "unregistered raw-model receipt")
    first, attempt = json.loads(raw), json.loads(frozen(ATTEMPT))
    require(first.get("schema") == "stage10-raw-hardware-joint-prefix-mp0001/v1" and
            first.get("status") == "all_original_prefixes_scored" and
            first.get("familywise_alpha") == "1/20" and
            first.get("new_confidence_budget_spent") is False and
            first.get("actual_hardware_uniquely_identified") is False and
            first.get("controller_advance") is False, "raw-model first identity/scope")
    commit = first["freeze_commit"]
    require(attempt.get("freeze_commit") == commit and attempt.get("source_bindings") == first["source_bindings"],
            "raw-model attempt binding")
    paths = []
    for entry in first["source_bindings"]:
        relative = Path(entry["path"])
        require(not relative.is_absolute() and ".." not in relative.parts, "evidence path outside source corridor")
        path = ROOT / relative
        require(hashlib.sha256(frozen(path, commit)).hexdigest() == entry["sha256"], "source SHA changed")
        paths.append(path.name)
    require(REQUIRED <= set(paths) and len(paths) == len(set(entry["path"] for entry in first["source_bindings"])),
            "raw-model source inventory")
    old = json.loads(frozen(BASE / "primary-first-c0002.json"))
    with localcontext() as context:
        context.prec = 60
        threshold_lower = Q(Decimal(40).ln().next_minus())
    require(len(first["runs"]) == len(old["runs"]) == 2, "complete two-run inventory")
    summaries = []
    for run, original, name, n in zip(first["runs"], old["runs"], ("2016-04-15", "2016-06-14"), (10201, 10202)):
        require(run.get("run") == original["run"] == name and
                run.get("raw_source_membership_verified") is True and
                run.get("raw_model_joint_witness_verified") is True and
                run.get("all_prefix_intersections_checked") is True, "shared raw-model membership missing")
        a, b = run["primary"], run["independent"]
        for result in (a, b):
            require(result.get("trials") == n and result.get("all_prefixes_checked") is True and
                    result.get("all_prefixes_below_threshold_certified") is True and
                    result.get("first_rejection") is None and result.get("uncertain_prefixes") == [] and
                    Q(result["maximum_log_e"]["upper"]) < threshold_lower and
                    result["trial_bit_sequence_sha256"] == original["trial_bit_sequence_sha256"], "original full-prefix witness invalid")
        require(a["counts"] == b["counts"] and a["pooled_counts"] == b["pooled_counts"] and
                sum(sum(row["counts"]) for row in a["counts"]) == n and
                run["all_original_trial_bits_sha256"] == a["trial_bit_sequence_sha256"], "complete original counts mismatch")
        summaries.append({"run": name, "trials": n, "maximum_log_e": a["maximum_log_e"]})
    return {"schema": SCHEMA, "evidence_valid": True,
            "status": "shared_raw_model_joint_member_verified",
            "shared_raw_model_joint_member_verified": True,
            "raw_programme_and_independent_residual_consumed": True,
            "all_original_prefixes_double_checked": True, "trials": 20403, "runs": summaries,
            "familywise_alpha": "1/20", "new_confidence_budget_spent": False,
            "actual_hardware_uniquely_identified": False, "actual_clock_programme_identified": False,
            "controller_advance": False, "archive_files_read_at_intake": 0,
            "new_numerical_solves_at_intake": 0, "new_statistical_executions_at_intake": 0,
            "first_sha256": hashlib.sha256(raw).hexdigest(), "science_freeze": commit}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true", required=True)
    parser.add_argument("--first", type=Path, default=FIRST)
    args = parser.parse_args()
    print(json.dumps(consume(args.first), sort_keys=True))
