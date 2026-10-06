"""Validate the public source-member receipt without admitting an actual apparatus."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
SCHEMA = "p23-public-observable-verification/v1"
VERSION = "p23-public-observables-po0003"
IDENTITY = ("source_mapping_identified","publication_configuration_identified","production_admitted")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(directory, name):
    return json.loads((directory/name).read_text())


def committed(path):
    relative = path.relative_to(ROOT).as_posix()
    commit = subprocess.check_output(["git","log","-1","--format=%H","--",relative],cwd=ROOT,text=True).strip()
    require(bool(commit),"source_not_committed:"+relative)
    require(subprocess.check_output(["git","show",commit+":"+relative],cwd=ROOT) == path.read_bytes(),
            "source_modified_after_freeze:"+relative)
    return commit


def interval(row):
    lo,hi = F(row["exact_lower"]),F(row["exact_upper"])
    require(lo <= hi,"reversed_exact_probability_interval")
    require(row["lower"] == float(lo) and row["upper"] == float(hi),"floating_interval_disagrees_with_exact_endpoints")
    return lo,hi


def assess(report_dir=None, *, enabled=True):
    base = {"schema":SCHEMA,"version":VERSION,"evidence_valid":False,
            **{k:False for k in IDENTITY},"private_optimizer_input_required":False}
    if not enabled:
        return {**base,"status":"disabled_by_override"}
    directory = HERE if report_dir is None else Path(report_dir)
    try:
        names = ("public-criterion.md","public-criterion-po0002.md","public-criterion-po0003.md",
                 "public-observables.json","public_compare.py","public_compare_po0002.py","public_compare_po0003.py",
                 "predict.py","public-witness-check.py","public_verify.py")
        commits = {name:committed(HERE/name) for name in names}
        report = read(directory,"public-comparison-po0003.json")
        require(report["schema"] == "p23-public-observable-comparison/v3" and report["version"] == VERSION,
                "wrong_public_source_family_scope")
        require(all(report[k] is False for k in IDENTITY) and report["private_optimizer_input_required"] is False,
                "compatibility_does_not_identify_source_or_optimum")
        require(report["retrospective"] is True and report["multipaired_window_qualified"] is False,
                "incorrect_public_data_qualification")
        require(report["held_out_count_access_in_member_construction"] is False
                and report["whole_held_out_row_change_leaves_training_identical"] is True
                and report["training_rows"] == [0,1,3] and report["held_out_row"] == 2,
                "whole_cell_holdout_not_preserved")
        require(report["features_evaluated"] == 12 and report["features_in_global_union"] == 16
                and F(report["alpha"]) == F(1,20),"public_confidence_contract_mismatch")
        hashes = {"criterion_sha256":"public-criterion-po0003.md","statistical_criterion_sha256":"public-criterion.md",
                  "source_criterion_sha256":"public-criterion-po0002.md","target_sha256":"public-observables.json",
                  "program_sha256":"public_compare_po0003.py","parent_program_sha256":"public_compare.py",
                  "member_program_sha256":"public_compare_po0002.py","observable_predictor_sha256":"predict.py"}
        for key,name in hashes.items():
            require(report[key] == digest(HERE/name),"public_source_binding_mismatch:"+name)
        require(report["interval_source_sha256"] == digest(HERE.parent/"response/response.py"),"interval_source_binding_mismatch")
        fresh = subprocess.run([sys.executable,str(HERE/"public_compare_po0003.py"),"--check-only"],
                               capture_output=True,text=True,timeout=30)
        require(fresh.returncode == 0 and json.loads(fresh.stdout) == report,"public_receipt_recomputation_mismatch")
        target = read(HERE,"public-observables.json")
        require(report["complete_trials"] == sum(sum(row) for row in target["counts"]),"complete_trial_denominator_mismatch")
        confidence = report["common_mean_confidence"]
        require([b["model"] for b in report["branches"]] == ["S1_signal","independent_OR","named_M3"],"postselected_rate_model")
        outcomes = {}
        for branch in report["branches"]:
            require(branch["outcome"] == "EXHIBITED_COMPATIBLE_MEMBER" and all(v is True for v in branch["checks"].values()),
                    "missing_legal_source_member:"+branch["model"])
            values = {k:F(v) for k,v in branch["projected_statistics"].items()}
            require(values["H"] >= 0 and values["V"] >= 0 and values["X"]**2 <= values["H"]*values["V"],"illegal_source_Gram")
            for name in ("j","sA_cell","sB_cell"):
                require(len(branch["forward_probability_enclosures"][name]) == len(confidence[name]) == 4,
                        "incomplete_probability_cell_set")
                for p,c in zip(branch["forward_probability_enclosures"][name],confidence[name]):
                    pl,pu = interval(p)
                    cl,cu = interval(c)
                    require(cl <= pl <= pu <= cu,"mathematical_envelope_not_contained")
                require(branch["confidence_inclusion"][name] == [True]*4 and branch["actual_forward_inside_enclosure"][name] == [True]*4,
                        "incorrect_membership_verdict")
            outcomes[branch["model"]] = branch["outcome"]
        witness = read(directory,"public-witness-verification.json")
        require(witness["schema"] == "p23-public-witness-independent/v1" and witness["passed"] is True
                and witness["input_version"] == VERSION,
                "independent_full_mode_witness_not_verified")
        require(witness["report_sha256"] == digest(directory/"public-comparison-po0003.json")
                and witness["executable_freeze"]["sha256"] == digest(HERE/"public-witness-check.py"),"independent_witness_binding_mismatch")
        require(all(witness[k] is False for k in IDENTITY),"independent_witness_cannot_identify_actual_source")
        require([b["model"] for b in witness["branches"]] == ["S1_signal","independent_OR","named_M3"],
                "independent_witness_model_selection")
        require(all(b["independent_forward_validation_passed"] is True and b["exact_interval_membership_certified"] is True
                    and b["floating_point_membership_check"] is True for b in witness["branches"]),
                "independent_source_or_membership_check_failed")
        # The optical theorem and synthetic independent replay are separate prerequisites.
        law = subprocess.run([sys.executable,str(HERE/"verify.py"),"--directory",str(directory),"--check-only"],
                             capture_output=True,text=True,timeout=60)
        optical = json.loads(law.stdout)
        require(law.returncode == 0 and optical["schema"] == "p23-observable-prediction-verification/v1"
                and optical["status"] == "verified", "source_observable_producer_not_verified")
        bindings = {**optical["bindings"],**{(HERE/name).relative_to(ROOT).as_posix():digest(HERE/name) for name in names}}
        for name in ("public-comparison-po0003.json","public-witness-verification.json"):
            bindings[(HERE/name).relative_to(ROOT).as_posix()] = digest(directory/name)
        return {**base,"status":"verified","evidence_valid":True,"models":outcomes,
                "complete_trials":report["complete_trials"],"features_evaluated":12,"alpha":report["alpha"],
                "whole_cell_held_out":True,"retrospective":True,"multipaired_window_qualified":False,
                "nominal_optimum_verified":False,"statistical_scope":{"S1_signal":"common_mean_source_with_memory",
                "independent_OR":"common_mean_source_with_memory","named_M3":"stationary_named_M3"},
                "source_freezes":commits,"bindings":bindings}
    except (OSError,ValueError,KeyError,TypeError,subprocess.SubprocessError) as error:
        return {**base,"status":"invalid_public_observable_evidence","reason":str(error)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory",type=Path)
    parser.add_argument("--check-only",action="store_true")
    args = parser.parse_args()
    result = assess(args.directory)
    print(json.dumps(result,indent=2,sort_keys=True,allow_nan=False))
    return 0 if result["status"] == "verified" else 1


if __name__ == "__main__":
    sys.exit(main())
