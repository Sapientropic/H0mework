#!/usr/bin/env python3
"""Source-generated null threshold consumes original public prefix statistics."""
from fractions import Fraction as F
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6]
VERSION="p23-original-public-source-review-pr0001"
SCHEMA="p23-original-public-source-review/v1"


def require(value,reason):
    if not value:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frozen(path):
    rel=Path(path).resolve().relative_to(ROOT).as_posix()
    commit=subprocess.check_output(["git","log","-1","--format=%H","--",rel],cwd=ROOT,text=True).strip()
    require(commit and subprocess.check_output(["git","show",commit+":"+rel],cwd=ROOT)==Path(path).read_bytes(),"unfrozen_original_source_review:"+rel)
    return {"path":rel,"commit":commit,"sha256":digest(path)}


def config():
    text=(HERE/"criterion-original-source-review.md").read_text()
    matches=re.findall(r"<!-- ORIGINAL-SOURCE-REVIEW-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- ORIGINAL-SOURCE-REVIEW-FROZEN-END -->",text,re.S)
    require(len(matches)==1,"nonunique_original_source_review")
    c=json.loads(matches[0]);m=json.loads((HERE/"sources-original-source-review.json").read_text())
    require(c["version"]==m["version"]==VERSION and c["alpha"]=="1/20" and
            c["original_setting_epsilon"]=="3/1000" and c["target_run"]=="XOR3" and c["target_pulse_count"]==5 and
            c["family_sizes"]=={"single":1,"main_four_windows":4,"six_declared_runs_four_windows":24,"qualified_all_run_mask_cap":196602} and
            c["one_training_selected_cut_per_candidate_required"] is True and c["test_selected_cut_allowed"] is False,
            "changed_original_statistical_contract")
    for row in m["inputs"]:
        require(digest(ROOT/row["path"])==row["sha256"],"original_source_binding_changed:"+row["path"])
    bindings=[frozen(HERE/name) for name in ("criterion-original-source-review.md","sources-original-source-review.json","prefix_review.py")]
    return c,bindings


def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec);sys.modules[name]=result;spec.loader.exec_module(result)
    return result


def prefix_identity(observations,data,c):
    require(observations["schema"]=="p23-public-observable-input/v1" and
            observations["row_order"]==["ab","ab_prime","a_prime_b","a_prime_b_prime"] and
            observations["outcome_order"]==["++","+0","0+","00"] and
            observations["source"]["aggregate_pulses"]==[4,5,6,7,8] and
            observations["source"]["dataset"]=="Classical XOR3" and observations["source"]["table"]=="S-II",
            "wrong_original_prefix_source_or_semantics")
    counts=observations["counts"]
    require(len(counts)==4 and all(len(row)==4 for row in counts) and
            all(type(k) is int and k>=0 for row in counts for k in row),"incomplete_original_prefix_counts")
    W=counts[0][0];L=counts[1][1]+counts[2][2]+counts[3][0];N=sum(map(sum,counts))
    target=next(r for r in data["runs"] if r["name"]==c["target_run"])
    index=data["pulse_counts"].index(c["target_pulse_count"])
    require(W==target["NS"][index]==c["prefix_NS"] and
            W+L==target["Nchi"][index]==c["prefix_Nchi"] and
            N==data["main_Table_I"]["prefix_complete_trials"][index]==c["prefix_complete_trials"],
            "original_complete_prefix_does_not_match_published_sufficient_statistics")
    return {"wins":W,"losses":L,"NS":W,"Nchi":W+L,"complete_trials":N,"setting_trial_totals":[sum(row) for row in counts],
            "all_sixteen_outcomes_retained":True,"old_prefix_full_run_substitution":False,"identity_exact":True}


def arithmetic_review(report,identity,c):
    require(report["schema"]=="p23-published-statistics-audit/v1" and report["evidence_valid"] is True,"invalid_original_p_arithmetic")
    main=[r for r in report["printed_checks"] if r["table"]=="main_I"]
    require(len(main)==8 and all(r["outcome"]=="PRINTED_PRECISION_COMPATIBLE" for r in main),"original_main_printed_p_not_certified")
    row=next(r for r in main if r["pulse_count"]==c["target_pulse_count"] and F(r["epsilon"])==F(c["original_setting_epsilon"]))
    require(row["NS"]==identity["NS"] and row["Nchi"]==identity["Nchi"],"arithmetic_tail_is_foreign_prefix")
    tail=report["tail_receipts"][row["tail_key"]]
    lo,hi=F(tail["interval"]["exact_lower"]),F(tail["interval"]["exact_upper"])
    require(0<=lo<=hi<=1 and tail["proof"]["n"]==identity["Nchi"] and tail["proof"]["h"]==identity["NS"] and
            F(tail["proof"]["q"])==F(1006009,2000018),"wrong_original_epsilon_or_success_threshold")
    bounds={name:{"candidate_count":count,"exact_p_upper":str(min(F(1),count*hi)),
                  "rejects_at_original_alpha":count*hi<F(c["alpha"])} for name,count in c["family_sizes"].items()}
    differences=[r for r in report["printed_checks"] if r["outcome"]=="CERTIFIED_PRINTED_TAIL_DISCREPANCY"]
    return {"original_tail_interval":tail["interval"],"original_printed_p":row["printed"],"original_q0":tail["proof"]["q"],
            "selection_scope_bounds":bounds,"main_eight_printed_p_values_certified":True,"SI_printed_precision_discrepancies":differences}


def kernel_review(certificate=None):
    directory=HERE/"contrast-source"
    command=[sys.executable,str(directory/"certify.py"),"--check-only"]
    if certificate is not None:
        command.extend(("--certificate",str(certificate)))
    run=subprocess.run(command,text=True,capture_output=True,timeout=60)
    row=json.loads(run.stdout)
    require(run.returncode==0 and row.get("schema")=="p23-source-contrast-evidence/v1" and
            all(row.get(name) is True for name in ("evidence_valid","source_generated_probability_law_all_N",
                "source_negative_CH_implies_original_binomial_threshold","source_negative_CH_fixed_bet_expected_value_bound")) and
            all(row.get(name) is False for name in ("actual_source_epoch_or_hardware_identified","new_stochastic_process_or_Ville_kernel",
                "new_infinite_Born_or_Gaussian_Gamma_bridge","controller_advance")),"source_negative_CH_threshold_not_kernel_certified")
    return row


def generate():
    c,bindings=config()
    identity=prefix_identity(json.loads((HERE.parent/"observable-prediction/public-observables.json").read_text()),
                             json.loads((HERE/"published-statistics/published-inputs.json").read_text()),c)
    original=load_module("_pr_original_statistics",HERE/"published-statistics/audit.py")
    recalculated=original.generate();saved=json.loads((HERE/"published-statistics/audit-ps0001.json").read_text())
    require(recalculated==saved,"original_tail_receipt_recalculation_mismatch")
    arithmetic=arithmetic_review(saved,identity,c);kernel=kernel_review()
    positive=arithmetic["selection_scope_bounds"]["qualified_all_run_mask_cap"]["rejects_at_original_alpha"]
    return {"schema":SCHEMA,"version":VERSION,"evidence_valid":True,"bindings":bindings,
            "prefix_identity":identity,"source_contrast_kernel":kernel,**arithmetic,
            "alpha":c["alpha"],"setting_epsilon":c["original_setting_epsilon"],
            "qualified_negative_CH_source_class_statistically_rejected":positive,
            "verdict":"NEGATIVE_CH_SOURCE_CLASS_STATISTICALLY_REJECTED" if positive else "SOURCE_NULL_NOT_REJECTED_AT_FAMILY_CAP",
            "max_family_scope":"one_training_fixed_Nchi_per_qualified_candidate_no_test_cut_search",
            "all_masks_historical_execution_independently_certified":False,"mask_cap_grants_spacelike_identity":False,
            "original_CI_modified":False,"CI_compatible_negative_sources_claimed_logically_impossible":False,
            "source_actual_configuration_identified":False,"new_probability_process_kernel_claimed":False,
            "private_instrument_parameters_required_for_threshold":False,"bell_event_files_read":0,
            "nominal_optimum_contract_replaced":False}


def consume(certificate_path=None,disabled=False):
    result={"schema":"p23-original-source-review-evidence/v1","evidence_valid":False,"disabled":disabled,
            "original_public_prefix_source_review_certified":False,"source_negative_CH_null_rejected":False,"apparatus_optimum_verified":False}
    if disabled:
        return {**result,"reason":"explicitly_disabled"}
    try:
        canonical=HERE/"original-source-review.json"
        binding=frozen(canonical)
        candidate=Path(certificate_path) if certificate_path is not None else canonical
        require(digest(candidate)==binding["sha256"],"unbound_or_lookalike_original_source_certificate")
        report=json.loads(candidate.read_text())
        require(report==generate(),"original_source_review_failed_reverification")
        result.update(evidence_valid=True,original_public_prefix_source_review_certified=True,
                      source_negative_CH_null_rejected=report["qualified_negative_CH_source_class_statistically_rejected"],
                      verdict=report["verdict"],source=binding,selection_scope_bounds=report["selection_scope_bounds"],
                      max_family_scope=report["max_family_scope"],alpha=report["alpha"],
                      actual_source_configuration_identified=False,original_CI_modified=False,
                      private_instrument_parameters_required=False,reason="certified_original_prefix_and_source_generated_null")
    except (OSError,ValueError,KeyError,TypeError,subprocess.SubprocessError) as exc:
        result["reason"]=str(exc)
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument("--output",type=Path)
    parser.add_argument("--check-only",action="store_true");parser.add_argument("--certificate",type=Path);parser.add_argument("--disabled",action="store_true")
    args=parser.parse_args()
    if args.check_only:
        report=consume(args.certificate,args.disabled);print(json.dumps(report,sort_keys=True));return 0 if report["evidence_valid"] else 1
    require(args.output is not None and not args.output.exists(),"new_original_source_output_required")
    report=generate();args.output.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"sha256":digest(args.output),"verdict":report["verdict"],"bounds":report["selection_scope_bounds"]}));return 0


if __name__=="__main__":
    raise SystemExit(main())
