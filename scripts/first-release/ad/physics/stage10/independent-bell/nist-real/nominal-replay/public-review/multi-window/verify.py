#!/usr/bin/env python3
"""Strict cross-verification of independently frozen public count receipts."""
from fractions import Fraction as F
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[7]
VERSION="p23-public-multi-window-cross-mwc0001"


def require(value,reason):
    if not value:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frozen(path):
    rel=Path(path).resolve().relative_to(ROOT).as_posix()
    commit=subprocess.check_output(["git","log","-1","--format=%H","--",rel],cwd=ROOT,text=True).strip()
    require(commit and subprocess.check_output(["git","show",commit+":"+rel],cwd=ROOT)==Path(path).read_bytes(),"unfrozen_cross_source:"+rel)
    return {"path":rel,"sha256":digest(path),"commit":commit}


def config():
    text=(HERE/"criterion-cross.md").read_text()
    blocks=re.findall(r"<!-- MW-CROSS-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- MW-CROSS-FROZEN-END -->",text,re.S)
    require(len(blocks)==1,"nonunique_cross_contract")
    cfg=json.loads(blocks[0])
    manifest=json.loads((HERE/"sources-cross.json").read_text())
    require(cfg["version"]==manifest["version"]==VERSION,"wrong_cross_contract")
    for row in manifest["inputs"]:
        require(digest(ROOT/row["path"])==row["sha256"],"cross_binding_changed:"+row["path"])
    for row in json.loads((HERE/"sources.json").read_text())["inputs"]:
        require(digest(ROOT/row["path"])==row["sha256"],"public_source_binding_changed:"+row["path"])
    return cfg,[frozen(HERE/n) for n in ("criterion-cross.md","sources-cross.json","verify.py")]


def endpoints(v):
    require(type(v) is dict and "exact_lower" in v and "exact_upper" in v,"not_an_exact_interval")
    lo,hi=F(v["exact_lower"]),F(v["exact_upper"])
    require(lo<=hi,"reversed_exact_interval")
    return lo,hi


def compare(a,b,tolerance,relative=False):
    al,au=endpoints(a);bl,bu=endpoints(b)
    require(max(al,bl)<=min(au,bu),"independent_direction_enclosures_disjoint")
    scale=max(F(1),abs(al),abs(au),abs(bl),abs(bu)) if relative else F(1)
    require(max(abs(al-bl),abs(au-bu))<=tolerance*scale,"independent_endpoint_difference_exceeded")
    return max(abs(al-bl),abs(au-bu))/scale


def load_firsts():
    a=json.loads((HERE/"primary-first.json").read_text())
    compressed=(HERE/"independent.json.gz").read_bytes()
    raw=gzip.decompress(compressed)
    meta=json.loads((HERE/"independent-gzip-storage.json").read_text())
    require(hashlib.sha256(raw).hexdigest()==meta["logical_sha256"] and len(raw)==meta["logical_bytes"] and
            hashlib.sha256(compressed).hexdigest()==meta["stored_sha256"],"independent_lossless_first_changed")
    return a,json.loads(raw)


def validate_pair(a,b,cfg):
    require(a["version"]==b["version"]=="p23-public-multi-window-mw0001","wrong_scientific_versions")
    require(a["alpha"]==b["statistics"]["alpha"]=="1/20" and
            b["statistics"]["feature_global_allocation"]==[16,40,6,32767] and
            a["global_count_processes"]==16*40*6*32767,"changed_confidence_budget")
    require(a["bell_event_files_read"]==b["bell_event_files_read"]==0 and
            b["overlapping_windows_multiplied_as_independent_likelihoods"] is False,"changed_input_role")
    require(len(a["runs"])==len(b["runs"])==cfg["expected_runs"],"missing_public_run")
    bm={r["workbook"]:r for r in b["runs"]}
    require(len(bm)==cfg["expected_runs"],"duplicate_independent_run")
    tolerance=F(cfg["CI_endpoint_tolerance"])
    etolerance=F(cfg["evalue_relative_tolerance"])
    checked=0;groups=0;max_ci=F(0);max_e=F(0);local_rows=[]
    for run in a["runs"]:
        require(run["workbook"] in bm,"lookalike_run")
        other=bm[run["workbook"]]
        require(run["sha256"]==other["sha256"] and run["complete_trials"]==other["complete_trials"],"changed_workbook_exposure")
        require(len(run["groups"])==len(other["groups"])==5,"missing_public_window")
        require(run["common_spacelike_pulse"]["necessary_common_pulse_constraints_nonempty"]==
                other["necessary_N1_N3_N5_N7"]["identical_fresh_pulse_necessary_relations_compatible"] and
                run["common_all_public_pulse"]["necessary_common_pulse_constraints_nonempty"]==
                other["necessary_including_N9"]["identical_fresh_pulse_necessary_relations_compatible"],"independent_necessary_verdict_differs")
        for ga,gb in zip(run["groups"],other["groups"]):
            groups+=1
            require(ga["pulse_count"]==gb["pulse_count"] and ga["sheet"]==gb["sheet"] and
                    ga["paper_pulse_numbers"]==gb["paper_pulse_numbers"] and ga["counts"]==gb["counts"] and
                    ga["complete_trials"]==gb["complete_trials"]==sum(map(sum,ga["counts"])) and
                    all(type(k) is int and k>=0 for row in ga["counts"] for k in row),"changed_complete_count_or_pulse_identity")
            require(ga["spacelike_pulse_identity_in_public_SI"]==gb["spacelike_review_scope"]==
                    (ga["pulse_count"] in (1,3,5,7)),"nine_pulse_spacelike_scope_changed")
            require(len(ga["count_receipts"])==len(gb["all_feature_receipts"])==12,"missing_feature_receipt")
            for index,(field,col) in enumerate(([("j",(0,))]*4)+([("sA_cell",(0,1))]*4)+([("sB_cell",(0,2))]*4)):
                row=index%4
                pa=ga["common_mean_confidence"][field][row];pb=gb["common_Born_CI"][field][row]
                max_ci=max(max_ci,compare(pa,pb,tolerance));checked+=1
                ra,rb=ga["count_receipts"][index],gb["all_feature_receipts"][index]
                count=sum(ga["counts"][row][k] for k in col)
                require(ra["feature_index"]==index and rb["field"]==field and rb["row"]==row and
                        ra["count"]==rb["count"]==count and ra["trials"]==rb["complete_trials"]==ga["complete_trials"],"feature_semantics_changed")
                ma={F(g["lambda"]):g["bound_expected_count"] for g in ra["grid"]}
                mb={F(g["lambda"]):g["predictable_mean_bound"] for g in rb["all_40_bets"]}
                expected={F(sign,2**k) for k in range(1,21) for sign in (-1,1)}
                require(len(ra["grid"])==len(rb["all_40_bets"])==40 and set(ma)==set(mb)==expected,"changed_fixed_lambda_grid")
                for lam in expected:
                    compare(ma[lam],mb[lam],tolerance)
            la,lb=ga["local_count_test"],gb["local_fixed_bet_review"]
            wins=ga["counts"][0][0]; losses=ga["counts"][1][1]+ga["counts"][2][2]+ga["counts"][3][0]
            require(la["win_count"]==lb["wins"]==wins and la["loss_count"]==lb["losses"]==losses and
                    F(la["q0"])==F(lb["q0"])==F(1006009,2000018),"changed_local_contrast")
            require(len(la["grid"])==len(lb["all_20_fixed_bets"])==20,"changed_local_bet_mixture")
            for index,(xa,xb) in enumerate(zip(la["grid"],lb["all_20_fixed_bets"]),start=1):
                require(xa["power"]==xb["power"]==index and F(xa["p"])==F(xb["p"]),"changed_local_fixed_bet")
                compare(xa["log_e_value"],xb["log_evalue"],tolerance)
            max_e=max(max_e,compare(la["mixture_e_value"],lb["e_mixture"],etolerance,relative=True))
            ae=endpoints(la["mixture_e_value"]);be=endpoints(lb["e_mixture"])
            lower=min(ae[0],be[0]);upper=max(ae[1],be[1])
            bound=min(F(1),1/lower) if lower>0 else F(1)
            require(F(la["time_uniform_single_process_p_upper"])>=min(F(1),1/ae[0]) and
                    endpoints(lb["individual_anytime_p_upper"])[1]>=min(F(1),1/be[0]),"fabricated_local_p_upper")
            local_rows.append({"workbook":run["workbook"],"N":ga["pulse_count"],"wins":wins,"losses":losses,
                               "e_value":{"exact_lower":str(lower),"exact_upper":str(upper)},"single_anytime_p_upper":str(bound),
                               "XOR3_four_window_p_upper":str(min(F(1),4*bound)),
                               "all_6_times_32767_p_upper":str(min(F(1),6*32767*bound)),
                               "four_window_spacelike_scope":ga["pulse_count"] in (1,3,5,7)})
    require(groups==cfg["expected_groups"] and checked==cfg["expected_features"],"incomplete_public_cross_verification")
    return {"runs":6,"windows":groups,"CI_features":checked,"count_bets":checked*40,"contrast_bets":groups*20,
            "maximum_CI_endpoint_difference":str(max_ci),"maximum_evalue_relative_difference":str(max_e),"local_count_review":local_rows}


def generate():
    cfg,bindings=config();a,b=load_firsts(); result=validate_pair(a,b,cfg)
    return {"schema":"p23-public-multi-window-cross/v1","version":VERSION,"evidence_valid":True,"bindings":bindings,
            **result,"public_complete_counts_and_independent_CI_certified":True,"necessary_common_pulse_verdicts_agree":True,
            "optimum_verified":False,"actual_configuration_identified":False,"sigma_hard_bounds_used":False}


def consume(certificate=None,disabled=False):
    result={"schema":"p23-public-multi-window-evidence/v1","evidence_valid":False,"disabled":disabled,
            "public_count_review_certified":False,"apparatus_optimum_verified":False}
    if disabled:
        result["reason"]="explicitly_disabled";return result
    try:
        canonical=HERE/"cross-verification.json"
        binding=frozen(canonical)
        candidate=Path(certificate) if certificate is not None else canonical
        require(digest(candidate)==binding["sha256"],"unbound_or_lookalike_cross_certificate")
        report=json.loads(candidate.read_text())
        require(report==generate(),"cross_certificate_reverification_failed")
        result.update(evidence_valid=True,public_count_review_certified=True,reason="certified_public_counts_and_joint_fixed_bets",
                      source=binding,features=report["CI_features"],local_count_review=report["local_count_review"])
    except (ValueError,OSError,KeyError,TypeError,subprocess.CalledProcessError) as exc:
        result["reason"]=str(exc)
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument("--output",type=Path)
    parser.add_argument("--check-only",action="store_true");parser.add_argument("--certificate",type=Path);parser.add_argument("--disabled",action="store_true")
    args=parser.parse_args()
    if args.check_only:
        report=consume(args.certificate,args.disabled);print(json.dumps(report,sort_keys=True));return 0 if report["evidence_valid"] else 1
    require(args.output is not None and not args.output.exists(),"first_cross_output_required")
    report=generate();args.output.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"output":str(args.output),"sha256":digest(args.output),"features":report["CI_features"]}));return 0


if __name__=="__main__":
    raise SystemExit(main())
