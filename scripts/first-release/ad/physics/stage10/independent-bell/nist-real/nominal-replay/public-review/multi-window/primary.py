#!/usr/bin/env python3
"""Complete public count envelopes and shared pulse-law necessary constraints."""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
ROOT = BASE.parents[5]
VERSION = "p23-public-multi-window-mw0001"


def require(value, reason):
    if not value:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frozen(path):
    relative = Path(path).resolve().relative_to(ROOT).as_posix()
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative], cwd=ROOT, text=True).strip()
    require(commit and subprocess.check_output(["git", "show", commit+":"+relative], cwd=ROOT) == Path(path).read_bytes(),
            "unfrozen_source:"+relative)
    return {"path": relative, "commit": commit, "sha256": digest(path)}


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    sys.modules[name] = value
    spec.loader.exec_module(value)
    return value


stats = module("_mw_public_count", BASE/"observable-prediction/public_compare.py")
I = stats.I


@lru_cache(maxsize=1)
def configuration():
    blocks = re.findall(r"<!-- MW-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- MW-FROZEN-END -->", (HERE/"criterion.md").read_text(), re.S)
    require(len(blocks) == 1, "nonunique_criterion")
    config = json.loads(blocks[0])
    manifest = json.loads((HERE/"sources.json").read_text())
    require(config["version"] == manifest["version"] == VERSION and config["features"] == 16 and
            config["alpha"] == "1/20" and config["pulse_counts"] == [1,3,5,7,9] and
            config["runs_covered"] == 6 and config["pulse_subsets_covered"] == 32767,
            "statistical_contract_changed")
    bindings = [frozen(HERE/name) for name in ("criterion.md", "sources.json", "primary.py")]
    subprocess.run(["git", "merge-base", "--is-ancestor", bindings[0]["commit"], bindings[2]["commit"]], cwd=ROOT, check=True)
    for row in manifest["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and digest(path) == row["sha256"], "input_binding_changed:"+row["path"])
    stats.arithmetic.PRECISION = 10**config["root_precision_digits"]
    return config, bindings


def validate_counts(counts):
    require(type(counts) is list and len(counts) == 4 and
            all(type(row) is list and len(row) == 4 for row in counts), "incomplete_setting_outcome_table")
    require(all(type(k) is int and k >= 0 for row in counts for k in row), "nonliteral_nonnegative_integer_required")
    require(all(sum(row) > 0 for row in counts), "empty_setting_exposure")
    return sum(map(sum, counts))


def pack(value):
    if isinstance(value, I):
        return value.receipt()
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): pack(v) for k,v in value.items()}
    if isinstance(value, (list,tuple)):
        return [pack(v) for v in value]
    return value


def intersection(values):
    require(bool(values), "empty_interval_list")
    lo, hi = max(v.lo for v in values), min(v.hi for v in values)
    return None if lo > hi else I(lo,hi)


def clamp_probability(value):
    return intersection([value,I(0,1)])


def nth_root(value, n, digits):
    require(0 <= value <= 1 and type(n) is int and n > 0, "invalid_probability_root")
    scale = 10**digits
    target = value.numerator*scale**n//value.denominator
    lo, hi = 0,scale+1
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**n <= target:
            lo = mid
        else:
            hi = mid
    return I(F(lo,scale),F(lo if F(lo,scale)**n == value else lo+1,scale))


def root_interval(value, n, digits):
    physical = clamp_probability(value)
    if physical is None:
        return None
    return I(nth_root(physical.lo,n,digits).lo,nth_root(physical.hi,n,digits).hi)


def envelopes(counts, config):
    n = validate_counts(counts)
    values = [row[0] for row in counts]+[row[0]+row[1] for row in counts]+[row[0]+row[2] for row in counts]
    eps = F(config["settings_predictability"])
    pl,pu = ((1-eps)/2)**2,((1+eps)/2)**2
    intervals,receipts = [],[]
    for index,k in enumerate(values):
        mean,receipt = stats.count_envelope(k,n,config)
        bound = I(max(F(0),mean.lo/pu),min(F(1),mean.hi/pl))
        intervals.append(bound)
        receipts.append({**receipt,"feature_index":index,"conditional_setting_probability":[str(pl),str(pu)],
                         "observable_mean":bound})
    return {"j":intervals[:4],"sA_cell":intervals[4:8],"sB_cell":intervals[8:]},receipts


def pulse_roots(ci,n,config):
    ba,bb = map(F,config["background_per_pulse"])
    rows=[]
    for cell in range(4):
        sa,sb,j = ci["sA_cell"][cell],ci["sB_cell"][cell],ci["j"][cell]
        values={"A":1-sa,"B":1-sb,"AB":1-sa-sb+j}
        row={}
        for name,background in (("A",1-ba),("B",1-bb),("AB",(1-ba)*(1-bb))):
            root=root_interval(values[name],n,config["root_precision_digits"])
            row[name] = None if root is None else clamp_probability(root/background)
        rows.append(row)
    return rows


def common_pulse(groups,pulse_counts):
    selected=[g for g in groups if g["pulse_count"] in pulse_counts]
    constraints={}
    for name,cell_sets in (("A",([0,1],[2,3])),("B",([0,2],[1,3])),("AB",([0],[1],[2],[3]))):
        for index,cell_set in enumerate(cell_sets):
            refs=[{"N":g["pulse_count"],"cell":cell,"interval":g["pulse_roots"][cell][name]}
                  for g in selected for cell in cell_set]
            intervals=[r["interval"] for r in refs]
            common=None if any(i is None for i in intervals) else intersection(intervals)
            witness=None
            if common is None:
                if any(i is None for i in intervals):
                    witness={"nonphysical_root":next(r for r in refs if r["interval"] is None)}
                else:
                    lower=max(refs,key=lambda r:r["interval"].lo)
                    upper=min(refs,key=lambda r:r["interval"].hi)
                    witness={"lower_source":lower,"upper_source":upper,"strict_gap":lower["interval"].lo-upper["interval"].hi}
            constraints[name+str(index)]={"intersection":common,"empty_witness":witness,"inputs":refs}
    compatible=all(v["intersection"] is not None for v in constraints.values())
    return {"pulse_counts":pulse_counts,"necessary_common_pulse_constraints_nonempty":compatible,
            "verdict":"NECESSARY_RELATIONS_NONEMPTY" if compatible else "IDENTICAL_PULSE_MODEL_REJECTED",
            "full_Gaussian_source_existence_certified":False,"constraints":constraints}


def decimal_bound(value,operation,precision=60):
    """Enclose rational input first, then use correctly rounded Decimal functions."""
    value=F(value)
    with localcontext() as ctx:
        ctx.prec=precision
        ctx.rounding=ROUND_FLOOR
        lower=Decimal(value.numerator)/Decimal(value.denominator)
        ctx.rounding=ROUND_CEILING
        upper=Decimal(value.numerator)/Decimal(value.denominator)
        ctx.rounding="ROUND_HALF_EVEN"
        lo=(lower.ln() if operation=="ln" else lower.exp()).next_minus()
        hi=(upper.ln() if operation=="ln" else upper.exp()).next_plus()
        return I(F(lo),F(hi))


def local_deterministic_check():
    rows=[]
    for a0,a1,b0,b1 in itertools.product((0,1),repeat=4):
        win=a0*b0
        loss=a0*(1-b1)+(1-a1)*b0+a1*b1
        require(win <= loss,"local_indicator_inequality_failed")
        rows.append({"assignment":[a0,a1,b0,b1],"win":win,"loss":loss})
    return rows


def local_bets(counts,config):
    validate_counts(counts)
    win=counts[0][0]
    loss=counts[1][1]+counts[2][2]+counts[3][0]
    eps=F(config["settings_predictability"])
    ratio=((1+eps)/(1-eps))**2
    q0=ratio/(1+ratio)
    logs,grid=[],[]
    for k in range(config["local_bet_grid_powers"][0],config["local_bet_grid_powers"][1]+1):
        p=q0+(1-q0)/2**k
        log=win*decimal_bound(p/q0,"ln")+loss*decimal_bound((1-p)/(1-q0),"ln")
        # exp(3)>10 follows already from its first four Taylor terms; exp(-256)<10^-80.
        value=I(0,F(1,10**80)) if log.hi < -256 else I(decimal_bound(log.lo,"exp").lo,decimal_bound(log.hi,"exp").hi)
        logs.append(value)
        grid.append({"power":k,"p":p,"log_e_value":log,"e_value":value})
    e=sum(logs,I.point(0))/len(logs)
    one=F(1)
    upper=min(one,one/e.lo) if e.lo>0 else one
    family=config["runs_covered"]*config["pulse_subsets_covered"]
    return {"win_count":win,"loss_count":loss,"CH_count_difference":win-loss,"q0":q0,"grid":grid,
            "mixture_e_value":e,"time_uniform_single_process_p_upper":upper,
            "all_run_all_mask_p_upper":min(one,family*upper),
            "named_four_window_p_upper":min(one,4*upper),
            "family_size":family,"empirical_grid_selection":False}


def run():
    config,bindings=configuration()
    document=json.loads((HERE/config["inputs"]).read_text())
    books=document["diagnostic_workbooks"]
    require(len(books)==6,"incomplete_runs")
    runs=[]
    for book in books:
        require(digest(HERE.parent/"public-summaries"/book["file"])==book["sha256"],"workbook_binding_changed")
        require([g["pulse_count"] for g in book["groups"]]==config["pulse_counts"],"incomplete_window_family")
        groups=[]
        exposure=None
        for group in book["groups"]:
            n=validate_counts(group["counts"])
            require(n==group["complete_trials_literal_count_sum"],"exposure_mismatch")
            require(exposure is None or exposure==n,"different_nested_window_exposure")
            exposure=n
            require(group["xml_integer_literals"] is True and group["paper_pulse_numbers"]==[int(v)+1 for v in group["sheet"]]
                    and len(group["paper_pulse_numbers"])==group["pulse_count"],"pulse_mapping_changed")
            ci,receipts=envelopes(group["counts"],config)
            groups.append({"pulse_count":group["pulse_count"],"paper_pulse_numbers":group["paper_pulse_numbers"],
                           "complete_trials":n,"setting_trial_totals":[sum(r) for r in group["counts"]],
                           "sheet":group["sheet"],"counts":group["counts"],"common_mean_confidence":ci,
                           "count_receipts":receipts,"pulse_roots":pulse_roots(ci,group["pulse_count"],config),
                           "local_count_test":local_bets(group["counts"],config),
                           "spacelike_pulse_identity_in_public_SI":group["pulse_count"] in config["spacelike_review_pulse_counts"]})
        runs.append({"workbook":book["file"],"url":book["url"],"sha256":book["sha256"],"complete_trials":exposure,
                     "groups":groups,"common_spacelike_pulse":common_pulse(groups,config["spacelike_review_pulse_counts"]),
                     "common_all_public_pulse":common_pulse(groups,config["pulse_counts"])})
    return pack({"schema":"p23-public-multi-window/v1","version":VERSION,"bindings":bindings,
                 "all_30_complete_public_tables_used":True,"confidence_features":360,"alpha":config["alpha"],
                 "global_count_processes":16*40*6*32767,"all_time_Ville_scope":True,
                 "local_indicator_proof":local_deterministic_check(),"runs":runs,
                 "public_calibration_sigma_not_hard_bound":True,"old_cut_not_replaced":True,
                 "bell_event_files_read":0,"nominal_optimum_verified":False})


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    require(not args.output.exists(),"first_receipt_already_exists")
    result=run()
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True,allow_nan=False)+"\n")
    print(json.dumps({"version":VERSION,"output":str(args.output),"sha256":digest(args.output),
                      "run_verdicts":{r["workbook"]:{"N1_3_5_7":r["common_spacelike_pulse"]["verdict"],
                                                   "N1_3_5_7_9":r["common_all_public_pulse"]["verdict"]} for r in result["runs"]}}))


if __name__=="__main__":
    main()
