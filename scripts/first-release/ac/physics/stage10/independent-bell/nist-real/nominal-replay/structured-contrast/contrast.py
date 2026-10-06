#!/usr/bin/env python3
"""Complete-trial e-process for a named scalar-loss source bridge."""
from __future__ import annotations

import argparse
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN, localcontext
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
FREEZE = "b4114c8e81"
CRITERION = HERE/"criterion-sc0001.1.md"
SOURCES = HERE/"sources-sc0001.1.json"
VERSION = "p23-structured-contrast-sc0001.1"
FLAGS = ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
         "calibration_protocol_identified", "actual_source_failure_claimed")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return Path(path).relative_to(ROOT).as_posix()


def frozen(path, commit):
    subprocess.run(["git","merge-base","--is-ancestor",commit,"HEAD"],cwd=ROOT,check=True)
    require(subprocess.check_output(["git","show",commit+":"+relative(path)],cwd=ROOT) == Path(path).read_bytes(),
            "structured_source_changed:"+relative(path))


def specification(text):
    blocks = re.findall(r"```json\s*(.*?)\s*```",text,re.S)
    require(len(blocks) == 1 and text.count("SC-FROZEN-BEGIN") == text.count("SC-FROZEN-END") == 1,
            "nonunique_structured_criterion")
    config = json.loads(blocks[0])
    require(config["version"] == VERSION and all(config[k] is False for k in FLAGS),"structured_scope_changed")
    require(config["mirror_cells"] == [0,3] and config["lambda_exponents"] == list(range(1,21)),
            "structured_grid_changed")
    a,b,width = F(".747"),F(".756"),F(config["eta_probability_half_width"])
    require(width == F(".003") and "±.003" in text,"structured_efficiency_unit_mismatch")
    expected = {"nominal_center":a/b,"printed_probability_box":(a-width)/(b+width),
                "matched_calibration_box":(a-width-F(2,9999))/(b+width)}
    ratios = {k:F(v) for k,v in config["efficiency_ratios"].items()}
    require(ratios == expected and all(0 < c <= 1 for c in ratios.values()),"text_machine_ratio_mismatch")
    require(F(config["alpha"]) == F(1,20) and config["run_count"] == 6 and config["slot_subset_count"] == 32767 and
            config["efficiency_model_count"] == 3 and config["mirror_cell_count"] == 2 and config["lambda_count"] == 20,
            "structured_family_budget_changed")
    return config,ratios


def inputs():
    frozen(CRITERION,FREEZE); frozen(SOURCES,FREEZE)
    config,ratios = specification(CRITERION.read_text())
    source = json.loads(SOURCES.read_text())
    require(source["schema"] == "p23-structured-contrast-sources/v1" and source["version"] == VERSION and
            all(source[k] is False for k in FLAGS) and source["retrospective"] is True,"structured_input_scope_changed")
    bindings = {}
    for row in source["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and row["path"] not in bindings and digest(path) == row["sha256"],
                "structured_input_binding_mismatch")
        bindings[row["path"]] = row["sha256"]
    for path in (CRITERION,SOURCES):
        bindings[relative(path)] = digest(path)
    public = json.loads((HERE/config["public_counts"]).resolve().read_text())
    require(public["outcome_order"] == ["++","+0","0+","00"] and
            public["row_order"] == ["ab","ab_prime","a_prime_b","a_prime_b_prime"],"count_order_changed")
    counts = public["counts"]
    require(len(counts) == 4 and all(len(row) == 4 and all(type(n) is int and n >= 0 for n in row) and
            sum(row) > 0 for row in counts),"invalid_complete_trial_counts")
    text = (HERE.parent/"shalm2015-channel-inputs.txt").read_text()
    rows = re.findall(r"(\d+(?:\.\d+)?)\s+\+-\s+(\d+(?:\.\d+)?)\s*%\s*\((Alice|Bob)\)",text)
    require(len(rows) == 2 and {r[2] for r in rows} == {"Alice","Bob"} and
            all(F(half)/100 == F(config["eta_probability_half_width"]) for _,half,_ in rows),
            "public_efficiency_text_unit_mismatch")
    return config,ratios,counts,bindings


def logarithm(value, digits):
    value = F(value)
    require(value > 0,"nonpositive_test_factor")
    if value == 1:
        return F(0),F(0)
    with localcontext() as ctx:
        ctx.prec = digits
        ctx.rounding = ROUND_FLOOR
        lower = Decimal(value.numerator)/Decimal(value.denominator)
        ctx.rounding = ROUND_CEILING
        upper = Decimal(value.numerator)/Decimal(value.denominator)
        ctx.rounding = ROUND_HALF_EVEN
        lo = ctx.ln(lower).next_minus(ctx)
        hi = ctx.ln(upper).next_plus(ctx)
        return F(lo),F(hi)


def factors(c, lam):
    require(0 <= c <= 1 and 0 <= lam < 1,"invalid_null_or_bet")
    return (1-lam*(1-c),1-lam,1+c*lam,F(1))


def log_process(row, c, lam, digits):
    lo = hi = F(0)
    for count,factor in zip(row,factors(c,lam)):
        a,b = logarithm(factor,digits)
        lo += count*a
        hi += count*b
    return lo,hi


def enclosure(value):
    lo,hi = value
    return {"exact_lower":str(lo),"exact_upper":str(hi),"lower":float(lo),"upper":float(hi)}


def controls(ratios):
    lam = F(1,32)
    cases = 0
    for name,c in ratios.items():
        p = (F(0),c/(1+c),1/(1+c),F(0))
        require(sum(p) == 1 and sum(x*y for x,y in zip(p,factors(c,lam))) == 1,
                "zero_mean_factor_not_one")
        require(all(x >= 0 for x in factors(c,lam)),"negative_factor")
        a,b = (F(".747"),F(".756")) if name == "nominal_center" else (c*F(".759"),F(".759"))
        mean = F(1,10000)
        pa,pb = a*mean/(1+a*mean),b*mean/(1+b*mean)
        joint = 1-1/(1+a*mean)-1/(1+b*mean)+1/(1+mean*(a+b-a*b))
        distribution = (joint,pa-joint,pb-joint,1-pa-pb+joint)
        if c <= a/b:
            require(all(p >= 0 for p in distribution) and sum(distribution) == 1 and
                    sum(x*y for x,y in zip(distribution,factors(c,lam))) <= 1,"native_null_control_failed")
            cases += 1
    c = ratios["printed_probability_box"]
    checks = {"zero_mean_boundary_factor_is_one":True,"actual_thinning_null_controls":cases == 3,
              "same_trial_joint_factor_is_not_two_independent_factors":factors(c,lam)[0] != (1-lam)*(1+c*lam),
              "zero_bet_factor_is_one":factors(c,F(0)) == (F(1),)*4,
              "zero_outcome_factor_is_one":factors(c,lam)[3] == 1,
              "exact_recipe_matches_machine_ratios":ratios["matched_calibration_box"] == (F(".744")-F(2,9999))/F(".759")}
    require(all(checks.values()),"structured_contrast_control_failed")
    return checks


def generate():
    config,ratios,counts,bindings = inputs()
    path = Path(__file__).resolve()
    commit = subprocess.check_output(["git","log","-1","--format=%H","--",relative(path)],cwd=ROOT,text=True).strip()
    frozen(path,commit)
    subprocess.run(["git","merge-base","--is-ancestor",FREEZE,commit],cwd=ROOT,check=True)
    family = config["run_count"]*config["slot_subset_count"]*len(ratios)*len(config["mirror_cells"])*len(config["lambda_exponents"])
    delta = F(config["alpha"])/family
    threshold = logarithm(1/delta,config["primary_decimal_digits"])
    rows = []
    for name,c in ratios.items():
        for cell in config["mirror_cells"]:
            for exponent in config["lambda_exponents"]:
                lam = F(1,2**exponent)
                log_m = log_process(counts[cell],c,lam,config["primary_decimal_digits"])
                rows.append({"efficiency_model":name,"cell":cell,"lambda_exponent":exponent,
                             "c":str(c),"lambda":str(lam),"counts":counts[cell],"log_M":enclosure(log_m),
                             "rejected":log_m[0] > threshold[1]})
    summary = {}
    for name in ratios:
        selected = [row for row in rows if row["efficiency_model"] == name]
        best = max(selected,key=lambda row:F(row["log_M"]["exact_lower"]))
        summary[name] = {"rejected":any(row["rejected"] for row in selected),
                         "worst_case_null_ratio":str(ratios[name]),"max_log_M":best["log_M"],
                         "max_cell":best["cell"],"max_lambda_exponent":best["lambda_exponent"]}
    all_rejected = all(row["rejected"] for row in summary.values())
    return {"schema":"p23-structured-contrast-primary/v1","version":VERSION,
        "criterion_freeze":{"commit":subprocess.check_output(["git","rev-parse",FREEZE],cwd=ROOT,text=True).strip(),
                            "criterion_sha256":digest(CRITERION),"sources_sha256":digest(SOURCES)},
        "executable_freeze":{"commit":commit,"sha256":digest(path)},"bindings":bindings,
        "alpha":config["alpha"],"family_size":family,"per_process_delta":str(delta),"log_threshold":enclosure(threshold),
        "rows":rows,"summary":summary,"all_named_mappings_rejected":all_rejected,
        "outcome":"ALIGNED_SCALAR_MAPPING_REJECTED" if all_rejected else "NOT_ALL_NAMED_MAPPINGS_REJECTED",
        "controls":controls(ratios),"retrospective":True,"bell_event_files_read":0,
        "kernel_closed_form_Born_identity":False,"other_implementation_output_used_as_input":False,
        "nominal_optimum_verdict_changed":False,**{flag:False for flag in FLAGS}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only",action="store_true")
    args = parser.parse_args()
    report = generate()
    text = json.dumps(report,indent=2,allow_nan=False)+"\n"
    if not args.check_only:
        (HERE/"contrast.json").write_text(text)
    print(text,end="")


if __name__ == "__main__":
    main()
