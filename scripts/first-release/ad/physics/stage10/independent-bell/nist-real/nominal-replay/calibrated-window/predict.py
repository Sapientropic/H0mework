#!/usr/bin/env python3
"""Single-only calibration and full-source phase-mixture window prediction."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
FREEZE = "435305719b"
VERSION = "p23-calibrated-window-cb0001"
FLAGS = ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
         "actual_window_model_identified", "calibration_protocol_identified", "noise_channel_identified",
         "source_pair_rate_reference_identified")


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
            "frozen_calibrated_source_changed:"+relative(path))


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name,path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


def inputs():
    for name in ("criterion.md","sources.json"):
        frozen(HERE/name,FREEZE)
    text = (HERE/"criterion.md").read_text()
    blocks = re.findall(r"```json\s*(.*?)\s*```",text,re.S)
    require(len(blocks) == 1,"nonunique_calibrated_source_criterion")
    config = json.loads(blocks[0])
    packet = json.loads((HERE/"sources.json").read_text())
    require(config["version"] == packet["version"] == VERSION and
            all(config[k] is False and packet[k] is False for k in FLAGS),"calibrated_source_scope_changed")
    bindings = {}
    for row in packet["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and digest(path) == row["sha256"],"calibrated_source_binding_mismatch")
        bindings[row["path"]] = row["sha256"]
    for name in ("criterion.md","sources.json"):
        bindings[relative(HERE/name)] = digest(HERE/name)
    public = (HERE.parent/"shalm2015-channel-inputs.txt").read_text()
    rows = re.findall(r"(\d+(?:\.\d+)?)\s+\+-\s+(\d+(?:\.\d+)?)\s*%\s*\((Alice|Bob)\)",public)
    require(len(rows) == 2 and {r[2] for r in rows} == {"Alice","Bob"},"ambiguous_efficiency_source_text")
    documented = {name:(F(center)/100,F(half)/100) for center,half,name in rows}
    require([documented[p][0] for p in ("Alice","Bob")] == list(map(F,config["eta_center"])) and
            all(documented[p][1] == F(config["eta_probability_half_width"]) for p in documented),
            "text_machine_efficiency_unit_mismatch")
    gaussian = load_module("_cb_frozen_gaussian",HERE.parent/"gaussian-window/gaussian.py")
    arithmetic = gaussian.arithmetic
    config = {**gaussian.specification(),**config}
    counts = json.loads((HERE/config["public_counts"]).resolve().read_text())["counts"]
    confidence = json.loads((HERE/config["public_confidence_report"]).resolve().read_text())["common_mean_confidence"]
    return config,bindings,counts,confidence,gaussian,arithmetic


def fifth_root(value, digits, I):
    value = F(value)
    require(0 <= value <= 1,"fifth_root_not_probability")
    scale = 10**digits
    target = value.numerator*scale**5//value.denominator
    lo,hi = 0,scale+1
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**5 <= target:
            lo = mid
        else:
            hi = mid
    upper = lo if F(lo,scale)**5 == value else lo+1
    return I(F(lo,scale),F(upper,scale))


def training_view(counts):
    require(len(counts) == 4,"missing_setting_cells")
    result = []
    for index in (0,3):
        row = counts[index]
        require(len(row) == 4 and all(type(c) is int and c >= 0 for c in row) and sum(row) > 0,
                "invalid_training_full_counts")
        result.append({"sA":F(row[0]+row[1],sum(row)),"sB":F(row[0]+row[2],sum(row))})
    return result


def nearest_grid(value, digits):
    scale = 10**digits
    def integer(x):
        x = x*scale+F(1,2)
        return x.numerator//x.denominator
    lo,hi = integer(value.lo),integer(value.hi)
    require(lo == hi,"ROOT_ENCLOSURE_DOES_NOT_FIX_SOURCE_GRID_POINT")
    return F(lo,scale)


def source_from_singles(view, config, gaussian):
    I = gaussian.I
    eta_a,eta_b = map(F,config["eta_center"])
    ba,bb = map(F,config["background_per_pulse"])
    normalized = []
    means = []
    for row in view:
        a = (1-ba)/fifth_root(1-row["sA"],config["root_precision_digits"],I)-1
        b = (1-bb)/fifth_root(1-row["sB"],config["root_precision_digits"],I)-1
        require(a.lo >= 0 and b.lo >= 0,"INVALID_SINGLE_CALIBRATION_MEAN")
        means.append({"A":a,"B":b})
        normalized.append((a/eta_a+b/eta_b)/2)
    s0,_ = gaussian.trigonometry(config["angles_deg"][0],config)
    s1,_ = gaussian.trigonometry(config["angles_deg"][1],config)
    difference = s1.square()-s0.square()
    require(difference.lo > 0,"singles_calibration_minor_not_positive")
    delta = (normalized[1]-normalized[0])/difference
    nv = normalized[0]-s0.square()*delta
    nh = nv+delta
    require(min(nh.lo,nv.lo) >= 0,"INVALID_SINGLE_CALIBRATION_SOURCE")
    th,tv = [nearest_grid(n/(1+n),config["source_grid_digits"]) for n in (nh,nv)]
    require(0 <= th < 1 and 0 <= tv < 1,"INVALID_SINGLE_CALIBRATION_GEOMETRIC_SOURCE")
    return {"geometric_ratio":[str(th),str(tv)],"transmission_A":[str(eta_a)]*2,
            "transmission_B":[str(eta_b)]*2}, {"view":view,"photon_means":means,
              "native_mean_enclosures":{"H":nh,"V":nv},"geometric_ratio_enclosures":{"H":nh/(1+nh),"V":nv/(1+nv)},
              "independent_joint_statistics_used":False,"heldout_rows_used":False,"global_N_used":False,
              "documented_optimal_state_used":False,"public_q_used":False}


def visibility_calibration(config):
    a,b = map(F,config["eta_center"])
    tc = F(config["calibration_geometric_ratio"])
    n = tc/(1-tc)
    u = a+b-a*b
    plus = 1-1/(1+n*a)-1/(1+n*b)+1/(1+n*u)
    minus = n*a/(1+n*a)*n*b/(1+n*b)
    base = (plus-minus)/(plus+minus)
    target = F(config["visibility_DA_center"])
    phase_flip = (1-target/base)/2
    require(0 <= phase_flip <= 1,"INVALID_VISIBILITY_CALIBRATION_SOURCE")
    d,k = (1+n*a)*(1+n*b),n*(1+n)*a*b
    monotone = (1-phase_flip)*(d-k)**2 >= phase_flip*d*d
    require(monotone,"CALIBRATION_FRINGE_NOT_MONOTONE")
    observed_da = (1-2*phase_flip)*base
    hv = list(map(F,config["visibility_HV_interval"]))
    da = list(map(F,config["visibility_DA_interval"]))
    matched = {}
    for party,x,y in (("Alice",a,b),("Bob",b,a)):
        efficiency = 1-(1-x)*(1+n*y)/((1+n*x)*(1+n*(x+y-x*y)))
        width = F(config["eta_probability_half_width"])
        matched[party] = {"raw_transmission":x,"source_bucket_efficiency":efficiency,
                          "interval":[x-width,x+width],"contained":x-width <= efficiency <= x+width}
    require(all(row["contained"] for row in matched.values()) and hv[0] <= base <= hv[1] and
            da[0] <= observed_da <= da[1],"CALIBRATION_MEMBER_OUTSIDE_PUBLIC_INTERVAL")
    return phase_flip,{"geometric_ratio":tc,"Jplus":plus,"Jminus":minus,"HV_visibility":base,
        "DA_visibility":observed_da,"DA_full_fringe_monotonicity":monotone,"phase_flip_probability":phase_flip,
        "matched_Klyshko":matched,"calibration_protocol_identified":False}


def mixed_pulse(packet, phase_flip, a, b, config, gaussian):
    components = []
    for phase in (F(1),F(-1)):
        source = gaussian.Source({**packet,"phase_cos":{"numerator":str(phase),"sqrt_denominator":"1"}})
        components.append(source.pulse(a,b,config))
    return {key:(1-phase_flip)*components[0][key]+phase_flip*components[1][key]
            for key in ("no_click_A","no_click_B","no_click_AB")}


def window(pulse, windows, background, gaussian):
    ba,bb = map(F,background)
    a = gaussian.power((1-ba)*pulse["no_click_A"],windows)
    b = gaussian.power((1-bb)*pulse["no_click_B"],windows)
    ab = gaussian.power((1-ba)*(1-bb)*pulse["no_click_AB"],windows)
    return {"sA":1-a,"sB":1-b,"j":1-a-b+ab}


def source_controls(counts, config, gaussian, original):
    altered = [list(row) for row in counts]
    for index in (0,3):
        altered[index] = [c+d for c,d in zip(altered[index],(1,-1,-1,1))]
    same,_ = source_from_singles(training_view(altered),config,gaussian)
    require(same == original,"joint_statistics_leaked_into_source")
    for index in (1,2):
        altered[index] = [c+(j+1)*17 for j,c in enumerate(altered[index])]
    held,_ = source_from_singles(training_view(altered),config,gaussian)
    require(held == original,"heldout_cell_or_global_N_leaked_into_source")
    packet = {"geometric_ratio":["1/10","1/10"],"transmission_A":["1","1"],"transmission_B":["1","1"]}
    pulse = mixed_pulse(packet,F(1,2),"45","45",config,gaussian)
    correct = window(pulse,5,(F(0),F(0)),gaussian)
    wrong = []
    for phase in ("1","-1"):
        source = gaussian.Source({**packet,"phase_cos":{"numerator":phase,"sqrt_denominator":"1"}})
        wrong.append(source.window("45","45",5,(F(0),F(0)),config)["observed"]["j"])
    after = (wrong[0]+wrong[1])/2
    covariance = gaussian.Source({**packet,"phase_cos":{"numerator":"0","sqrt_denominator":"1"}}).window(
        "45","45",5,(F(0),F(0)),config)["observed"]["j"]
    interior = window(mixed_pulse(packet,F(1,2),"0","45",config,gaussian),1,(F(0),F(0)),gaussian)["j"]
    endpoint = window(pulse,1,(F(0),F(0)),gaussian)["j"]
    checks = {"joint_change_preserving_marginals_does_not_change_source":same == original,
              "whole_heldout_rows_do_not_change_source":held == original,
              "phase_mix_after_window_is_a_different_source":not (after.lo <= correct["j"].hi and correct["j"].lo <= after.hi),
              "averaged_coherence_is_not_mixed_Gaussian_Born":not (covariance.lo <= correct["j"].hi and correct["j"].lo <= covariance.hi),
              "zero_DA_endpoint_contrast_need_not_mean_flat_full_fringe":endpoint.lo > interior.hi}
    require(all(checks.values()),"calibrated_source_control_failed")
    return checks


def generate():
    config,bindings,counts,confidence,gaussian,_ = inputs()
    path = Path(__file__).resolve()
    commit = subprocess.check_output(["git","log","-1","--format=%H","--",relative(path)],cwd=ROOT,text=True).strip()
    frozen(path,commit)
    subprocess.run(["git","merge-base","--is-ancestor",FREEZE,commit],cwd=ROOT,check=True)
    packet,construction = source_from_singles(training_view(counts),config,gaussian)
    phase_flip,calibration = visibility_calibration(config)
    cells = []
    for x,y in ((0,0),(0,1),(1,0),(1,1)):
        pulse = mixed_pulse(packet,phase_flip,config["angles_deg"][x],config["angles_deg"][2+y],config,gaussian)
        cells.append({"pulse_no_click":pulse,"observed":window(pulse,config["window_pulses"],config["background_per_pulse"],gaussian)})
    probabilities = {key:[row["observed"][field] for row in cells] for key,field in
                     (("j","j"),("sA_cell","sA"),("sB_cell","sB"))}
    inclusion = {key:[F(outer["exact_lower"]) <= inner.lo <= inner.hi <= F(outer["exact_upper"])
                      for inner,outer in zip(values,confidence[key])] for key,values in probabilities.items()}
    h,v = map(F,packet["geometric_ratio"])
    source = gaussian.Source({**packet,"phase_cos":{"numerator":"1","sqrt_denominator":"1"}})
    diagnostics = {"pair_at_least_one":h+v-h*v,"pair_exactly_one":(1-h)*(1-v)*(h+v),
                   "mean_pair":h/(1-h)+v/(1-v),"conditional_pair_amplitude_ratio":gaussian.square_root(v/h),
                   "documented_pair_probability":"1/2000","documented_amplitude_ratio":"276/961",
                   "public_q_uncertainty_bound_identified":False,"used_to_construct_source":False}
    report = {"schema":"p23-calibrated-window-primary/v1","version":VERSION,
        "criterion_freeze":{"commit":subprocess.check_output(["git","rev-parse",FREEZE],cwd=ROOT,text=True).strip(),
                            "sha256":digest(HERE/"criterion.md")},
        "executable_freeze":{"commit":commit,"sha256":digest(path)},"bindings":bindings,
        "source_parameters":packet,"phase_flip_probability":phase_flip,"source_construction":construction,
        "calibration_readouts":calibration,"public_cells":cells,"public_probabilities":probabilities,
        "confidence_inclusion":inclusion,"exact_pair_tail":source.total_pair_tail(config["source_pair_cutoff"]),
        "outcome":"EXHIBITED_PUBLICLY_CALIBRATED_WINDOW_MEMBER" if all(all(v) for v in inclusion.values()) else "NOT_CERTIFIED_BY_ENCLOSURE",
        "controls":source_controls(counts,config,gaussian,packet),"source_diagnostics":diagnostics,
        **{key:False for key in FLAGS},"private_optimizer_input_required":False,"bell_event_files_read":0,
        "retrospective":True,"independent_joint_statistics_used_to_construct_source":False,
        "other_implementation_output_used_as_input":False}
    return gaussian.serial(report)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only",action="store_true")
    args = parser.parse_args()
    result = generate()
    text = json.dumps(result,indent=2,allow_nan=False)+"\n"
    if not args.check_only:
        (HERE/"prediction.json").write_text(text)
    print(text,end="")


if __name__ == "__main__":
    main()
