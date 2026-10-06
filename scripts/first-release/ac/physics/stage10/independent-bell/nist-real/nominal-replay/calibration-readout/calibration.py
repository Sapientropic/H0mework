#!/usr/bin/env python3
"""Source-count PGF and named bucket calibration readouts."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
FREEZE = "d9ead286cf"
VERSION = "p23-calibration-readout-cal0001"
SEED = HERE.parent/"observable-prediction/public-comparison-po0003.json"
FLAGS = ("calibration_preparation_identified", "calibration_ports_identified",
         "calibration_pump_identified", "background_subtraction_identified",
         "source_mapping_identified", "publication_configuration_identified", "production_admitted")
BACKGROUNDS = {"signal_only":(F(0),F(0)), "independent_OR":(F(89,10**8),F(32,10**8))}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return Path(path).relative_to(ROOT).as_posix()


def frozen(path, commit):
    subprocess.run(["git","merge-base","--is-ancestor",commit,"HEAD"],cwd=ROOT,check=True)
    raw = subprocess.check_output(["git","show",commit+":"+relative(path)],cwd=ROOT)
    if raw != Path(path).read_bytes():
        raise ValueError("frozen_source_changed:"+relative(path))


def inputs():
    for path in (HERE/"criterion.md",HERE/"sources.json"):
        frozen(path,FREEZE)
    source = json.loads((HERE/"sources.json").read_text())
    if source["version"] != VERSION or any(source[k] is not False for k in FLAGS):
        raise ValueError("calibration_scope_changed")
    bindings = {}
    for row in source["inputs"]:
        path = (ROOT/row["path"]).resolve()
        if not path.is_relative_to(ROOT) or digest(path) != row["sha256"]:
            raise ValueError("calibration_input_binding_mismatch")
        bindings[row["path"]] = row["sha256"]
    for path in (HERE/"criterion.md",HERE/"sources.json"):
        bindings[relative(path)] = digest(path)
    text = (HERE.parent/"shalm2015-channel-inputs.txt").read_text()
    rows = re.findall(r"(\d+(?:\.\d+)?)\s+\+-\s+(\d+(?:\.\d+)?)\s*%\s*\((Alice|Bob)\)",text)
    if len(rows) != 2 or {r[2] for r in rows} != {"Alice","Bob"}:
        raise ValueError("ambiguous_public_efficiency_text")
    width = F(source["eta_probability_half_width"])
    efficiencies = {}
    for center,half,party in rows:
        if F(half)/100 != width:
            raise ValueError("text_machine_efficiency_unit_mismatch")
        efficiencies[party] = (F(center)/100-width,F(center)/100+width)
    seed = json.loads(SEED.read_text())
    branch = next(r for r in seed["branches"] if r["model"] == "independent_OR")
    stats = {k:F(v) for k,v in branch["projected_statistics"].items()}
    packet = {"geometric_ratio":[],"transmission_A":[],"transmission_B":[]}
    for pol in ("H","V"):
        a,b,l = stats["A"+pol],stats["B"+pol],stats[pol]
        den = 5*l-a*b
        if min(a,b,l,den) <= 0:
            raise ValueError("NO_VALID_CALIBRATION_SEED")
        n = a*b/den
        packet["geometric_ratio"].append(n/(1+n))
        packet["transmission_A"].append(den/(5*b))
        packet["transmission_B"].append(den/(5*a))
    validate(packet)
    return packet,efficiencies,bindings


def validate(packet):
    ts,alice,bob = (packet[k] for k in ("geometric_ratio","transmission_A","transmission_B"))
    if any(len(x) != 2 for x in (ts,alice,bob)) or not all(0 <= t < 1 for t in ts):
        raise ValueError("invalid_geometric_source")
    if not all(0 <= t <= 1 for t in alice+bob):
        raise ValueError("invalid_pure_loss")


def pgf(ts, z):
    if not all(0 <= value <= 1 for value in z):
        raise ValueError("invalid_no_click_weight")
    return ((1-ts[0])/(1-ts[0]*z[0]))*((1-ts[1])/(1-ts[1]*z[1]))


def pair_quantities(ts):
    h,v = ts
    vacuum = (1-h)*(1-v)
    return {"at_least_one":1-vacuum,"exactly_one":vacuum*(h+v),
            "mean_pair":h/(1-h)+v/(1-v),"vacuum":vacuum}


def prepare(packet, name):
    output = {k:list(v) for k,v in packet.items()}
    if name == "pure_H_same_H_gain":
        output["geometric_ratio"][1] = F(0)
    elif name == "pure_V_same_V_gain":
        output["geometric_ratio"][0] = F(0)
    elif name != "dual_pol":
        raise ValueError("unknown_calibration_preparation")
    return output


def native_bucket(packet, windows, background):
    validate(packet)
    if type(windows) is not int or windows < 1 or not all(0 <= b <= 1 for b in background):
        raise ValueError("invalid_window_or_background")
    ts,a,b = (packet[k] for k in ("geometric_ratio","transmission_A","transmission_B"))
    ca,cb = [1-t for t in a],[1-t for t in b]
    pulse = {"A":pgf(ts,ca),"B":pgf(ts,cb),"AB":pgf(ts,[x*y for x,y in zip(ca,cb)])}
    bg_a,bg_b = background
    no_click = {"A":((1-bg_a)*pulse["A"])**windows,
                "B":((1-bg_b)*pulse["B"])**windows,
                "AB":((1-bg_a)*(1-bg_b)*pulse["AB"])**windows}
    rates = {"sA":1-no_click["A"],"sB":1-no_click["B"],
             "j":1-no_click["A"]-no_click["B"]+no_click["AB"]}
    if not all(0 <= p <= 1 for p in rates.values()) or rates["j"] > min(rates["sA"],rates["sB"]):
        raise ValueError("invalid_native_bucket_probability")
    ratios = {}
    for party,herald in (("Alice","sB"),("Bob","sA")):
        denominator = rates[herald]
        ratios[party] = {"status":"defined" if denominator else "UNDEFINED_ZERO_HERALD",
                         "value":rates["j"]/denominator if denominator else None}
    return {"pulse_no_click":pulse,"window_no_click":no_click,"probabilities":rates,"Klyshko":ratios}


def exact(value):
    return {"exact":str(value),"value":float(value)}


def render(value):
    if isinstance(value,F):
        return exact(value)
    if isinstance(value,dict):
        return {k:render(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):
        return [render(v) for v in value]
    return value


def monomode_identity(t, a, b):
    n = t/(1-t)
    u = a+b-a*b
    return 1-(1-a)*(1+n*b)/((1+n*a)*(1+n*u))


def named_branches(packet, efficiencies):
    rows = []
    for preparation in ("dual_pol","pure_H_same_H_gain","pure_V_same_V_gain"):
        source = prepare(packet,preparation)
        for windows in (1,5):
            for background_name,background in BACKGROUNDS.items():
                rates = native_bucket(source,windows,background)
                row = {"preparation":preparation,"window_pulses":windows,"background_model":background_name,
                       "source_parameters":source,"pair_quantities_per_pulse":pair_quantities(source["geometric_ratio"]),
                       **rates,"calibration_identity_identified":False}
                if preparation != "dual_pol" and windows == 1 and background_name == "signal_only":
                    index = 0 if preparation == "pure_H_same_H_gain" else 1
                    t = source["geometric_ratio"][index]
                    a,b = source["transmission_A"][index],source["transmission_B"][index]
                    identities = {"Alice":monomode_identity(t,a,b),"Bob":monomode_identity(t,b,a)}
                    row["matched_monopol_contract"] = {}
                    for party,transmission in (("Alice",a),("Bob",b)):
                        actual = rates["Klyshko"][party]["value"]
                        if actual != identities[party] or not 0 <= actual-transmission <= 2*t/(1-t):
                            raise ValueError("source_PGF_matched_Klyshko_contract_failed")
                        lo,hi = efficiencies[party]
                        row["matched_monopol_contract"][party] = {
                            "generated_exact_bucket_efficiency":actual,"raw_transmission":transmission,
                            "multi_pair_increase":actual-transmission,"increase_upper_bound":2*t/(1-t),
                            "public_interval":[lo,hi],"inside_public_interval":lo <= actual <= hi,
                            "role":"conditional calibration identity; actual identity not assigned"}
                rows.append(render(row))
    return rows


def controls():
    fixtures = [([F(0),F(0)],[F(1),F(1)],[F(1),F(1)]),
                ([F(1,10000),F(0)],[F(1),F(1)],[F(1),F(1)]),
                ([F(0),F(1,20000)],[F(4,5),F(7,10)],[F(3,4),F(13,20)]),
                ([F(1,10000),F(1,20000)],[F(0),F(0)],[F(1),F(1)]),
                ([F(1,10000),F(1,20000)],[F(1),F(1)],[F(0),F(0)]),
                ([F(1,10000),F(1,20000)],[F(4,5),F(7,10)],[F(3,4),F(13,20)]),
                ([F(1,500),F(1,1000)],[F(4,5),F(7,10)],[F(3,4),F(13,20)])]
    checked = []
    for ts,a,b in fixtures:
        packet = dict(zip(("geometric_ratio","transmission_A","transmission_B"),(ts,a,b)))
        for windows in (1,5):
            for background_name,background in BACKGROUNDS.items():
                row = native_bucket(packet,windows,background)
                for party in ("Alice","Bob"):
                    value = row["Klyshko"][party]["value"]
                    if value is not None and not 0 <= value <= 1:
                        raise ValueError("invalid_conditional_bucket_control")
                checked.append({"source_parameters":packet,"window_pulses":windows,
                                "background_model":background_name,**row})
    pure = dict(zip(("geometric_ratio","transmission_A","transmission_B"),
                    ([F(1,10000),F(0)],[F(4,5),F(7,10)],[F(3,4),F(13,20)])))
    single = native_bucket(pure,1,BACKGROUNDS["signal_only"])
    five = native_bucket(pure,5,BACKGROUNDS["signal_only"])
    q = pair_quantities(pure["geometric_ratio"])
    checks = {"mean_is_not_pair_at_least_one":q["mean_pair"] != q["at_least_one"],
              "exactly_one_is_not_at_least_one":q["exactly_one"] != q["at_least_one"],
              "bucket_efficiency_is_not_raw_loss":single["Klyshko"]["Alice"]["value"] != F(4,5),
              "five_any_click_is_not_sum":five["probabilities"]["j"] != 5*single["probabilities"]["j"],
              "OR_is_not_additive_background":native_bucket(pure,1,BACKGROUNDS["independent_OR"])["probabilities"]["sA"]
                   != single["probabilities"]["sA"]+BACKGROUNDS["independent_OR"][0],
              "vacuum_herald_is_undefined":native_bucket(fixtures_packet(fixtures[0]),1,(F(0),F(0)))["Klyshko"]["Alice"]["value"] is None}
    if not all(checks.values()):
        raise ValueError("failed_calibration_negative_control")
    return {"case_count":len(checked),"checks":checks,"rows":render(checked)}


def fixtures_packet(fixture):
    return dict(zip(("geometric_ratio","transmission_A","transmission_B"),fixture))


def generate():
    packet,efficiencies,bindings = inputs()
    path = Path(__file__).resolve()
    commit = subprocess.check_output(["git","log","-1","--format=%H","--",relative(path)],cwd=ROOT,text=True).strip()
    frozen(path,commit)
    subprocess.run(["git","merge-base","--is-ancestor",FREEZE,commit],cwd=ROOT,check=True)
    return {"schema":"p23-calibration-readout-primary/v1","version":VERSION,
            "status":"source_generated_calibration_readout","criterion_freeze":{"commit":subprocess.check_output(
                ["git","rev-parse",FREEZE],cwd=ROOT,text=True).strip(),"sha256":digest(HERE/"criterion.md")},
            "executable_freeze":{"commit":commit,"sha256":digest(path)},"bindings":bindings,
            "source_parameters":{k:list(map(str,v)) for k,v in packet.items()},
            "source_pair_quantities":render(pair_quantities(packet["geometric_ratio"])),
            "branches":named_branches(packet,efficiencies),"controls":controls(),
            "public_q":{"value":"1/2000","uncertainty_bound_identified":False,
                        "quantity_reference_identified":False,"used_to_fit_source":False},
            **{k:False for k in FLAGS},"private_optimizer_input_required":False,
            "bell_event_files_read":0,"retrospective":True,
            "actual_calibration_failure_claimed":False,"other_implementation_output_used_as_input":False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only",action="store_true")
    args = parser.parse_args()
    report = generate()
    data = json.dumps(report,indent=2,allow_nan=False)+"\n"
    if not args.check_only:
        (HERE/"calibration.json").write_text(data)
    print(data,end="")


if __name__ == "__main__":
    main()
