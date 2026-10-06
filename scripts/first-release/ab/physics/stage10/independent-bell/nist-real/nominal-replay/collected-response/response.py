#!/usr/bin/env python3
"""Native collected-source CH, its angle response, and conditional calibration bounds."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
SOURCE = HERE.parent / "investigation/collected-source"
CRITERION = "criterion-r0001.1.md"
FREEZE = "4a8e1753f4"


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


arithmetic = module("_cr_primary_rational", HERE.parent / "response/response.py")
I, F = arithmetic.Interval, arithmetic.F
collection = module("_cr_primary_source", SOURCE / "model.py")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_frozen():
    freeze = subprocess.check_output(["git", "rev-parse", FREEZE], cwd=ROOT, text=True).strip()
    subprocess.run(["git", "merge-base", "--is-ancestor", freeze, "HEAD"], cwd=ROOT, check=True)
    for name in (CRITERION, "sources.json"):
        path = (HERE / name).relative_to(ROOT).as_posix()
        require(subprocess.check_output(["git", "show", freeze + ":" + path], cwd=ROOT) ==
                (HERE / name).read_bytes(), "unfrozen_input:" + name)
    text = (HERE / CRITERION).read_text()
    matches = re.findall(r"<!-- CR-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- CR-FROZEN-END -->", text, re.S)
    require(len(matches) == 1, "nonunique_criterion")
    config = json.loads(matches[0])
    for key in ("source_mapping_identified", "publication_configuration_identified", "production_admitted"):
        require(config[key] is False, "conditional_consumer_cannot_admit_source")
    packet = json.loads((HERE / "sources.json").read_text())
    for row in packet["inputs"]:
        require(digest(ROOT / row["path"]) == row["sha256"], "source_binding_mismatch:" + row["path"])
    require(F(config["q_max"]) / (F(config["klyshko_min"]["A"]) * F(config["klyshko_min"]["B"])) == F("25/23343"),
            "native_calibration_budget_mismatch")
    return config, {"commit": freeze, "criterion": CRITERION,
                    "criterion_sha256": digest(HERE / CRITERION), "sources_sha256": digest(HERE / "sources.json")}


def input_box(config, correction):
    half = F(config["angle_half_width_deg"])
    box = {key: I(F(value) - half, F(value) + half)
           for key, value in zip(("a0", "a1", "b0", "b1"), config["angles_deg"])}
    box["r_col"] = I(*map(F, config["r_col"]))
    box["gamma"] = I(*map(F, config["gamma"]))
    box["t"] = correction
    return box


def response_interval(box, side, pi, terms):
    r = box["r_col"]
    chi = 2 * r / (1 + r.square())
    own, other = ("a", "b") if side == "alice" else ("b", "a")
    sine, cosine = arithmetic.sin_cos(box[own + "1"], pi, terms)
    s0, c0 = arithmetic.sin_cos(box[other + "0"], pi, terms)
    s1, c1 = arithmetic.sin_cos(box[other + "1"], pi, terms)
    geometry_over_chi = sine * (c0 - c1) / (chi * cosine * (s0 - s1))
    required_gamma = (1 + box["t"]) * geometry_over_chi
    required_t = box["gamma"] / geometry_over_chi - 1
    normalized = chi * cosine * (s0 - s1) * (box["gamma"] - required_gamma) / 2
    sign = "negative" if normalized.hi < 0 else "positive" if normalized.lo > 0 else "not_certified"
    return {"normalized_per_radian": normalized.receipt(), "required_gamma": required_gamma.receipt(),
            "required_relative_Z_correction": required_t.receipt(), "sign": sign,
            "stationarity_excluded": sign != "not_certified",
            "nonzero_denominators": {"chi": chi.receipt(), "cos_primed": cosine.receipt(),
                                      "sine_difference": (s0 - s1).receipt()}}


def paired_update(box, config, pi, terms):
    path = dict(box)
    for key, value in zip(("a0", "a1", "b0", "b1"), config["paired_update_deg"]):
        step = F(value)
        path[key] = I(box[key].lo + min(step, 0), box[key].hi + max(step, 0))
    responses = {side: response_interval(path, side, pi, terms) for side in ("alice", "bob")}
    gain = I.point(0)
    for key, side, value in (("a1", "alice", config["paired_update_deg"][1]),
                             ("b1", "bob", config["paired_update_deg"][3])):
        row = responses[side]["normalized_per_radian"]
        gain += I(F(row["exact_lower"]), F(row["exact_upper"])) * F(value) * pi / 180
    return {"step_deg": config["paired_update_deg"], "path_box": {k: v.receipt() for k, v in path.items()},
            "path_responses": responses, "normalized_CH_improvement": gain.receipt(),
            "certified_improvement": gain.lo > 0,
            "absolute_scale": "multiply by the source-generated positive Q*uA*uB*trace(OmegaAB); no uniform absolute floor inferred"}


def projector(angle, derivative=False):
    s, c = math.sin(angle), math.cos(angle)
    return [[2 * s * c, c*c - s*s], [c*c - s*s, -2 * s * c]] if derivative else [[s*s, s*c], [s*c, c*c]]


def tensor(a, b):
    return [[a[i//2][j//2] * b[i%2][j%2] for j in range(4)] for i in range(4)]


def contract(rho, effect):
    value = sum(rho[i][j] * effect[j][i] for i in range(len(rho)) for j in range(len(rho)))
    require(abs(value.imag) < 1e-12, "nonreal_effect_readout")
    return value.real


class Model:
    def __init__(self, objects, config, lam):
        self.objects = objects
        self.Q, self.uA, self.uB, self.bA, self.bB = (
            float(F(config["controls"][key])) for key in ("Q", "uA", "uB", "background_A", "background_B"))
        self.lam = lam

    def rates(self, a, b):
        pa, pb = projector(a), projector(b)
        sa = self.Q * self.uA * contract(self.objects["A"], pa) + self.bA
        sb = self.Q * self.uB * contract(self.objects["B"], pb) + self.bB
        joint = self.Q * self.uA * self.uB * contract(self.objects["AB"], tensor(pa, pb))
        return sa, sb, joint + self.lam * sa * sb

    def score(self, angles):
        a0, a1, b0, b1 = angles
        return self.rates(a0,b0)[2] + self.rates(a0,b1)[2] + self.rates(a1,b0)[2] - self.rates(a1,b1)[2] - self.rates(a0,b0)[0] - self.rates(a0,b0)[1]

    def derivative(self, angles, side):
        a0, a1, b0, b1 = angles
        if side == "alice":
            dp = projector(a1, True)
            ds = self.Q * self.uA * contract(self.objects["A"], dp)
            return (self.Q * self.uA * self.uB * contract(self.objects["AB"], tensor(dp, [[x-y for x,y in zip(p,q)] for p,q in zip(projector(b0),projector(b1))])) +
                    self.lam * ds * (self.rates(a1,b0)[1] - self.rates(a1,b1)[1]))
        dp = projector(b1, True)
        ds = self.Q * self.uB * contract(self.objects["B"], dp)
        return (self.Q * self.uA * self.uB * contract(self.objects["AB"], tensor([[x-y for x,y in zip(p,q)] for p,q in zip(projector(a0),projector(a1))], dp)) +
                self.lam * ds * (self.rates(a0,b1)[0] - self.rates(a1,b1)[0]))


def controls(config):
    spec = collection.frozen()
    recipes = {r["name"]: r for r in spec["fixtures"]}
    rows, worst = [], 0.0
    settings = config["controls"]
    for name, r, phase, lam, degrees in itertools.product(settings["fixtures"], settings["r_src"],
            settings["phase_pi"], settings["lambda"], settings["angles_deg"]):
        source = collection.OpticalSource(recipes[name])
        objects = source.objects(float(F(r)), float(F(phase)))
        model = Model(objects, config, float(F(lam)))
        angles = [math.radians(float(F(a))) for a in degrees]
        updated = [a + math.radians(float(F(d))) for a,d in zip(angles,config["paired_update_deg"])]
        derivatives, fd_errors = {}, {}
        h = float(F(settings["derivative_step_radians"]))
        for index, side in ((1,"alice"),(3,"bob")):
            plus, minus = list(angles), list(angles)
            plus[index] += h; minus[index] -= h
            derivative = model.derivative(angles, side)
            error = abs(derivative - (model.score(plus)-model.score(minus))/(2*h))
            worst = max(worst,error)
            require(error <= float(F(settings["derivative_tolerance"])), "native_matrix_derivative_control_failed")
            derivatives[side], fd_errors[side] = derivative, error
        trace = sum(objects["AB"][i][i].real for i in range(4))
        contrast_a = objects["A"][1][1].real - objects["A"][0][0].real
        contrast_b = objects["B"][1][1].real - objects["B"][0][0].real
        rows.append({"fixture":name,"r_src":r,"phase_pi":phase,"lambda":lam,"angles_deg":degrees,
                     "CH":model.score(angles),"derivatives_per_radian":derivatives,
                     "finite_difference_errors":fd_errors,"paired_CH_improvement":model.score(updated)-model.score(angles),
                     "trace_joint":trace,"real_joint_coherence":2*objects["AB"][0][3].real,
                     "single_contrasts":{"A":contrast_a,"B":contrast_b},
                     "relative_M3_Z_correction":float(F(lam))*model.Q*contrast_a*contrast_b/trace,
                     "q_eff_calibration":source.rates(float(F(r)),model.Q,model.uA,model.uB)["q_eff"]})
    endpoint = collection.OpticalSource(recipes[settings["coordinate_regression"]["fixture"]])
    endpoint_rows = []
    for h,v in settings["coordinate_regression"]["preparations_HV"]:
        objects = endpoint.objects_from_preparation(float(F(h)),float(F(v)))
        for value in settings["coordinate_regression"]["physical_vertical_angles_deg"]:
            angle = math.radians(float(F(value)))
            actual = contract(objects["A"],projector(angle))
            expected = float(F(v))**2 if F(value)==0 else float(F(h))**2
            require(abs(actual-expected)<=float(F(settings["probability_tolerance"])),"source_effect_coordinate_mismatch")
            wrong = contract(objects["A"],projector(math.pi/2-angle))
            require(abs(wrong-expected)>.5,"coordinate_lookalike_not_rejected")
            endpoint_rows.append({"preparation_HV":[h,v],"physical_angle_deg":value,"single_click":actual,"wrong_effect_click":wrong})
    same_joint_checks=[]
    for row in rows:
        if row["fixture"] != "calibration_I":
            continue
        matching=next(x for x in rows if x["fixture"]=="calibration_II" and
                      all(x[k]==row[k] for k in ("r_src","phase_pi","lambda","angles_deg")))
        angles=[math.radians(float(F(a))) for a in row["angles_deg"]]
        for side,index,other in (("alice",1,(2,3)),("bob",3,(0,1))):
            difference=matching["derivatives_per_radian"][side]-row["derivatives_per_radian"][side]
            expected=(-float(F(row["lambda"])) * float(F(settings["Q"]))**2 *
                      float(F(settings["uA"]))*float(F(settings["uB"]))/2 * (-9/400) *
                      math.sin(2*angles[index])*(math.cos(2*angles[other[0]])-math.cos(2*angles[other[1]])))
            require(abs(difference-expected)<=float(F(settings["probability_tolerance"])),"same_joint_response_difference_failed")
        if F(row["lambda"])==0:
            require(abs(matching["CH"]-row["CH"])>1e-12,"same_primed_response_incorrectly_made_full_CH_equal")
        same_joint_checks.append({"r_src":row["r_src"],"phase_pi":row["phase_pi"],"lambda":row["lambda"],
                                  "angles_deg":row["angles_deg"],"same_joint_trace":abs(matching["trace_joint"]-row["trace_joint"])<1e-12,
                                  "delta_contrast_product":matching["single_contrasts"]["A"]*matching["single_contrasts"]["B"]-
                                                           row["single_contrasts"]["A"]*row["single_contrasts"]["B"],
                                  "full_CH_difference":matching["CH"]-row["CH"],"response_difference_verified":True})
    objects=collection.OpticalSource(recipes["calibration_II"]).objects(float(F(settings["r_src"][0])))
    model=Model(objects,config,1)
    angles=[math.radians(float(F(a))) for a in settings["angles_deg"][0]]
    degenerate=[]
    for key in ("Q","uA","uB"):
        control=Model(objects,config,1);setattr(control,key,0.)
        derivatives={side:control.derivative(angles,side) for side in ("alice","bob")}
        require(all(abs(value)<1e-15 for value in derivatives.values()),"zero_rate_override_failed")
        degenerate.append({"override":key+"=0","derivatives":derivatives})
    partial_a=[[sum(objects["AB"][2*i+k][2*j+k] for k in range(2)) for j in range(2)] for i in range(2)]
    partial_b=[[sum(objects["AB"][2*k+i][2*k+j] for k in range(2)) for j in range(2)] for i in range(2)]
    wrong=Model({**objects,"A":partial_a,"B":partial_b},config,0)
    actual=Model(objects,config,0)
    loss_error=abs(wrong.score(angles)-actual.score(angles))
    require(loss_error>float(F(settings["probability_tolerance"])),"joint_partial_trace_single_lookalike_accepted")
    return {"rows":rows,"worst_finite_difference_error":worst,"coordinate_endpoints":endpoint_rows,
            "same_joint_response_checks":same_joint_checks,"degenerate_overrides":degenerate,
            "single_pair_override": {"lambda":0,"CH":actual.score(angles),"M3_CH":model.score(angles)},
            "wrong_joint_marginal_single_CH_error":loss_error,"passed":True}


def bindings():
    packet=json.loads((HERE/"sources.json").read_text())
    result={r["path"]:digest(ROOT/r["path"]) for r in packet["inputs"]}
    for path in (HERE/CRITERION,HERE/"sources.json",HERE/"response.py",HERE.parent/"response/response.py"):
        result[path.relative_to(ROOT).as_posix()]=digest(path)
    return result


def compute():
    config,freeze=load_frozen()
    pi=I(*map(F,config["pi"]));terms=config["interval"]["primary_terms"]
    cases=[]
    for name,correction in (("single_pair_lambda0",I.point(0)),("M3_lambda1_calibration_envelope",I(*map(F,config["relative_M3_Z_correction"])))):
        box=input_box(config,correction)
        responses={side:response_interval(box,side,pi,terms) for side in ("alice","bob")}
        update=paired_update(box,config,pi,terms)
        passed=responses["alice"]["sign"]=="negative" and responses["bob"]["sign"]=="positive" and update["certified_improvement"]
        cases.append({"case":name,"status":"CERTIFIED" if passed else "NOT_CERTIFIED",
                      "box":{k:v.receipt() for k,v in box.items()},"responses":responses,"paired_update":update})
    return {"schema":"p23-collected-response-primary/v1","version":config["version"],"freeze":freeze,
            "source_mapping_identified":False,"publication_configuration_identified":False,"production_admitted":False,
            "status":"CERTIFIED" if all(c["status"]=="CERTIFIED" for c in cases) else "NOT_CERTIFIED",
            "normalized_convention":"dCH/(Q*uA*uB*trace(OmegaAB)); derivative per radian",
            "cases":cases,"source_controls":controls(config),"bindings":bindings(),
            "scope":"source-generated polarization-preserving single-pair collection, explicit lambda0/lambda1 rates, independently qualified collected-plane calibration envelope",
            "actual_final_NIST_calibration_bound":False,"bell_event_files_read":0,
            "other_implementation_output_used_as_input":False}


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only",action="store_true")
    args=parser.parse_args()
    result=compute()
    if not args.check_only:
        (HERE/"response.json").write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({"status":result["status"],"cases":[{"case":c["case"],"update":c["paired_update"]["normalized_CH_improvement"]} for c in result["cases"]],"controls":len(result["source_controls"]["rows"]),"fd_error":result["source_controls"]["worst_finite_difference_error"]},indent=2))
