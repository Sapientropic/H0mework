"""Vacuum geometric pair kernels -> thermal objects -> full threshold window law."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
PUBLIC = HERE.parent/"observable-prediction"


def module(name,path):
    spec = importlib.util.spec_from_file_location(name,path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


arithmetic = module("_gaussian_exact_arithmetic",HERE.parent/"response/response.py")
I = arithmetic.Interval
SCALE = 10**36


def require(condition,reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def specification():
    text = (HERE/"criterion.md").read_text()
    block = text.split("<!-- GW-FROZEN-BEGIN -->")[1].split("<!-- GW-FROZEN-END -->")[0]
    return json.loads(block.split("```json")[1].split("```")[0])


def square_root(value):
    value = arithmetic.as_interval(value)
    require(value.lo >= 0,"negative_sqrt")
    def floor_root(x):
        return math.isqrt(x.numerator*SCALE*SCALE//x.denominator)
    lower,upper = floor_root(value.lo),floor_root(value.hi)
    if F(upper,SCALE)**2 != value.hi:
        upper += 1
    return I(F(lower,SCALE),F(upper,SCALE))


def power(value,n):
    result = I.point(1)
    for _ in range(n):
        result *= value
    return result


def trigonometry(degrees,config):
    angle = F(degrees)
    if angle == 0:
        return I.point(0),I.point(1)
    if angle == 90:
        return I.point(1),I.point(0)
    argument = angle*I(*map(F,config["pi"]))/180
    return arithmetic.trig(argument,config["primary_terms"]),arithmetic.trig(argument,config["primary_terms"],True)


def parameter_packet(t,ta,tb,cos_numerator,cos_radicand=F(1)):
    return {"geometric_ratio":list(map(F,t)),"transmission_A":list(map(F,ta)),
            "transmission_B":list(map(F,tb)),
            "phase_cos":{"numerator":F(cos_numerator),"sqrt_denominator":F(cos_radicand)}}


def lift_seed(values,windows):
    """Calibration produces raw source/loss parameters before the target is inspected."""
    s = {k:F(v) for k,v in values.items()}
    t,ta,tb = [],[],[]
    for label in ("H","V"):
        a,b,j = s["A"+label],s["B"+label],s[label]
        denominator = windows*j-a*b
        require(a > 0 and b > 0 and denominator > 0,"NO_VALID_CALIBRATION_SEED")
        mean = a*b/denominator
        t.append(mean/(1+mean))
        ta.append(denominator/(windows*b))
        tb.append(denominator/(windows*a))
    return parameter_packet(t,ta,tb,s["X"],s["H"]*s["V"])


class Source:
    def __init__(self,parameters):
        self.parameters = parameters
        self.t = list(map(F,parameters["geometric_ratio"]))
        self.ta = list(map(F,parameters["transmission_A"]))
        self.tb = list(map(F,parameters["transmission_B"]))
        require(len(self.t) == len(self.ta) == len(self.tb) == 2,"wrong_source_shape")
        require(all(0 <= t < 1 for t in self.t),"invalid_geometric_pair_kernel")
        require(all(0 <= x <= 1 for x in self.ta+self.tb),"invalid_passive_loss")
        numerator = F(parameters["phase_cos"]["numerator"])
        radicand = F(parameters["phase_cos"]["sqrt_denominator"])
        require(radicand > 0 and numerator*numerator <= radicand,"invalid_source_phase")
        self.gamma = I.point(numerator)/square_root(radicand)
        self.n = [t/(1-t) for t in self.t]
        self.a = [n*t for n,t in zip(self.n,self.ta)]
        self.b = [n*t for n,t in zip(self.n,self.tb)]
        self.c = [n*(1+n)*ta*tb for n,ta,tb in zip(self.n,self.ta,self.tb)]

    def pulse(self,a,b,config):
        sa,ca = trigonometry(a,config)
        sb,cb = trigonometry(b,config)
        mean_a = self.a[0]*sa.square()+self.a[1]*ca.square()
        mean_b = self.b[0]*sb.square()+self.b[1]*cb.square()
        connected = (self.c[0]*sa.square()*sb.square()+self.c[1]*ca.square()*cb.square()
                     +2*square_root(self.c[0]*self.c[1])*self.gamma*sa*ca*sb*cb)
        denominator = (1+mean_a)*(1+mean_b)-connected
        require(denominator.lo > 0,"source_vacuum_determinant_not_positive")
        p0a,p0b,p00 = 1/(1+mean_a),1/(1+mean_b),1/denominator
        return {"no_click_A":p0a,"no_click_B":p0b,"no_click_AB":p00,
                "mean_A":mean_a,"mean_B":mean_b,"connected_intensity":connected,
                "intensity_coincidence":mean_a*mean_b+connected}

    def window(self,a,b,windows,background,config):
        pulse = self.pulse(a,b,config)
        ba,bb = map(F,background)
        p0a = power(pulse["no_click_A"],windows)
        p0b = power(pulse["no_click_B"],windows)
        p00 = power(pulse["no_click_AB"],windows)
        signal = {"sA":1-p0a,"sB":1-p0b,"j":1-p0a-p0b+p00}
        oa,ob = p0a*(1-ba)**windows,p0b*(1-bb)**windows
        oab = p00*((1-ba)*(1-bb))**windows
        return {"signal":signal,"observed":{"sA":1-oa,"sB":1-ob,"j":1-oa-ob+oab},
                "pulse":pulse,"window_no_click":{"A":p0a,"B":p0b,"AB":p00}}

    def total_pair_tail(self,cutoff):
        th,tv = self.t
        prefix = (1-th)*(1-tv)*sum((th**h*tv**(n-h) for n in range(cutoff+1) for h in range(n+1)),F(0))
        return 1-prefix

    def seed_coordinates(self,windows):
        return {"AH":windows*self.a[0],"AV":windows*self.a[1],"BH":windows*self.b[0],"BV":windows*self.b[1],
                "H":windows*self.c[0],"V":windows*self.c[1],"X":windows*square_root(self.c[0]*self.c[1])*self.gamma}


def serial(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,I):
        return value.receipt()
    if isinstance(value,dict):
        return {k:serial(v) for k,v in value.items()}
    if isinstance(value,list):
        return [serial(v) for v in value]
    return value


def cells(source,angles,windows,background,config):
    return [source.window(angles[x],angles[2+y],windows,background,config)
            for x in range(2) for y in range(2)]


def control_report(config):
    rows = []
    for i,t in enumerate(config["controls"]["geometric_ratio_pairs"]):
        for j,transmission in enumerate(config["controls"]["transmission_HV"]):
            ta,tb = transmission[:2],transmission[2:]
            for phase in config["controls"]["phase_cos"]:
                source = Source(parameter_packet(t,ta,tb,F(phase)))
                for windows in config["controls"]["windows"]:
                    for ai,angles in enumerate(config["controls"]["angles_deg"]):
                        rows.append({"case_id":f"t{i}/T{j}/ph{phase}/N{windows}/a{ai}",
                                     "source_parameters":source.parameters,"window_pulses":windows,"angles_deg":angles,
                                     "cells":cells(source,angles,windows,config["background_per_pulse"],config),
                                     "source_pair_tail":source.total_pair_tail(config["source_pair_cutoff"])})
    endpoints = []
    for th,tv in ((F("1/10000"),F(0)),(F(0),F("1/10000"))):
        source = Source(parameter_packet((th,tv),(1,1),(1,1),1))
        for angle in config["controls"]["endpoint_angles_deg"]:
            endpoints.append({"ratio_HV":[th,tv],"angle_deg":angle,
                              "cell":source.window(angle,angle,1,[F(0),F(0)],config)})
    return rows,endpoints


def generate():
    config = specification()
    seed_path = (HERE/config["seed_report"]).resolve()
    seed = json.loads(seed_path.read_text())
    require(seed["version"] == "p23-public-observables-po0003","wrong_seed_contract")
    branch = next(b for b in seed["branches"] if b["model"] == config["seed_model"])
    parameters = lift_seed(branch["projected_statistics"],config["window_pulses"])
    source = Source(parameters)
    reads = cells(source,config["angles_deg"],config["window_pulses"],config["background_per_pulse"],config)
    probabilities = {"j":[r["observed"]["j"] for r in reads],
                     "sA_cell":[r["observed"]["sA"] for r in reads],"sB_cell":[r["observed"]["sB"] for r in reads]}
    confidence = seed["common_mean_confidence"]
    included = {name:[F(c["exact_lower"]) <= p.lo <= p.hi <= F(c["exact_upper"]) for p,c in zip(values,confidence[name])]
                for name,values in probabilities.items()}
    all_included = all(all(v) for v in included.values())
    controls,endpoints = control_report(config)
    expected = {k:F(v) for k,v in branch["projected_statistics"].items()}
    coordinates = source.seed_coordinates(config["window_pulses"])
    lift_exact = {k: v.contains(expected[k]) if isinstance(v,I) else v == expected[k] for k,v in coordinates.items()}
    return serial({"schema":"p23-gaussian-window-primary/v1","version":config["version"],
                   "criterion_sha256":digest(HERE/"criterion.md"),"sources_sha256":digest(HERE/"sources.json"),
                   "program_sha256":digest(__file__),"seed_sha256":digest(seed_path),
                   "interval_source_sha256":digest(HERE.parent/"response/response.py"),
                   "source_parameters":parameters,"source_coordinates":coordinates,"seed_lift_exact":lift_exact,
                   "source_pair_tail":source.total_pair_tail(config["source_pair_cutoff"]),
                   "source_state":"normalized product TMSV kernels on vacuum; no photon-sector truncation",
                   "window_pulses":config["window_pulses"],"public_cells":reads,"public_probabilities":probabilities,
                   "confidence_inclusion":included,"outcome":"EXHIBITED_FULL_FOCK_WINDOW_MEMBER" if all_included else "NOT_CERTIFIED_BY_ENCLOSURE",
                   "controls":controls,"endpoint_controls":endpoints,
                   "private_optimizer_input_required":False,"publication_configuration_identified":False,
                   "source_mapping_identified":False,"production_admitted":False,"actual_window_model_identified":False,
                   "bell_event_files_read":0,"retrospective":True})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-only",action="store_true")
    args = parser.parse_args()
    content = json.dumps(generate(),indent=2,sort_keys=True,allow_nan=False)+"\n"
    if args.check_only:
        print(content,end="")
    else:
        (HERE/"gaussian.json").write_text(content)


if __name__ == "__main__":
    main()
