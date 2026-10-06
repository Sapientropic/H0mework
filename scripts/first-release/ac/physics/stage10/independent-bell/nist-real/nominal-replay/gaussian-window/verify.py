#!/usr/bin/env python3
"""Independent intake of the frozen geometric-source/window evidence."""
from __future__ import annotations

import argparse
import ast
import cmath
from fractions import Fraction as F
from functools import lru_cache
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
PUBLIC = HERE.parent/"observable-prediction"
FREEZE = "5b5814bceb3da6d03a84147d9af67327962e97b1"
VERSION = "p23-gaussian-window-gw0001"
SCHEMA = "p23-gaussian-window-verification/v1"
PRIMARY, INDEPENDENT = "gaussian.json", "independent_fock.json"
PROGRAMS = ("gaussian.py", "independent_fock.py")
IDENTITY = ("source_mapping_identified", "publication_configuration_identified",
            "production_admitted", "actual_window_model_identified")
KEYS = ("j", "sA_cell", "sB_cell")
INTERVAL_SOURCE = HERE.parent/"response/response.py"
LEAN_CHAIN = (HERE/"GaussianSource.lean", HERE/"Consumer.lean", HERE/"GaussianCertification.lean")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return Path(path).relative_to(ROOT).as_posix()


def frozen_file(path, commit):
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    require(subprocess.check_output(["git", "show", commit+":"+relative(path)], cwd=ROOT) == Path(path).read_bytes(),
            "frozen_file_changed:"+relative(path))


def program_freeze(path):
    name = relative(path)
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", name], cwd=ROOT, text=True).strip()
    require(bool(commit), "execution_source_not_committed:"+name)
    subprocess.run(["git", "merge-base", "--is-ancestor", FREEZE, commit], cwd=ROOT, check=True)
    frozen_file(path, commit)
    return {"commit":commit, "sha256":digest(path)}


def parse_criterion(text):
    start, end = "<!-- GW-FROZEN-BEGIN -->", "<!-- GW-FROZEN-END -->"
    require(text.count(start) == text.count(end) == 1, "nonunique_geometric_criterion")
    blocks = re.findall(r"```json\s*(.*?)\s*```", text, re.S)
    require(len(blocks) == 1, "nonunique_geometric_criterion")
    spec = json.loads(blocks[0])
    require(spec["version"] == VERSION and spec["source"] == "pair_only_two_polarization_single_mode_TMSV_from_vacuum",
            "source_contract_changed")
    require(all(spec[key] is False for key in IDENTITY), "conditional_source_cannot_admit_identity")
    require(spec["window_pulses"] == 5 and type(spec["window_pulses"]) is int and
            spec["source_pair_cutoff"] == 6 and spec["primary_terms"] == 12 and spec["independent_terms"] == 14 and
            spec["primary_precision_digits"] == 36 and spec["independent_precision_digits"] == 30,
            "frozen_method_changed")
    require(spec["seed_model"] == "independent_OR" and spec["seed_report"] == "../observable-prediction/public-comparison-po0003.json",
            "seed_contract_changed")
    require(spec["bell_event_files_read"] == 0 and type(spec["bell_event_files_read"]) is int and
            spec["retrospective"] is True, "unexpected_data_role")
    require(spec["pi"] == ["3.14159265358979323846", "3.14159265358979323847"] and
            F(spec["implementation_tolerance"]) == F(1,10**12), "frozen_enclosure_budget_changed")
    return spec


def scientific_inputs():
    for path in (HERE/"criterion.md", HERE/"sources.json", INTERVAL_SOURCE):
        frozen_file(path, FREEZE)
    spec = parse_criterion((HERE/"criterion.md").read_text())
    packet = json.loads((HERE/"sources.json").read_text())
    require(packet["schema"] == "p23-gaussian-window-sources/v1" and all(packet[k] is False for k in IDENTITY) and
            packet["private_optimizer_input_required"] is False and packet["bell_event_files_read"] == 0,
            "source_packet_scope_mismatch")
    subprocess.run(["git", "merge-base", "--is-ancestor", packet["public_source_commit"], FREEZE], cwd=ROOT, check=True)
    bindings = {}
    for row in packet["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and row["path"] not in bindings, "invalid_source_path")
        require(digest(path) == row["sha256"], "source_binding_mismatch:"+row["path"])
        bindings[row["path"]] = row["sha256"]
    for path in (HERE/"criterion.md", HERE/"sources.json", INTERVAL_SOURCE):
        bindings[relative(path)] = digest(path)
    seed = json.loads((HERE/spec["seed_report"]).resolve().read_text())
    require(seed["version"] == "p23-public-observables-po0003", "wrong_public_seed_revision")
    branch = next(row for row in seed["branches"] if row["model"] == "independent_OR")
    values = {key:F(value) for key,value in branch["projected_statistics"].items()}
    require(values.keys() == {"AH","AV","BH","BV","H","V","X"} and
            values == {key:F(value) for key,value in branch["source_member"]["statistics"].items()},
            "seed_statistics_and_source_disagree")
    confidence = seed["common_mean_confidence"]
    require(confidence.keys() == set(KEYS) and all(len(confidence[key]) == 4 for key in KEYS), "incomplete_public_confidence")
    for key in KEYS:
        for row in confidence[key]:
            interval(row)
    return spec, bindings, values, confidence


def implementation(path):
    name = "_gw_verified_"+path.stem+digest(path)[:12]
    specification = importlib.util.spec_from_file_location(name,path)
    module = importlib.util.module_from_spec(specification)
    sys.modules[name] = module
    specification.loader.exec_module(module)
    return module


def same_structure(actual, expected):
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(same_structure(actual[k],v) for k,v in expected.items())
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(same_structure(a,b) for a,b in zip(actual,expected))
    return actual == expected


def interval(row):
    require(isinstance(row,dict) and isinstance(row["exact_lower"],str) and isinstance(row["exact_upper"],str),
            "missing_exact_rational_interval")
    lower, upper = F(row["exact_lower"]), F(row["exact_upper"])
    require(lower <= upper, "reversed_mathematical_interval")
    for key,value in (("lower",lower),("upper",upper)):
        if key in row:
            require(type(row[key]) in (int,float) and math.isfinite(row[key]) and row[key] == float(value),
                    "displayed_interval_and_exact_fraction_disagree")
    return lower, upper


def inside(inner, outer):
    a,b = interval(inner); c,d = interval(outer)
    return c <= a <= b <= d


def overlap(left, right):
    a,b = interval(left); c,d = interval(right)
    return max(a,c) <= min(b,d)


def interval_distance(value, row):
    lo,hi = interval(row)
    return max(float(lo)-value, value-float(hi), 0.)


def tail(ratios, cutoff):
    h,v = ratios
    mass = (1-h)*(1-v)*sum((h**k*v**(n-k) for n in range(cutoff+1) for k in range(n+1)),F(0))
    require(0 <= mass <= 1, "invalid_geometric_source_mass")
    return mass, 1-mass


def seed_packet(values, windows):
    ratios,alice,bob = [],[],[]
    for pol in ("H","V"):
        a,b,l = values["A"+pol],values["B"+pol],values[pol]
        den = windows*l-a*b
        require(a > 0 and b > 0 and l > 0 and den > 0, "NO_VALID_CALIBRATION_SEED")
        # The cancelled form is independent of the primary n/(1+n) implementation.
        ratios.append(a*b/(windows*l))
        alice.append(l/b-a/windows)
        bob.append(l/a-b/windows)
    require(values["X"]**2 <= values["H"]*values["V"], "NO_VALID_CALIBRATION_SEED: phase")
    packet = {"geometric_ratio":list(map(str,ratios)),"transmission_A":list(map(str,alice)),
              "transmission_B":list(map(str,bob)),"phase_cos":{"numerator":str(values["X"]),
                "sqrt_denominator":str(values["H"]*values["V"])}}
    parameters(packet)
    return packet


def parameters(packet):
    arrays = []
    for name in ("geometric_ratio","transmission_A","transmission_B"):
        require(isinstance(packet[name],list) and len(packet[name]) == 2 and all(isinstance(v,str) for v in packet[name]),
                "invalid_raw_source_shape")
        arrays.append(tuple(map(F,packet[name])))
    ratios,alice,bob = arrays
    require(all(0 <= t < 1 for t in ratios), "invalid_geometric_ratio")
    require(all(0 <= t <= 1 for t in alice+bob), "invalid_passive_loss")
    numerator = F(packet["phase_cos"]["numerator"])
    radicand = F(packet["phase_cos"]["sqrt_denominator"])
    require(radicand > 0 and numerator*numerator <= radicand, "invalid_unit_circle_phase")
    return ratios,alice,bob,numerator,radicand


def lift_identities(packet, values, windows):
    ratios,alice,bob,num,rad = parameters(packet)
    means = [t/(1-t) for t in ratios]
    connected = [n*(1+n)*a*b for n,a,b in zip(means,alice,bob)]
    generated = {"AH":windows*means[0]*alice[0],"AV":windows*means[1]*alice[1],
                 "BH":windows*means[0]*bob[0],"BV":windows*means[1]*bob[1],
                 "H":windows*connected[0],"V":windows*connected[1]}
    return {**{k:value == values[k] for k,value in generated.items()},
            "X":num == values["X"] and rad == values["H"]*values["V"] and windows**2*connected[0]*connected[1] == rad}


@lru_cache(maxsize=512)
def symmetric_blocks(transmission, degrees, cutoff):
    th,tv = map(float,transmission)
    a = math.radians(float(degrees)); w = (math.sqrt(th)*math.sin(a),math.sqrt(tv)*math.cos(a))
    effect = [[float(i == j)-w[i]*w[j] for j in range(2)] for i in range(2)]
    blocks = []
    for total in range(cutoff+1):
        block = [[0.]*(total+1) for _ in range(total+1)]
        for source_h in range(total+1):
            # Multiplication of creation polynomials builds the symmetric tensor effect.
            polynomial = [1.]
            for column in [0]*source_h+[1]*(total-source_h):
                moved = [0.]*(len(polynomial)+1)
                for h,coefficient in enumerate(polynomial):
                    moved[h] += coefficient*effect[1][column]
                    moved[h+1] += coefficient*effect[0][column]
                polynomial = moved
            normalization = math.factorial(source_h)*math.factorial(total-source_h)
            for target_h,coefficient in enumerate(polynomial):
                block[target_h][source_h] = coefficient*math.sqrt(
                    math.factorial(target_h)*math.factorial(total-target_h)/normalization)
        blocks.append(block)
    return blocks


def fock_prefix(packet, a, b, cutoff):
    ratios,alice,bob,num,rad = parameters(packet)
    cosine = float(num)/math.sqrt(float(rad))
    require(abs(cosine) <= 1+1e-15, "invalid_float_phase_control")
    phase = complex(cosine,math.sqrt(max(0.,1-cosine*cosine)))
    ah,av = map(float,ratios)
    normalization = math.sqrt((1-ah)*(1-av))
    left,right = symmetric_blocks(alice,F(a),cutoff),symmetric_blocks(bob,F(b),cutoff)
    p0a=p0b=p00=norm=0.
    for total in range(cutoff+1):
        amplitudes = [normalization*math.sqrt(ah)**h*math.sqrt(av)**(total-h)*phase**(total-h)
                      for h in range(total+1)]
        norm += math.fsum(abs(z)**2 for z in amplitudes)
        p0a += math.fsum(abs(z)**2*left[total][h][h] for h,z in enumerate(amplitudes))
        p0b += math.fsum(abs(z)**2*right[total][h][h] for h,z in enumerate(amplitudes))
        p00 += math.fsum((x.conjugate()*y).real*left[total][h][k]*right[total][h][k]
                        for h,x in enumerate(amplitudes) for k,y in enumerate(amplitudes))
    return {"P0A":p0a,"P0B":p0b,"P00":p00,"mass":norm}


def control_cases(spec):
    controls = spec["controls"]
    rows = {}
    for i,ratios in enumerate(controls["geometric_ratio_pairs"]):
        for j,loss in enumerate(controls["transmission_HV"]):
            for phase,window,a in itertools.product(controls["phase_cos"],controls["windows"],range(len(controls["angles_deg"]))):
                packet = {"geometric_ratio":ratios,"transmission_A":loss[:2],"transmission_B":loss[2:],
                          "phase_cos":{"numerator":phase,"sqrt_denominator":"1"}}
                name = f"t{i}/T{j}/ph{phase}/N{window}/a{a}"
                rows[name] = {"source_parameters":packet,"window_pulses":window,"angles_deg":controls["angles_deg"][a]}
    require(len(rows) == 180, "control_coverage_changed")
    return rows


def probability_verdict(values, confidence):
    require(values.keys() == set(KEYS) and all(len(values[key]) == 4 for key in KEYS), "incomplete_window_probabilities")
    return {key:[inside(value,domain) for value,domain in zip(values[key],confidence[key])] for key in KEYS}


def add(left, right):
    return left[0]+right[0], left[1]+right[1]


def neg(value):
    return -value[1], -value[0]


def mul(left, right):
    values = [a*b for a in left for b in right]
    return min(values), max(values)


def power(value, exponent):
    require(value[0] >= 0 and type(exponent) is int and exponent >= 1, "invalid_probability_power")
    return value[0]**exponent, value[1]**exponent


def clipped(value):
    lo,hi = max(F(0),value[0]),min(F(1),value[1])
    require(lo <= hi, "empty_physical_probability_enclosure")
    return lo,hi


def encloses(row, value):
    lo,hi = interval(row)
    return lo <= value[0] <= value[1] <= hi


def validate_rates(pulse, rates, windows, background, *, primary):
    no = [power(interval(pulse[name]),windows) for name in ("P0A","P0B","P00")]
    a,b,j = no
    one = F(1),F(1)
    signal = {"sA":add(one,neg(a)),"sB":add(one,neg(b)),"j":add(add(add(one,neg(a)),neg(b)),j)}
    if not primary:
        signal = {name:clipped(value) for name,value in signal.items()}
    require(all(encloses(rates["signal"][name],value) for name,value in signal.items()), "window_signal_transport_mismatch")
    ba,bb = [1-(1-F(value))**windows for value in background]
    if primary:
        oa,ob,oab = mul(a,(1-ba,1-ba)),mul(b,(1-bb,1-bb)),mul(j,((1-ba)*(1-bb),(1-ba)*(1-bb)))
        observed = {"sA":add(one,neg(oa)),"sB":add(one,neg(ob)),"j":add(add(add(one,neg(oa)),neg(ob)),oab)}
    else:
        sa,sb,joint = (interval(rates["signal"][name]) for name in ("sA","sB","j"))
        observed = {"sA":add((ba,ba),mul((1-ba,1-ba),sa)),"sB":add((bb,bb),mul((1-bb,1-bb),sb)),
                    "j":add(add(add(mul(((1-ba)*(1-bb),(1-ba)*(1-bb)),joint),
                        mul((ba*(1-bb),ba*(1-bb)),sb)),mul((bb*(1-ba),bb*(1-ba)),sa)),(ba*bb,ba*bb))}
    require(all(encloses(rates["observed"][name],value) for name,value in observed.items()), "window_OR_transport_mismatch")


def primary_noclick(cell):
    return dict(zip(("P0A","P0B","P00"),[cell["pulse"][name] for name in ("no_click_A","no_click_B","no_click_AB")]))


def validate_prefix(packet, angles, pulse, spec, maxima):
    mass,budget = tail(parameters(packet)[0],spec["source_pair_cutoff"])
    require(F(pulse["mass"]) == mass and F(pulse["tail"]) == budget and mass+budget == 1,
            "unnormalized_source_prefix_or_tail_changed")
    actual = fock_prefix(packet,*angles,spec["source_pair_cutoff"])
    maxima["prefix_mass_error"] = max(maxima["prefix_mass_error"],abs(actual["mass"]-float(mass)))
    for name in ("P0A","P0B","P00"):
        lo,hi = interval(pulse["partial"][name])
        require(0 <= lo <= hi <= mass, "partial_Born_not_bounded_by_original_source_mass")
        require(encloses(pulse["full"][name],clipped((lo,hi+budget))), "unpaid_number_sector_tail")
        full_lo,full_hi = interval(pulse["full"][name])
        require(0 <= full_lo <= full_hi <= 1, "invalid_full_Born_range")
        maxima["prefix_Born_error"] = max(maxima["prefix_Born_error"],interval_distance(actual[name],pulse["partial"][name]))


def source_signature(row):
    ratios,alice,bob,num,rad = parameters(row["source_parameters"])
    require(type(row["window_pulses"]) is int and row["window_pulses"] in (1,5) and len(row["angles_deg"]) == 4,
            "invalid_control_window_or_angles")
    return ratios,alice,bob,num,rad,row["window_pulses"],tuple(map(F,row["angles_deg"]))


def validate_independent(report, primary, primary_rows, spec, seed, confidence):
    packet = seed_packet(seed,spec["window_pulses"])
    require(report["source_parameters"] == packet and
            {k:F(v) for k,v in report["calibration_seed"]["seed_statistics"].items()} == seed,
            "independent_source_or_seed_mismatch")
    require(report["calibration_seed"]["source_mapping_identified"] is False and
            all(value is True for group in report["calibration_seed"]["identities"].values()
                for key,value in group.items() if key.endswith(("matches_A","matches_B","matches_L"))),
            "independent_calibration_verdict_mismatch")
    candidate = report["candidate"]
    require(same_structure(report["prefix"],candidate["pulse_noclick"]) and len(report["prefix"]) == 4 and
            same_structure(report["public_probabilities"],candidate["observed_probability_enclosures"]),
            "independent_public_probability_body_mismatch")
    inclusion = probability_verdict(report["public_probabilities"],confidence)
    require(same_structure(report["confidence_inclusion"],inclusion) and
            same_structure(candidate["confidence_inclusion"],inclusion), "independent_public_inclusion_verdict_mismatch")
    outcome = "EXHIBITED_FULL_FOCK_WINDOW_MEMBER" if all(all(v) for v in inclusion.values()) else "NOT_CERTIFIED_BY_ENCLOSURE"
    require(report["outcome"] == candidate["enclosure_status"] == outcome, "independent_public_outcome_mismatch")
    require(F(report["cutoff_tail"]) == tail(parameters(packet)[0],spec["source_pair_cutoff"])[1], "independent_cutoff_tail_mismatch")
    maxima = {"prefix_mass_error":0.,"prefix_Born_error":0.}
    for index,(x,y) in enumerate(itertools.product(range(2),repeat=2)):
        pulse = report["prefix"][index]
        validate_prefix(packet,(spec["angles_deg"][x],spec["angles_deg"][2+y]),pulse,spec,maxima)
        rates = {"signal":{field:candidate["signal_probability_enclosures"][key][index] for key,field in
                            (("j","j"),("sA_cell","sA"),("sB_cell","sB"))},
                 "observed":{field:report["public_probabilities"][key][index] for key,field in
                            (("j","j"),("sA_cell","sA"),("sB_cell","sB"))}}
        validate_rates(pulse["full"],rates,spec["window_pulses"],spec["background_per_pulse"],primary=False)
        main_pulse = primary_noclick(primary["public_cells"][index])
        require(all(overlap(main_pulse[key],pulse["full"][key]) for key in main_pulse), "Gaussian_and_Fock_source_probabilities_disagree")
        validate_rates(main_pulse,primary["public_cells"][index],spec["window_pulses"],spec["background_per_pulse"],primary=True)
    expected = {source_signature(row):row for row in primary_rows.values()}
    controls = report["controls"]
    rows = controls["rows"]
    indexed = {source_signature(row):row for row in rows}
    require(len(rows) == len(indexed) == len(expected) == 180 and indexed.keys() == expected.keys() and
            len({row["case_id"] for row in rows}) == 180 and type(controls["case_count"]) is int and controls["case_count"] == 180 and
            type(controls["cell_count"]) is int and controls["cell_count"] == 720 and controls["passed"] is True and
            len(controls["checks"]) == 11 and all(value is True for value in controls["checks"].values()),
            "incomplete_or_failed_independent_controls")
    for signature,row in indexed.items():
        main = expected[signature]
        require(len(row["cells"]) == 4, "independent_control_cell_missing")
        for index,(x,y) in enumerate(itertools.product(range(2),repeat=2)):
            cell = row["cells"][index]
            pulse = cell["pulse_noclick"]
            angles = row["angles_deg"][x],row["angles_deg"][2+y]
            validate_prefix(row["source_parameters"],angles,pulse,spec,maxima)
            validate_rates(pulse["full"],cell,row["window_pulses"],spec["background_per_pulse"],primary=False)
            main_pulse = primary_noclick(main["cells"][index])
            require(all(overlap(main_pulse[key],pulse["full"][key]) for key in main_pulse), "control_Gaussian_Fock_no_click_disagreement")
            validate_rates(main_pulse,main["cells"][index],row["window_pulses"],spec["background_per_pulse"],primary=True)
    require(max(maxima.values()) <= float(F(spec["implementation_tolerance"])), "independent_creation_matrix_Born_control_failed")
    return {"outcome":outcome,"all_public_enclosures_contained":all(all(v) for v in inclusion.values()),
            "numeric_controls":{**maxima,"tolerance":spec["implementation_tolerance"],
              "role":"floating creation-polynomial/full-phase differential controls; exact enclosure inclusion is evaluated separately"}}


def validate_primary(report, spec, seed, confidence):
    expected = seed_packet(seed,spec["window_pulses"])
    require(report["source_parameters"] == expected and all(lift_identities(expected,seed,spec["window_pulses"]).values()),
            "raw_source_or_calibration_lift_mismatch")
    require(report["seed_lift_exact"].keys() == seed.keys() and all(value is True for value in report["seed_lift_exact"].values()),
            "seed_lift_verdict_mismatch")
    for key in seed:
        value = report["source_coordinates"][key]
        require(interval(value)[0] <= seed[key] <= interval(value)[1] if key == "X" else F(value) == seed[key],
                "source_coordinate_readback_mismatch")
    _,budget = tail(parameters(expected)[0],spec["source_pair_cutoff"])
    require(F(report["source_pair_tail"]) == budget, "source_tail_mismatch")
    require(type(report["window_pulses"]) is int and report["window_pulses"] == spec["window_pulses"] and
            len(report["public_cells"]) == 4, "window_contract_mismatch")
    probabilities = {key:[row["observed"][field] for row in report["public_cells"]]
                     for key,field in (("j","j"),("sA_cell","sA"),("sB_cell","sB"))}
    require(same_structure(report["public_probabilities"],probabilities), "window_probability_body_mismatch")
    inclusion = probability_verdict(probabilities,confidence)
    require(same_structure(report["confidence_inclusion"],inclusion), "public_inclusion_verdict_mismatch")
    outcome = "EXHIBITED_FULL_FOCK_WINDOW_MEMBER" if all(all(v) for v in inclusion.values()) else "NOT_CERTIFIED_BY_ENCLOSURE"
    require(report["outcome"] == outcome, "public_outcome_mismatch")
    controls = control_cases(spec)
    rows = {row["case_id"]:row for row in report["controls"]}
    require(len(report["controls"]) == len(rows) == 180 and rows.keys() == controls.keys(), "incomplete_source_controls")
    for name,row in rows.items():
        require(all(same_structure(row[key],value) for key,value in controls[name].items()) and len(row["cells"]) == 4,
                "control_source_or_window_changed")
        require(F(row["source_pair_tail"]) == tail(parameters(row["source_parameters"])[0],spec["source_pair_cutoff"])[1],
                "control_geometric_tail_changed")
    require(len(report["endpoint_controls"]) == 4, "endpoint_control_missing")
    return rows, inclusion, outcome


def verify_independent_snapshot(report, module, bindings, primary_hash):
    freeze = report["executable_freeze"]
    path = HERE/"independent_fock.py"
    for a,b in ((FREEZE,freeze["commit"]),(freeze["commit"],"HEAD")):
        subprocess.run(["git","merge-base","--is-ancestor",a,b],cwd=ROOT,check=True)
    raw = subprocess.check_output(["git","show",freeze["commit"]+":"+relative(path)],cwd=ROOT)
    def science(code):
        tree = ast.parse(code)
        tree.body = [node for node in tree.body if not isinstance(node,ast.FunctionDef) or node.name != "append_comparison"]
        return ast.dump(tree,include_attributes=False)
    require(hashlib.sha256(raw).hexdigest() == freeze["program_sha256"] and science(raw.decode()) == science(path.read_text()),
            "independent_scientific_source_changed")
    require(report["criterion_freeze"] == module.criterion_freeze() and
            report["other_implementation_output_used_as_input"] is False, "independent_source_or_input_contract_mismatch")
    expected_bindings = module.bindings()
    if "comparison" in report:
        expected_bindings[relative(HERE/PRIMARY)] = primary_hash
        expected_bindings[relative(HERE/"gaussian.py")] = digest(HERE/"gaussian.py")
        require(report["comparison"]["primary_report_sha256"] == primary_hash and
                report["comparison"]["primary_program_sha256"] == digest(HERE/"gaussian.py") and report["comparison"]["passed"] is True,
                "independent_comparison_binding_mismatch")
    require(report["bindings"] == expected_bindings, "independent_source_binding_mismatch")
    bindings.update(expected_bindings)


@lru_cache(maxsize=2)
def fresh_science(fingerprint):
    primary, independent = (implementation(HERE/name) for name in PROGRAMS)
    return primary.generate(), independent.compute(), independent


def lean_certification(bindings):
    receipt = json.loads((HERE/"certification.json").read_text())
    require(receipt["schema"] == "p23-gaussian-window-lean-certification/v1" and receipt["status"] == "certified" and
            receipt["criterion_freeze"]["commit"] == FREEZE, "missing_source_Lean_certification")
    require(all(receipt[k] is False for k in IDENTITY) and
            receipt["kernel_claims"] == {"source_normalization":True,"count_pgf":True,"coherent_effect_tail":True,
              "concrete_gamma_symtensor":False,"gaussian_vacuum_formula":False,"window_PGF_equals_Born":False},
            "Lean_scope_changed")
    _,required_bindings,_,_ = scientific_inputs()
    required_bindings.update({relative(path):digest(path) for path in (*LEAN_CHAIN,ROOT/"Lean/lean-toolchain",ROOT/"Lean/lake-manifest.json")})
    require(receipt["bindings"] == required_bindings, "incomplete_source_Lean_bindings")
    focused = receipt["focused_verification"]
    require(focused["fresh_source_compilation"] is True and type(focused["trust_level"]) is int and focused["trust_level"] == 0 and
            focused["warning_as_error"] is True and [row["source"] for row in focused["commands"]] == [relative(path) for path in LEAN_CHAIN] and
            all(type(row["exit_code"]) is int and row["exit_code"] == 0 and row["command"][1:3] == ["--trust=0","-DwarningAsError=true"]
                for row in focused["commands"]), "invalid_source_Lean_compile_receipt")
    require([row["file"] for row in focused["lsp"]] == [path.name for path in LEAN_CHAIN] and
            all(row["errors"] == row["warnings"] == 0 for row in focused["lsp"]), "invalid_source_Lean_LSP_receipt")
    for path in LEAN_CHAIN:
        row = receipt["execution_source_freezes"][relative(path)]
        require(row["sha256"] == digest(path), "source_Lean_execution_binding_mismatch")
        frozen_file(path,row["commit"])
        subprocess.run(["git","merge-base","--is-ancestor",FREEZE,row["commit"]],cwd=ROOT,check=True)
    require(receipt["authorized_axioms"] == ["propext","Classical.choice","Quot.sound"] and
            receipt["source_audit"]["target_probability_or_PGF_in_primitive"] is False and
            receipt["source_audit"]["operational_root_in_closure"] is False, "unauthorized_source_Lean_trust")
    bindings.update(required_bindings)
    bindings[relative(HERE/"certification.json")] = digest(HERE/"certification.json")


def assess(report_dir=None, *, enabled=True):
    base = {"schema":SCHEMA,"version":VERSION,"evidence_valid":False,**{k:False for k in IDENTITY},
            "private_optimizer_input_required":False,"bell_event_files_read":0,"retrospective":True}
    if not enabled:
        return {**base,"status":"disabled_by_override"}
    directory = HERE if report_dir is None else Path(report_dir)
    try:
        spec,bindings,seed,confidence = scientific_inputs()
        freezes = {relative(HERE/name):program_freeze(HERE/name) for name in (*PROGRAMS,"verify.py","tests.py")}
        lean_certification(bindings)
        files = [directory/PRIMARY,directory/INDEPENDENT]
        hashes = list(map(digest,files))
        main,own = (json.loads(path.read_text()) for path in files)
        require(main["schema"] == "p23-gaussian-window-primary/v1" and own["schema"] == "p23-gaussian-window-independent-fock/v1" and
                main["version"] == own["version"] == VERSION, "schema_or_revision_mismatch")
        for report in (main,own):
            require(all(report[k] is False for k in IDENTITY) and report["retrospective"] is True and
                    type(report["bell_event_files_read"]) is int and report["bell_event_files_read"] == 0,
                    "conditional_source_cannot_admit_identity")
        require(main["private_optimizer_input_required"] is False and main["criterion_sha256"] == digest(HERE/"criterion.md") and
                main["sources_sha256"] == digest(HERE/"sources.json") and main["program_sha256"] == digest(HERE/"gaussian.py") and
                main["interval_source_sha256"] == digest(INTERVAL_SOURCE) and main["seed_sha256"] == digest((HERE/spec["seed_report"]).resolve()),
                "primary_source_binding_mismatch")
        fresh_main,fresh_own,module = fresh_science(tuple(sorted({**bindings,**{k:v["sha256"] for k,v in freezes.items()}}.items())))
        require(same_structure(main,fresh_main), "primary_recomputation_mismatch")
        verify_independent_snapshot(own,module,bindings,hashes[0])
        for name in ("schema","version","status","calibration_seed","source_parameters","candidate","controls","arithmetic",
                     "public_probabilities","confidence_inclusion","outcome","cutoff_tail","prefix",
                     "primitive","tail_role","other_implementation_output_used_as_input"):
            require(same_structure(own[name],fresh_own[name]), "independent_recomputation_mismatch:"+name)
        rows,inclusion,primary_outcome = validate_primary(main,spec,seed,confidence)
        independent_result = validate_independent(own,main,rows,spec,seed,confidence)
        require(list(map(digest,files)) == hashes, "evidence_changed_during_verification")
        contained = all(all(v) for v in inclusion.values()) and independent_result["all_public_enclosures_contained"]
        return {**base,"status":"verified","evidence_valid":True,"criterion_freeze":{"commit":FREEZE,
                "criterion_sha256":digest(HERE/"criterion.md"),"sources_sha256":digest(HERE/"sources.json")},
                "execution_source_freezes":freezes,"primary_source_controls":180,"control_cells":720,
                "primary_outcome":primary_outcome,"independent_outcome":independent_result["outcome"],
                "outcome":"EXHIBITED_FULL_FOCK_WINDOW_MEMBER" if contained else "NOT_CERTIFIED_BY_ENCLOSURE",
                "all_public_enclosures_contained":contained,"source_Born_matrices_recomputed":True,
                "unnormalized_sector_prefix_and_exact_tail_recomputed":True,"public_statistical_contract":"p23-public-observables-po0003",
                "Lean_scope":"source normalization/PGF/factorial moments and coherent legal-effect Born tail; concrete Gamma, Gaussian vacuum and window equality are numerical consumers",
                "numeric_controls":independent_result["numeric_controls"],
                "bindings":{**bindings,**{k:v["sha256"] for k,v in freezes.items()},PRIMARY:hashes[0],INDEPENDENT:hashes[1]}}
    except FileNotFoundError as error:
        return {**base,"status":"missing_gaussian_window_evidence","reason":str(error)}
    except (ValueError,KeyError,TypeError,IndexError,AttributeError,ArithmeticError,ImportError,OSError,subprocess.SubprocessError,StopIteration) as error:
        return {**base,"status":"invalid_gaussian_window_evidence","reason":str(error)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only",action="store_true")
    parser.add_argument("--directory",type=Path)
    parser.add_argument("--disabled",action="store_true")
    args = parser.parse_args()
    result = assess(args.directory,enabled=not args.disabled)
    print(json.dumps(result,indent=2,allow_nan=False))
    return 0 if result["status"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
