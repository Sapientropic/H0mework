"""Single-only source construction and independent coherent Fock prediction."""
from __future__ import annotations

import argparse
import copy
import functools
import hashlib
import importlib.util
import json
import re
import subprocess
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
FREEZE = "435305719b"
OUTPUT = HERE/"independent.json"
FLAGS = ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
         "actual_window_model_identified", "calibration_protocol_identified", "noise_channel_identified",
         "source_pair_rate_reference_identified")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def criterion_freeze():
    commit = subprocess.check_output(["git", "rev-parse", FREEZE], cwd=ROOT, text=True).strip()
    for name in ("criterion.md", "sources.json"):
        path = HERE/name
        relative = str(path.relative_to(ROOT))
        if subprocess.check_output(["git", "show", commit+":"+relative], cwd=ROOT) != path.read_bytes():
            raise ValueError("frozen source contract changed: "+name)
    subprocess.check_call(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT)
    return {"commit": commit, "criterion_sha256": digest(HERE/"criterion.md"), "sources_sha256": digest(HERE/"sources.json")}


def executable_freeze():
    path = Path(__file__).resolve()
    relative = str(path.relative_to(ROOT))
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative], cwd=ROOT, text=True).strip()
    if not commit or subprocess.check_output(["git", "show", commit+":"+relative], cwd=ROOT) != path.read_bytes():
        raise ValueError("commit the independent source constructor before its first calculation")
    subprocess.check_call(["git", "merge-base", "--is-ancestor", FREEZE, commit], cwd=ROOT)
    return {"commit": commit, "program_sha256": digest(path)}


def identity_flags(spec):
    for name in FLAGS:
        if type(spec[name]) is not bool:
            raise TypeError("identity/proof flags must be actual booleans: "+name)
        if spec[name] is not False:
            raise ValueError("the frozen conditional model does not authorize an actual identity: "+name)
    return {name: False for name in FLAGS}


def load_frozen():
    criterion_freeze()
    blocks = re.findall(r"```json\s*(.*?)\s*```", (HERE/"criterion.md").read_text(), re.S)
    if len(blocks) != 1:
        raise ValueError("the calibrated-window contract has one JSON block")
    spec = json.loads(blocks[0])
    sources = json.loads((HERE/"sources.json").read_text())
    bound = {}
    for item in sources["inputs"]:
        if digest(ROOT/item["path"]) != item["sha256"]:
            raise ValueError("source input binding changed: "+item["path"])
        bound[item["path"]] = item["sha256"]
    for path in (HERE/"criterion.md", HERE/"sources.json", Path(__file__).resolve()):
        bound[str(path.relative_to(ROOT))] = digest(path)
    for commit in sources["prior_source_contracts"]:
        subprocess.check_call(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT)
    old_blocks = re.findall(r"```json\s*(.*?)\s*```", (HERE/"../gaussian-window/criterion.md").resolve().read_text(), re.S)
    gw = json.loads(old_blocks[0])
    if (spec["training_rows"] != [0, 3] or spec["source_grid_digits"] != 15
            or spec["root_precision_digits"] != 40 or spec["window_pulses"] != 5
            or spec["source_pair_cutoff"] != gw["source_pair_cutoff"]
            or spec["independent_terms"] != gw["independent_terms"]
            or spec["independent_precision_digits"] != gw["independent_precision_digits"]):
        raise ValueError("independent calculation differs from the frozen contract")
    identity_flags(spec)
    spec["pi"] = gw["pi"]
    spec["bindings"] = bound
    return spec


@functools.lru_cache(maxsize=1)
def fock_module():
    path = (HERE/"../gaussian-window/independent_fock.py").resolve()
    loader = importlib.util.spec_from_file_location("cb0001_coherent_fock", path)
    module = importlib.util.module_from_spec(loader)
    loader.loader.exec_module(module)
    return module


def training_single_view(public):
    result = []
    for index in (0, 3):
        row = public["counts"][index]
        if len(row) != 4 or any(type(x) is not int or x < 0 for x in row):
            raise ValueError("invalid declared training row")
        denominator = sum(row)
        if denominator == 0:
            raise ValueError("zero training-row denominator")
        result.append({"row_index": index, "row_denominator": denominator,
                       "alice_single": F(row[0]+row[1], denominator),
                       "bob_single": F(row[0]+row[2], denominator)})
    return result


def fifth_root(value, digits=40):
    value = F(value)
    if not 0 < value <= 1:
        raise ValueError("fifth-root input must be a positive non-click probability")
    scale = 10**digits
    integer = value.numerator*scale**5//value.denominator
    lo, hi = 0, scale+1
    while lo+1 < hi:
        mid = (lo+hi)//2
        if mid**5 <= integer:
            lo = mid
        else:
            hi = mid
    lower = F(lo, scale)
    upper = lower if lo**5*value.denominator == value.numerator*scale**5 else F(lo+1, scale)
    return lower, upper


def unique_nearest_grid(interval, digits=15):
    scale = 10**digits
    def nearest(x):
        shifted = x*scale+F(1, 2)
        return shifted.numerator//shifted.denominator
    low, high = nearest(interval.lo), nearest(interval.hi)
    if low != high:
        raise ValueError("SOURCE_GRID_NOT_UNIQUE")
    point = F(low, scale)
    if not point-F(1, 2*scale) < interval.lo <= interval.hi < point+F(1, 2*scale):
        raise ValueError("SOURCE_GRID_NEAREST_TIE")
    if not 0 <= point < 1:
        raise ValueError("SOURCE_GRID_OUTSIDE_GEOMETRIC_DOMAIN")
    return point


def construct_source(training, spec):
    if len(training) != 2 or [x["row_index"] for x in training] != [0, 3]:
        raise ValueError("only the two declared single-marginal training rows are accepted")
    fock = fock_module()
    I = fock.Interval
    eta = list(map(F, spec["eta_center"]))
    background = list(map(F, spec["background_per_pulse"]))
    means, roots, u = [], [], []
    for row in training:
        row_mean, row_roots = [], []
        for side, b in zip(("alice", "bob"), background):
            probability = row[side+"_single"]
            if not 0 <= probability < 1:
                raise ValueError("invalid training marginal")
            lower, upper = fifth_root(1-probability, spec["root_precision_digits"])
            row_roots.append({"exact_lower": str(lower), "exact_upper": str(upper)})
            row_mean.append((1-b)/I(lower, upper)-1)
        means.append(row_mean); roots.append(row_roots)
        u.append((row_mean[0]/eta[0]+row_mean[1]/eta[1])/2)
    angles = [F(spec["angles_deg"][0]), abs(F(spec["angles_deg"][1]))]
    sine_squared = [fock.trigonometry(angle, F(spec["pi"][0]), F(spec["pi"][1]))[0]**2 for angle in angles]
    d = sine_squared[1]-sine_squared[0]
    if d.lo <= 0:
        raise ValueError("training-angle inverse is not strictly nonsingular")
    difference = (u[1]-u[0])/d
    nv = u[0]-sine_squared[0]*difference
    nh = nv+difference
    if nh.lo < 0 or nv.lo < 0:
        raise ValueError("NEGATIVE_SOURCE_MEAN")
    intervals = [nh/(1+nh), nv/(1+nv)]
    points = [unique_nearest_grid(x, spec["source_grid_digits"]) for x in intervals]
    packet = {"geometric_ratio": list(map(str, points)), "transmission_A": [str(eta[0])]*2,
              "transmission_B": [str(eta[1])]*2}
    trace = {"training": [{key: str(value) if isinstance(value, F) else value for key, value in row.items()} for row in training],
             "fifth_root_enclosures": roots, "mean_enclosures": [[x.json() for x in row] for row in means],
             "u_enclosures": [x.json() for x in u], "sin_squared": [x.json() for x in sine_squared],
             "inverse_denominator": d.json(), "n_H": nh.json(), "n_V": nv.json(),
             "raw_ratio_enclosures_before_grid": [x.json() for x in intervals],
             "unique_nearest_grid_points": list(map(str, points)), "source_grid_digits": spec["source_grid_digits"],
             "joint_statistics_used": False, "rows_01_10_used": False, "global_N_used": False,
             "CI_used": False, "documented_optimum_or_q_used": False}
    return packet, trace


def exact_json(value):
    return {"exact": str(value), "value": float(value)}


def calibration_recipe(spec):
    n = F(spec["calibration_geometric_ratio"])/(1-F(spec["calibration_geometric_ratio"]))
    a, b = map(F, spec["eta_center"])
    u = a+b-a*b
    single_a, single_b = n*a/(1+n*a), n*b/(1+n*b)
    joint_plus = 1-1/(1+n*a)-1/(1+n*b)+1/(1+n*u)
    joint_minus = single_a*single_b
    base = (joint_plus-joint_minus)/(joint_plus+joint_minus)
    lam = (1-F(spec["visibility_DA_center"])/base)/2
    if not 0 <= lam <= 1:
        raise ValueError("INVALID_PHASE_FLIP_PROBABILITY")
    D, K = (1+n*a)*(1+n*b), n*(1+n)*a*b
    lhs, rhs = (1-lam)*(D-K)**2, lam*D**2
    return lam, {"Jplus": exact_json(joint_plus), "Jminus": exact_json(joint_minus),
                 "Vbase": exact_json(base), "phase_flip_probability": exact_json(lam),
                 "full_DA_fringe_monotonicity": {"variable": "x=cos²(Alice_angle−45°) in [0,1]",
                     "lhs": exact_json(lhs), "rhs": exact_json(rhs), "holds": lhs >= rhs,
                     "role": "exact arithmetic condition in the frozen full-fringe contract"}}


def phase_packet(packet, cosine):
    return {**packet, "phase_cos": {"numerator": str(F(cosine)), "sqrt_denominator": "1"}}


def phase_pulses(packet, a, b, spec):
    fock = fock_module()
    return [fock.pulse_noclick(phase_packet(packet, cosine), F(a), F(b), spec) for cosine in (1, -1)]


def mixed_pulse(phases, lam):
    if not 0 <= lam <= 1 or phases[0]["mass"] != phases[1]["mass"] or phases[0]["tail"] != phases[1]["tail"]:
        raise ValueError("phase components do not share the same normalized source number law")
    weights = [1-lam, lam]
    return {"full": {key: sum((weight*phase["full"][key] for weight, phase in zip(weights, phases)), fock_module().Interval(0)).intersect(0, 1)
                     for key in ("P0A", "P0B", "P00")},
            "mass": phases[0]["mass"], "tail": phases[0]["tail"]}


def forward(packet, lam, a, b, window, background, spec):
    phases = phase_pulses(packet, a, b, spec)
    pulse = mixed_pulse(phases, lam)
    rates = fock_module().window_rates(pulse, window, background)
    return {"phases": phases, "mixed": pulse, **rates}


def subset(interval, bounds):
    return F(bounds[0]) <= interval.lo and interval.hi <= F(bounds[1])


def calibration_checks(spec, lam, recipe):
    fock = fock_module()
    a, b = map(F, spec["eta_center"])
    t = F(spec["calibration_geometric_ratio"])
    packet = {"geometric_ratio": [str(t)]*2, "transmission_A": [str(a)]*2, "transmission_B": [str(b)]*2}
    comparisons = {}
    all_passed = recipe["full_DA_fringe_monotonicity"]["holds"]
    for name, high_angle, low_angle, bob in (("HV", 0, 90, 0), ("DA", 45, -45, 45)):
        high = forward(packet, lam, high_angle, bob, 1, [0, 0], spec)["signal"]["j"]
        low = forward(packet, lam, low_angle, bob, 1, [0, 0], spec)["signal"]["j"]
        visibility = (high-low)/(high+low)
        inside = subset(visibility, spec["visibility_"+name+"_interval"])
        target = F(recipe["Vbase"]["exact"]) if name == "HV" else F(spec["visibility_DA_center"])
        exact_enclosed = visibility.contains(target)
        comparisons[name] = {"maximum_joint": high.json(), "minimum_joint": low.json(), "visibility": visibility.json(),
                             "published_interval_containment": inside, "source_exact_visibility_enclosed": exact_enclosed}
        all_passed &= inside and exact_enclosed
    pure = {**packet, "geometric_ratio": [str(t), "0"]}
    matched = forward(pure, lam, 90, 90, 1, [0, 0], spec)["signal"]
    n, u = t/(1-t), a+b-a*b
    half = F(spec["eta_probability_half_width"])
    klyshko = {}
    for name, ta, tb, herald in (("alice", a, b, matched["sB"]), ("bob", b, a, matched["sA"])):
        exact = 1-(1-ta)*(1+n*tb)/((1+n*ta)*(1+n*u))
        interval = (matched["j"]/herald).intersect(0, 1)
        inside = subset(interval, (ta-half, ta+half))
        bound = 0 <= exact-ta <= 2*n
        enclosed = interval.contains(exact)
        klyshko[name] = {"value": interval.json(), "source_exact": exact_json(exact), "inflation": exact_json(exact-ta),
                         "upper_inflation_bound": str(2*n), "published_interval_containment": inside,
                         "exact_enclosed": enclosed, "inflation_bound_holds": bound}
        all_passed &= inside and bound and enclosed
    return {"recipe": recipe, "visibility": comparisons, "matched_Klyshko": klyshko, "passed": bool(all_passed),
            "calibration_protocol_identified": False, "noise_channel_identified": False}


def predictions(packet, lam, spec):
    angles = list(map(F, spec["angles_deg"]))
    public, signal = ({key: [] for key in ("j", "sA_cell", "sB_cell")} for _ in range(2))
    internals = []
    for ai, bi in ((0, 0), (0, 1), (1, 0), (1, 1)):
        result = forward(packet, lam, angles[ai], angles[2+bi], spec["window_pulses"], spec["background_per_pulse"], spec)
        for key, field in (("j", "j"), ("sA_cell", "sA"), ("sB_cell", "sB")):
            public[key].append(result["observed"][field].json())
            signal[key].append(result["signal"][field].json())
        internals.append(result)
    return public, signal, internals


def validate_confidence(confidence, frozen):
    if confidence != frozen:
        raise ValueError("the frozen confidence domain cannot be weakened or replaced")
    for key in ("j", "sA_cell", "sB_cell"):
        if len(confidence[key]) != 4:
            raise ValueError("the simultaneous confidence domain has exactly twelve components")


def controls(public_counts, training, packet, lam, spec, internals, confidence):
    fock = fock_module()
    same_joint = copy.deepcopy(public_counts)
    for index in (0, 3):
        row = same_joint["counts"][index]
        for offset, change in enumerate((1, -1, -1, 1)):
            row[offset] += change
    changed_unused = copy.deepcopy(public_counts)
    changed_unused["counts"][1] = [999, 123, 456, 789]
    changed_unused["counts"][2] = [321, 654, 987, 111]
    changed_unused["global_N"] = 1
    joint_training = training_single_view(same_joint)
    unused_training = training_single_view(changed_unused)
    joint_packet, _ = construct_source(joint_training, spec)
    unused_packet, _ = construct_source(unused_training, spec)
    phase_marginals = all(phases[0]["full"][side].lo == phases[1]["full"][side].lo
                          and phases[0]["full"][side].hi == phases[1]["full"][side].hi
                          for result in internals for phases in (result["phases"],) for side in ("P0A", "P0B"))
    last = internals[3]
    phase_window = [fock.window_rates(pulse, spec["window_pulses"], spec["background_per_pulse"])["observed"]["j"] for pulse in last["phases"]]
    wrong = (1-lam)*phase_window[0]+lam*phase_window[1]
    right = last["observed"]["j"]
    mixture_gap = wrong-right
    t = F(spec["calibration_geometric_ratio"])
    a, b = map(F, spec["eta_center"])
    balanced = {"geometric_ratio": [str(t)]*2, "transmission_A": [str(a)]*2, "transmission_B": [str(b)]*2}
    endpoints = forward(balanced, F(1, 2), 45, 45, 1, [0, 0], spec)["signal"]["j"]
    middle = forward(balanced, F(1, 2), 0, 45, 1, [0, 0], spec)["signal"]["j"]
    opposite = forward(balanced, F(1, 2), -45, 45, 1, [0, 0], spec)["signal"]["j"]
    n = t/(1-t); D = (1+n*a)*(1+n*b); K = n*(1+n)*a*b
    checks = {"changed_training_joint_preserves_four_single_view": joint_training == training,
              "changed_training_joint_preserves_raw_source": joint_packet == packet,
              "changed_entire_01_10_and_global_N_preserves_four_single_view": unused_training == training,
              "changed_entire_01_10_and_global_N_preserves_raw_source": unused_packet == packet,
              "source_phase_does_not_change_single_marginals": phase_marginals,
              "window_after_phase_mixture_rejected": mixture_gap.lo > 0,
              "half_flip_equal_endpoints": max(endpoints.lo, opposite.lo) <= min(endpoints.hi, opposite.hi),
              "half_flip_endpoint_zero_not_complete_visibility": endpoints.lo > middle.hi,
              "half_flip_fails_full_fringe_monotonicity": F(1, 2)*(D-K)**2 < F(1, 2)*D**2}
    simple_cases = []
    for ratios, transmission in (([0, 0], [1, 1, 1, 1]), ([t, t], [0, 0, 0, 0]), ([t, 0], [1, 1, 1, 1])):
        source = {"geometric_ratio": list(map(str, ratios)), "transmission_A": list(map(str, transmission[:2])),
                  "transmission_B": list(map(str, transmission[2:]))}
        for probability in (F(0), F(1, 2)):
            value = forward(source, probability, 90, 90, 1, [0, 0], spec)
            expected = F(0) if sum(ratios) == 0 or sum(transmission) == 0 else t
            simple_cases.append(all(value["signal"][key].contains(expected) for key in ("sA", "sB", "j")))
    checks["vacuum_zero_unit_loss_lambda_controls"] = all(simple_cases)
    pure = {"geometric_ratio": [str(t), "0"], "transmission_A": ["1", "1"], "transmission_B": ["1", "1"]}
    pure_prefix = fock.pulse_noclick(phase_packet(pure, 1), 90, 90, spec)
    normalized = pure_prefix["partial"]["P0A"]/pure_prefix["mass"]
    checks["source_prefix_renormalization_rejected"] = not normalized.contains(1-t)
    checks["omitted_source_number_tail_rejected"] = pure_prefix["tail"] > 0 and pure_prefix["mass"] < 1
    forged = dict(spec); forged["calibration_protocol_identified"] = True
    try:
        identity_flags(forged)
        checks["fake_calibration_identity_rejected"] = False
    except ValueError:
        checks["fake_calibration_identity_rejected"] = True
    forged = dict(spec); forged["calibration_protocol_identified"] = 1
    try:
        identity_flags(forged)
        checks["integer_not_proof_boolean"] = False
    except TypeError:
        checks["integer_not_proof_boolean"] = True
    widened = copy.deepcopy(confidence)
    widened["j"][0]["exact_lower"], widened["j"][0]["exact_upper"] = "0", "1"
    try:
        validate_confidence(widened, confidence)
        checks["confidence_widening_rejected"] = False
    except ValueError:
        checks["confidence_widening_rejected"] = True
    return {"checks": checks, "passed": all(checks.values()), "wrong_window_mixture_gain": mixture_gap.json(),
            "half_flip_complete_fringe_curvature": (endpoints-middle).json(), "simple_control_count": len(simple_cases)}


def posterior_diagnostics(packet):
    fock = fock_module()
    th, tv = map(F, packet["geometric_ratio"])
    return {"pair_at_least_one": exact_json(th+tv-th*tv), "exactly_one": exact_json((1-th)*(1-tv)*(th+tv)),
            "mean_pair": exact_json(th/(1-th)+tv/(1-tv)),
            "one_pair_amplitude_ratio": fock.sqrt_endpoint(tv/th).json() if th else None,
            "public_pair_approximation": "0.0005", "public_pair_acceptance_interval": None,
            "printed_amplitude_ratio": "276/961", "role": "post-prediction diagnostics; none entered source construction"}


def compute():
    spec = load_frozen()
    program = executable_freeze()
    public_counts = json.loads((HERE/spec["public_counts"]).resolve().read_text())
    try:
        training = training_single_view(public_counts)
        packet, construction = construct_source(training, spec)
        lam, recipe = calibration_recipe(spec)
    except ValueError as error:
        return {"schema": "p23-calibrated-window-independent/v1", "version": spec["version"],
                "criterion_freeze": criterion_freeze(), "executable_freeze": program, "bindings": spec["bindings"],
                "status": "FAIL", "outcome": "SOURCE_CONSTRUCTION_FAILED", "reason": str(error),
                "joint_statistics_used_to_construct_source": False, "bell_event_files_read": 0,
                "retrospective": True, **identity_flags(spec)}
    calibration = calibration_checks(spec, lam, recipe)
    public, signal, internals = predictions(packet, lam, spec)
    # The held-out statistical domain is first consumed after the source and all predictions exist.
    confidence_path = (HERE/spec["public_confidence_report"]).resolve()
    confidence = json.loads(confidence_path.read_text())["common_mean_confidence"]
    validate_confidence(confidence, confidence)
    inclusion = {key: [F(bound["exact_lower"]) <= F(value["exact_lower"]) and F(value["exact_upper"]) <= F(bound["exact_upper"])
                      for value, bound in zip(public[key], confidence[key])] for key in public}
    control = controls(public_counts, training, packet, lam, spec, internals, confidence)
    exhibited = calibration["passed"] and control["passed"] and all(all(values) for values in inclusion.values())
    prefixes = [{"mass": str(result["mixed"]["mass"]), "tail": str(result["mixed"]["tail"]),
                 "phase_prefixes": [fock_module().pulse_json(pulse) for pulse in result["phases"]],
                 "mixed_single_pulse_no_click": {key: value.json() for key, value in result["mixed"]["full"].items()}}
                for result in internals]
    return {"schema": "p23-calibrated-window-independent/v1", "version": spec["version"],
            "criterion_freeze": criterion_freeze(), "executable_freeze": program, "bindings": spec["bindings"],
            "status": "PASS" if calibration["passed"] and control["passed"] else "FAIL",
            "outcome": "EXHIBITED_PUBLICLY_CALIBRATED_WINDOW_MEMBER" if exhibited else "NOT_CERTIFIED_BY_ENCLOSURE",
            "source_parameters": packet, "phase_flip_probability": exact_json(lam), "source_construction": construction,
            "calibration": calibration, "public_probabilities": public, "signal_probabilities": signal,
            "confidence_inclusion": inclusion, "coherent_phase_prefixes": prefixes, "controls": control,
            "posterior_diagnostics": posterior_diagnostics(packet),
            "arithmetic": {"fifth_root_digits": spec["root_precision_digits"], "source_grid_digits": spec["source_grid_digits"],
                           "independent_interval_digits": spec["independent_precision_digits"], "coherent_Taylor_terms": spec["independent_terms"],
                           "pi": spec["pi"], "source_pair_cutoff": spec["source_pair_cutoff"]},
            "probability_primitive": "bound coherent Fock number-amplitude/Γ(E) source; phase no-click mixtures precede every independent-pulse power",
            "other_implementation_output_used_as_input": False, "joint_statistics_used_to_construct_source": False,
            "private_optimizer_input_required": False, "bell_event_files_read": 0, "retrospective": True, **identity_flags(spec)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = compute()
    if not args.check_only:
        OUTPUT.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": result["status"], "outcome": result["outcome"], "confidence_inclusion": result.get("confidence_inclusion"),
                      "calibration_passed": result.get("calibration", {}).get("passed"),
                      "controls": result.get("controls", {}).get("checks"), "reason": result.get("reason")}))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
