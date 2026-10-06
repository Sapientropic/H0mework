"""Inclusive TMSV bucket counts from number mass and loss weights."""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import subprocess
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
OUTPUT = HERE / "independent_count.json"
FREEZE = "d9ead286cf"
DIGITS = 30
SCALE = 10**DIGITS
UNDEFINED = "UNDEFINED_ZERO_HERALD"


def down(value):
    value = F(value)
    return F(value.numerator*SCALE//value.denominator, SCALE)


def up(value):
    return -down(-F(value))


class Interval:
    def __init__(self, lower, upper=None):
        self.lo = F(lower)
        self.hi = self.lo if upper is None else F(upper)
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @staticmethod
    def cast(value):
        return value if isinstance(value, Interval) else Interval(value)

    def __add__(self, other):
        other = self.cast(other)
        return Interval(down(self.lo+other.lo), up(self.hi+other.hi))

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self+-self.cast(other)

    def __rsub__(self, other):
        return self.cast(other)+-self

    def __mul__(self, other):
        other = self.cast(other)
        products = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(down(min(products)), up(max(products)))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        if other.lo <= 0 <= other.hi:
            raise ValueError("herald enclosure crosses zero")
        return self*Interval(down(1/other.hi), up(1/other.lo))

    def __pow__(self, exponent):
        if exponent < 0 or self.lo < 0:
            raise ValueError("only nonnegative probabilities and integer powers are used")
        return Interval(down(self.lo**exponent), up(self.hi**exponent))

    def intersect(self, lower, upper):
        return Interval(max(self.lo, F(lower)), min(self.hi, F(upper)))

    def contains(self, value):
        return self.lo <= F(value) <= self.hi

    def json(self):
        return {"exact_lower": str(self.lo), "exact_upper": str(self.hi),
                "lower": float(self.lo), "upper": float(self.hi)}


def exact_json(value):
    return {"exact": str(value), "value": float(value)}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def criterion_freeze():
    commit = subprocess.check_output(["git", "rev-parse", FREEZE], cwd=ROOT, text=True).strip()
    for name in ("criterion.md", "sources.json"):
        path = HERE/name
        committed = subprocess.check_output(["git", "show", commit+":"+str(path.relative_to(ROOT))], cwd=ROOT)
        if committed != path.read_bytes():
            raise ValueError("frozen calibration input changed: "+name)
    subprocess.check_call(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT)
    return {"commit": commit, "criterion_sha256": digest(HERE/"criterion.md"),
            "sources_sha256": digest(HERE/"sources.json")}


def executable_freeze():
    path = Path(__file__).resolve()
    relative = str(path.relative_to(ROOT))
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative], cwd=ROOT, text=True).strip()
    if not commit or subprocess.check_output(["git", "show", commit+":"+relative], cwd=ROOT) != path.read_bytes():
        raise ValueError("freeze the complete independent executable before its first calculation")
    subprocess.check_call(["git", "merge-base", "--is-ancestor", FREEZE, commit], cwd=ROOT)
    return {"commit": commit, "program_sha256": digest(path)}


def load_frozen():
    criterion_freeze()
    sources = json.loads((HERE/"sources.json").read_text())
    bound = {}
    for item in sources["inputs"]:
        if digest(ROOT/item["path"]) != item["sha256"]:
            raise ValueError("source binding changed: "+item["path"])
        bound[item["path"]] = item["sha256"]
    subprocess.check_call(["git", "merge-base", "--is-ancestor", sources["parent_result_commit"], "HEAD"], cwd=ROOT)
    gw_text = (HERE/"../gaussian-window/criterion.md").resolve().read_text()
    blocks = re.findall(r"```json\s*(.*?)\s*```", gw_text, re.S)
    if len(blocks) != 1:
        raise ValueError("the bound Gaussian specification has one JSON block")
    gw = json.loads(blocks[0])
    text = (HERE/"criterion.md").read_text()
    cutoff = re.search(r"h\+v≤(\d+)", text)
    eta = {}
    for side in ("A", "B"):
        match = re.search(r"η"+side+r"∈\[([0-9.]+),([0-9.]+)\]", text)
        if match is None:
            raise ValueError("missing public efficiency interval")
        eta[side] = list(map(F, match.groups()))
    if cutoff is None or int(cutoff[1]) != gw["source_pair_cutoff"] or gw["independent_precision_digits"] != DIGITS:
        raise ValueError("number cutoff/precision differs from the frozen source specification")
    if gw["controls"]["windows"] != [1, 5]:
        raise ValueError("the calibration contract uses one and five fresh slots")
    bound[str((HERE/"criterion.md").relative_to(ROOT))] = digest(HERE/"criterion.md")
    bound[str((HERE/"sources.json").relative_to(ROOT))] = digest(HERE/"sources.json")
    bound[str(Path(__file__).resolve().relative_to(ROOT))] = digest(Path(__file__))
    return {"version": sources["version"], "cutoff": int(cutoff[1]), "eta": eta, "gw": gw,
            "bindings": bound, "roles": sources}


def source_parameters(ratios, transmissions, phase=None):
    if len(ratios) != 2 or len(transmissions) != 4:
        raise ValueError("two polarizations and two loss arms are required")
    packet = {"geometric_ratio": [str(F(x)) for x in ratios],
              "transmission_A": [str(F(x)) for x in transmissions[:2]],
              "transmission_B": [str(F(x)) for x in transmissions[2:]],
              "phase_cos": phase or {"numerator": "1", "sqrt_denominator": "1"}}
    unpack_source(packet)
    return packet


def unpack_source(packet):
    ratios = list(map(F, packet["geometric_ratio"]))
    alice, bob = (list(map(F, packet["transmission_"+side])) for side in ("A", "B"))
    if len(ratios) != 2 or len(alice) != 2 or len(bob) != 2:
        raise ValueError("wrong number of source/loss modes")
    if any(not 0 <= x < 1 for x in ratios) or any(not 0 <= x <= 1 for x in alice+bob):
        raise ValueError("invalid source ratio or actual transmission")
    numerator = F(packet["phase_cos"]["numerator"])
    radicand = F(packet["phase_cos"]["sqrt_denominator"])
    if radicand <= 0 or numerator*numerator > radicand:
        raise ValueError("invalid source phase parameter")
    return ratios, alice, bob


def lift_seed(spec):
    report_path = (HERE/"../gaussian-window"/spec["gw"]["seed_report"]).resolve()
    report = json.loads(report_path.read_text())
    branch = next(x for x in report["branches"] if x["model"] == spec["gw"]["seed_model"])
    seed = {key: F(value) for key, value in branch["source_member"]["statistics"].items()}
    N = F(spec["gw"]["window_pulses"])
    ratios, alice, bob, identities = [], [], [], {}
    for pol in ("H", "V"):
        A, B, L = seed["A"+pol], seed["B"+pol], seed[pol]
        denominator = N*L-A*B
        if min(A, B, L, denominator) <= 0:
            raise ValueError("NO_VALID_CALIBRATION_SEED")
        n = A*B/denominator
        t = n/(1+n)
        ta, tb = denominator/(N*B), denominator/(N*A)
        if not 0 <= ta <= 1 or not 0 <= tb <= 1:
            raise ValueError("NO_VALID_CALIBRATION_SEED: transmission outside [0,1]")
        ratios.append(t); alice.append(ta); bob.append(tb)
        identities[pol] = {"N_n_TA": N*n*ta == A, "N_n_TB": N*n*tb == B,
                           "N_n_1plusn_TA_TB": N*n*(1+n)*ta*tb == L}
    phase = {"numerator": str(seed["X"]), "sqrt_denominator": str(seed["H"]*seed["V"])}
    packet = source_parameters(ratios, alice+bob, phase)
    return packet, {"model": spec["gw"]["seed_model"], "seed_sha256": digest(report_path),
                    "identities": identities, "role": "fixed source-construction seed; no private optimizer or held-out fitting"}


def source_moments(packet):
    (th, tv), _, _ = unpack_source(packet)
    return {"pair_at_least_one": th+tv-th*tv,
            "exactly_one": (1-th)*(1-tv)*(th+tv), "mean_pair": th/(1-th)+tv/(1-tv)}


def source_zero_to_arm(ratios, transmission):
    return all(t == 0 or eta == 0 for t, eta in zip(ratios, transmission))


def pulse_prefix(packet, cutoff=6):
    (th, tv), alice, bob = unpack_source(packet)
    normalization = (1-th)*(1-tv)
    mass = F(0)
    prefix = {"A0": F(0), "B0": F(0), "AB0": F(0)}
    for total in range(cutoff+1):
        for h in range(total+1):
            v = total-h
            number_mass = normalization*th**h*tv**v
            loss_a = (1-alice[0])**h*(1-alice[1])**v
            loss_b = (1-bob[0])**h*(1-bob[1])**v
            mass += number_mass
            prefix["A0"] += number_mass*loss_a
            prefix["B0"] += number_mass*loss_b
            prefix["AB0"] += number_mass*loss_a*loss_b
    tail = 1-mass
    if not 0 <= tail <= 1 or any(not 0 <= x <= mass for x in prefix.values()):
        raise ValueError("invalid original number mass or no-click prefix")
    zero_a = source_zero_to_arm((th, tv), alice)
    zero_b = source_zero_to_arm((th, tv), bob)
    tail_bounds = {key: Interval(0, tail) for key in prefix}
    # An identity no-click effect fixes its entire untouched-sector contribution.
    if zero_a:
        tail_bounds["A0"] = Interval(tail)
    if zero_b:
        tail_bounds["B0"] = Interval(tail)
    if zero_a and zero_b:
        tail_bounds["AB0"] = Interval(tail)
    full = {key: (Interval(value)+tail_bounds[key]).intersect(0, 1) for key, value in prefix.items()}
    return {"mass": mass, "tail": tail, "prefix": prefix, "tail_bounds": tail_bounds, "full": full,
            "zero_signal_A": zero_a, "zero_signal_B": zero_b}


def conditional_ratio(joint, herald, zero):
    if zero:
        return {"status": UNDEFINED, "reason": "the declared source/effect/background gives an exactly zero herald"}
    if herald.lo <= 0:
        return {"status": "UNRESOLVED_HERALD_ENCLOSURE", "reason": "the positive herald enclosure needs finer arithmetic"}
    return {"status": "DEFINED", "interval": (joint/herald).intersect(0, 1)}


def count_readout(packet, window, background, cutoff=6):
    if window not in (1, 5):
        raise ValueError("only the frozen one/five-slot windows are consumed")
    ba, bb = map(F, background)
    if not 0 <= ba <= 1 or not 0 <= bb <= 1:
        raise ValueError("invalid independent OR background")
    pulse = pulse_prefix(packet, cutoff)
    a0 = ((1-ba)*pulse["full"]["A0"])**window
    b0 = ((1-bb)*pulse["full"]["B0"])**window
    ab0 = ((1-ba)*(1-bb)*pulse["full"]["AB0"])**window
    zero_a = pulse["zero_signal_A"] and ba == 0
    zero_b = pulse["zero_signal_B"] and bb == 0
    sa = Interval(0) if zero_a else (1-a0).intersect(0, 1)
    sb = Interval(0) if zero_b else (1-b0).intersect(0, 1)
    joint = Interval(0) if zero_a or zero_b else (1-a0-b0+ab0).intersect(0, min(sa.hi, sb.hi))
    return {"pulse": pulse, "window_no_click": {"A0": a0, "B0": b0, "AB0": ab0},
            "rates": {"sA": sa, "sB": sb, "j": joint},
            "Klyshko": {"alice": conditional_ratio(joint, sb, zero_b),
                        "bob": conditional_ratio(joint, sa, zero_a)}}


def matched_exact(t, ta, tb):
    t, ta, tb = map(F, (t, ta, tb))
    if not 0 <= t < 1 or not 0 <= ta <= 1 or not 0 <= tb <= 1:
        raise ValueError("invalid matched-polarization source/effect")
    n = t/(1-t)
    u = ta+tb-ta*tb
    result = {"mean": n, "upper_inflation_bound": 2*n}
    for side, a, b in (("alice", ta, tb), ("bob", tb, ta)):
        if t == 0 or b == 0:
            result[side] = {"status": UNDEFINED}
        else:
            k = 1-(1-a)*(1+n*b)/((1+n*a)*(1+n*u))
            result[side] = {"status": "DEFINED", "value": k, "transmission": a,
                            "inflation": k-a, "bound_passed": 0 <= k-a <= 2*n}
    return result


def ratio_json(ratio):
    return {key: value.json() if isinstance(value, Interval) else value for key, value in ratio.items()}


def prefix_json(pulse):
    return {"mass": str(pulse["mass"]), "tail": str(pulse["tail"]),
            "prefix": {key: str(value) for key, value in pulse["prefix"].items()},
            "tail_contribution": {key: value.json() for key, value in pulse["tail_bounds"].items()},
            "full": {key: value.json() for key, value in pulse["full"].items()},
            "zero_signal_A": pulse["zero_signal_A"], "zero_signal_B": pulse["zero_signal_B"]}


def eta_intersection(ratio, bounds):
    if ratio["status"] != "DEFINED":
        return {"status": ratio["status"], "calibration_identity_identified": False}
    value = ratio["interval"]
    intersects = max(value.lo, bounds[0]) <= min(value.hi, bounds[1])
    return {"status": "INTERSECTS" if intersects else "DISJOINT", "public_interval": list(map(str, bounds)),
            "scope": "conditional on this exact declared calibration source, bucket port, window and background law",
            "calibration_identity_identified": False}


def preparations(packet):
    th, tv = packet["geometric_ratio"]
    return [("dual_pol", packet), ("pure_H", {**packet, "geometric_ratio": [th, "0"]}),
            ("pure_V", {**packet, "geometric_ratio": ["0", tv]})]


def candidate_rows(packet, spec):
    rows, sources = [], []
    for name, source in preparations(packet):
        ratios, alice, bob = unpack_source(source)
        sources.append({"preparation": name, "source_parameters": source,
                        "source_pair_readouts": {key: exact_json(value) for key, value in source_moments(source).items()},
                        "original_number_prefix": prefix_json(pulse_prefix(source, spec["cutoff"]))})
        for window, model in itertools.product((1, 5), ("signal_only", "independent_OR")):
            background = ["0", "0"] if model == "signal_only" else spec["gw"]["background_per_pulse"]
            readout = count_readout(source, window, background, spec["cutoff"])
            row = {"case_id": f"{name}/N{window}/{model}", "preparation": name, "window_pulses": window,
                   "background_model": model, "background_per_pulse": list(background),
                   "rates": {key: value.json() for key, value in readout["rates"].items()},
                   "Klyshko": {key: ratio_json(value) for key, value in readout["Klyshko"].items()},
                   "conditional_public_eta": {"alice": eta_intersection(readout["Klyshko"]["alice"], spec["eta"]["A"]),
                                              "bob": eta_intersection(readout["Klyshko"]["bob"], spec["eta"]["B"])}}
            if name != "dual_pol" and window == 1 and model == "signal_only":
                pol = 0 if name == "pure_H" else 1
                matched = matched_exact(ratios[pol], alice[pol], bob[pol])
                row["matched_single_polarization"] = {"mean": str(matched["mean"]), "upper_inflation_bound": str(matched["upper_inflation_bound"])}
                for side in ("alice", "bob"):
                    item = matched[side]
                    if item["status"] == "DEFINED":
                        enclosed = readout["Klyshko"][side]["interval"].contains(item["value"])
                        row["matched_single_polarization"][side] = {"status": "DEFINED", "K": exact_json(item["value"]),
                            "inflation": exact_json(item["inflation"]), "bound_passed": item["bound_passed"], "number_enclosed": enclosed}
                    else:
                        row["matched_single_polarization"][side] = item
            rows.append(row)
    return sources, rows


def source_controls(spec):
    controls = spec["gw"]["controls"]
    checks = {"original_number_mass_plus_tail": True, "positive_original_no_click_prefix": True,
              "bucket_probabilities_bounded": True, "conditional_ratios_bounded": True,
              "vacuum_or_zero_loss_readout": True, "zero_herald_explicitly_undefined": True,
              "matched_formula_enclosed_by_number_sum": True, "matched_inflation_bound": True}
    case_count = defined = undefined = 0
    worst_width = F(0)
    for ratios, transmission, window, model in itertools.product(controls["geometric_ratio_pairs"], controls["transmission_HV"],
                                                                 controls["windows"], ("signal_only", "independent_OR")):
        source = source_parameters(ratios, transmission)
        background = ["0", "0"] if model == "signal_only" else spec["gw"]["background_per_pulse"]
        result = count_readout(source, window, background, spec["cutoff"])
        pulse = result["pulse"]
        case_count += 1
        checks["original_number_mass_plus_tail"] &= pulse["mass"]+pulse["tail"] == 1
        checks["positive_original_no_click_prefix"] &= all(0 <= x <= pulse["mass"] for x in pulse["prefix"].values())
        for value in result["rates"].values():
            checks["bucket_probabilities_bounded"] &= 0 <= value.lo <= value.hi <= 1
            worst_width = max(worst_width, value.hi-value.lo)
        for ratio in result["Klyshko"].values():
            if ratio["status"] == "DEFINED":
                defined += 1
                value = ratio["interval"]
                checks["conditional_ratios_bounded"] &= 0 <= value.lo <= value.hi <= 1
                worst_width = max(worst_width, value.hi-value.lo)
            else:
                undefined += 1
                checks["zero_herald_explicitly_undefined"] &= ratio["status"] == UNDEFINED
        raw_ratios, alice, bob = unpack_source(source)
        if pulse["zero_signal_A"] and pulse["zero_signal_B"]:
            ba, bb = map(F, background)
            sa, sb = 1-(1-ba)**window, 1-(1-bb)**window
            checks["vacuum_or_zero_loss_readout"] &= all(result["rates"][key].contains(value) for key, value in (("sA", sa), ("sB", sb), ("j", sa*sb)))
        if window == 1 and model == "signal_only" and (raw_ratios[0] == 0 or raw_ratios[1] == 0):
            pol = 0 if raw_ratios[1] == 0 else 1
            matched = matched_exact(raw_ratios[pol], alice[pol], bob[pol])
            for side in ("alice", "bob"):
                item = matched[side]
                if item["status"] == "DEFINED":
                    checks["matched_formula_enclosed_by_number_sum"] &= result["Klyshko"][side]["status"] == "DEFINED" and result["Klyshko"][side]["interval"].contains(item["value"])
                    checks["matched_inflation_bound"] &= item["bound_passed"]
                else:
                    checks["zero_herald_explicitly_undefined"] &= result["Klyshko"][side]["status"] == UNDEFINED
    t = F(controls["geometric_ratio_pairs"][1][0])
    pure_h = source_parameters([t, 0], controls["transmission_HV"][0])
    pulse = pulse_prefix(pure_h, spec["cutoff"])
    normalized_prefix = Interval(pulse["prefix"]["A0"])/pulse["mass"]
    one = count_readout(pure_h, 1, [0, 0], spec["cutoff"])
    five = count_readout(pure_h, 5, [0, 0], spec["cutoff"])
    mixed_loss = list(map(F, controls["transmission_HV"][2]))
    matched = matched_exact(t, mixed_loss[0], mixed_loss[2])
    vacuum = source_parameters([0, 0], controls["transmission_HV"][0])
    vacuum_result = count_readout(vacuum, 1, [0, 0], spec["cutoff"])
    moments = source_moments(pure_h)
    checks.update({"omitted_number_tail_detected": pulse["tail"] > 0 and pulse["mass"] < 1,
                   "prefix_renormalization_detected": not normalized_prefix.contains(1-t),
                   "mean_not_at_least_one": moments["mean_pair"] > moments["pair_at_least_one"],
                   "zero_source_not_fake_transmission_efficiency": all(x["status"] == UNDEFINED for x in vacuum_result["Klyshko"].values()),
                   "pure_loss_not_exact_bucket_conditional_efficiency": matched["alice"]["value"] > mixed_loss[0],
                   "sum_of_window_pulse_counts_rejected": (5*one["rates"]["j"]).lo > five["rates"]["j"].hi,
                   "unbound_calibration_roles_do_not_admit_identity": all(spec["roles"][key] is False for key in (
                       "calibration_preparation_identified", "calibration_ports_identified", "calibration_pump_identified", "background_subtraction_identified"))})
    return {"case_count": case_count, "defined_conditional_ratios": defined, "undefined_zero_herald_ratios": undefined,
            "checks": checks, "passed": all(checks.values()), "worst_interval_width": exact_json(worst_width),
            "grid": "bound gw ratios/losses × windows 1/5 × signal-only/independent-OR; phase is irrelevant to inclusive number effects"}


def compute():
    spec = load_frozen()
    program = executable_freeze()
    packet, seed = lift_seed(spec)
    source_rows, branches = candidate_rows(packet, spec)
    controls = source_controls(spec)
    matched_passed = all(item[side]["bound_passed"] and item[side]["number_enclosed"]
        for row in branches if "matched_single_polarization" in row
        for item in (row["matched_single_polarization"],) for side in ("alice", "bob") if item[side]["status"] == "DEFINED")
    roles = {key: False for key in ("calibration_preparation_identified", "calibration_ports_identified", "calibration_pump_identified",
        "background_subtraction_identified", "source_mapping_identified", "publication_configuration_identified", "production_admitted", "actual_window_model_identified")}
    return {"schema": "p23-calibration-readout-independent/v1", "version": spec["version"],
            "criterion_freeze": criterion_freeze(), "executable_freeze": program, "bindings": spec["bindings"],
            "status": "PASS" if controls["passed"] and matched_passed else "FAIL", "source_parameters": packet,
            "seed_lift": seed, "preparations": source_rows, "branches": branches, "controls": controls,
            "matched_exact_controls_passed": matched_passed,
            "public_q": {"reported_approximate": "0.0005", "acceptance_interval": None,
                         "role": spec["roles"]["public_q_role"]},
            "arithmetic": {"outward_decimal_digits": DIGITS, "prefix_mass": "exact rational number mass × diagonal loss weights",
                           "cutoff": spec["cutoff"], "tail": "exact omitted number probability; no prefix renormalization"},
            "probability_primitive": "number-sector source mass and actual inclusive local loss survival; no PGF probability function imported",
            "other_implementation_output_used_as_input": False, "bell_event_files_read": 0,
            "private_optimizer_input_required": False, "retrospective": True, **roles}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = compute()
    if not args.check_only:
        OUTPUT.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": result["status"], "branches": len(result["branches"]),
                      "control_cases": result["controls"]["case_count"], "checks": result["controls"]["checks"]}))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
