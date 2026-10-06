"""Number-basis TMSV Born sums with exact geometric-tail payment."""
from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import math
import re
import subprocess
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
CRITERION = HERE / "criterion.md"
OUTPUT = HERE / "independent_fock.json"
FREEZE = "5b5814bceb"
DIGITS = 30
SCALE = 10**DIGITS


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
            raise ValueError("reversed rational interval")

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
        values = [x*y for x in (self.lo, self.hi) for y in (other.lo, other.hi)]
        return Interval(down(min(values)), up(max(values)))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.lo <= 0 <= self.hi:
            raise ValueError("rational interval division crosses zero")
        return Interval(down(1/self.hi), up(1/self.lo))

    def __truediv__(self, other):
        return self*self.cast(other).reciprocal()

    def __rtruediv__(self, other):
        return self.cast(other)*self.reciprocal()

    def __pow__(self, exponent):
        if exponent < 0:
            return self.reciprocal()**(-exponent)
        if exponent == 0:
            return Interval(1)
        if exponent % 2:
            return Interval(down(self.lo**exponent), up(self.hi**exponent))
        lower = 0 if self.lo <= 0 <= self.hi else min(abs(self.lo), abs(self.hi))**exponent
        return Interval(down(lower), up(max(abs(self.lo), abs(self.hi))**exponent))

    def intersect(self, lower, upper):
        return Interval(max(self.lo, F(lower)), min(self.hi, F(upper)))

    def contains(self, value):
        return self.lo <= F(value) <= self.hi

    def json(self):
        return {"exact_lower": str(self.lo), "exact_upper": str(self.hi), "lower": float(self.lo), "upper": float(self.hi)}


@functools.lru_cache(maxsize=4096)
def sqrt_endpoint(value):
    value = F(value)
    if value < 0:
        raise ValueError("negative square-root input")
    numerator_root, denominator_root = math.isqrt(value.numerator), math.isqrt(value.denominator)
    if numerator_root*numerator_root == value.numerator and denominator_root*denominator_root == value.denominator:
        return Interval(F(numerator_root, denominator_root))
    integer = math.isqrt(value.numerator*SCALE*SCALE//value.denominator)
    return Interval(F(integer, SCALE), F(integer+1, SCALE))


def sqrt_interval(value):
    value = Interval.cast(value)
    return Interval(sqrt_endpoint(value.lo).lo, sqrt_endpoint(value.hi).hi)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def criterion_freeze():
    commit = subprocess.check_output(["git", "rev-parse", FREEZE], cwd=ROOT, text=True).strip()
    for path in (CRITERION, HERE/"sources.json"):
        relative = str(path.relative_to(ROOT))
        committed = subprocess.check_output(["git", "show", commit+":"+relative], cwd=ROOT)
        if committed != path.read_bytes():
            raise ValueError("frozen input changed: "+relative)
    subprocess.check_call(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT)
    return {"commit": commit, "criterion_sha256": digest(CRITERION), "sources_sha256": digest(HERE/"sources.json")}


def executable_freeze():
    path = str(Path(__file__).relative_to(ROOT))
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", path], cwd=ROOT, text=True).strip()
    if not commit or subprocess.check_output(["git", "show", commit+":"+path], cwd=ROOT) != Path(__file__).read_bytes():
        raise ValueError("commit the complete independent executable before numerical execution")
    subprocess.check_call(["git", "merge-base", "--is-ancestor", FREEZE, commit], cwd=ROOT)
    return {"commit": commit, "program_sha256": digest(Path(__file__))}


def load_frozen():
    criterion_freeze()
    blocks = re.findall(r"```json\s*(.*?)\s*```", CRITERION.read_text(), re.S)
    if len(blocks) != 1:
        raise ValueError("one machine-readable criterion is required")
    spec = json.loads(blocks[0])
    if spec["independent_precision_digits"] != DIGITS or spec["independent_terms"] != 14 or spec["source_pair_cutoff"] != 6:
        raise ValueError("independent method differs from the frozen specification")
    return spec


def bindings():
    criterion_freeze()
    packet = json.loads((HERE/"sources.json").read_text())
    result = {}
    for row in packet["inputs"]:
        if digest(ROOT/row["path"]) != row["sha256"]:
            raise ValueError("source binding changed: "+row["path"])
        result[row["path"]] = row["sha256"]
    subprocess.check_call(["git", "merge-base", "--is-ancestor", packet["public_source_commit"], "HEAD"], cwd=ROOT)
    for path in (CRITERION, HERE/"sources.json", Path(__file__)):
        result[str(path.relative_to(ROOT))] = digest(path)
    return result


@functools.lru_cache(maxsize=256)
def taylor_endpoint(kind, x):
    x = F(x)
    if kind == "sin":
        degree = 27
        polynomial = sum(((-1)**k*x**(2*k+1)/math.factorial(2*k+1) for k in range(14)), F(0))
    elif kind == "cos":
        degree = 26
        polynomial = sum(((-1)**k*x**(2*k)/math.factorial(2*k) for k in range(14)), F(0))
    else:
        raise ValueError("unrecognized Taylor function")
    remainder = abs(x)**(degree+1)/math.factorial(degree+1)
    return Interval(down(polynomial-remainder), up(polynomial+remainder))


@functools.lru_cache(maxsize=64)
def trigonometry(degrees, pi_lo, pi_hi):
    degrees = F(degrees)
    residue = degrees % 360
    if residue in (0, 90, 180, 270):
        sine, cosine = {0: (0, 1), 90: (1, 0), 180: (0, -1), 270: (-1, 0)}[residue]
        return Interval(sine), Interval(cosine)
    radians = Interval(degrees)*Interval(pi_lo, pi_hi)/180
    if radians.lo < -F(pi_lo)/2 or radians.hi > F(pi_lo)/2:
        raise ValueError("endpoint sine monotonicity domain not covered")
    sine = Interval(taylor_endpoint("sin", radians.lo).lo, taylor_endpoint("sin", radians.hi).hi)
    maximum = max(abs(radians.lo), abs(radians.hi))
    minimum = 0 if radians.lo <= 0 <= radians.hi else min(abs(radians.lo), abs(radians.hi))
    cosine = Interval(taylor_endpoint("cos", maximum).lo, 1 if minimum == 0 else taylor_endpoint("cos", minimum).hi)
    return sine, cosine


def valid_source(tH, tV, transmissions, phase_cos):
    if not 0 <= tH < 1 or not 0 <= tV < 1:
        raise ValueError("geometric ratios must lie in [0,1)")
    if any(not 0 <= value <= 1 for value in transmissions):
        raise ValueError("actual transmissions must lie in [0,1]")
    if phase_cos.lo < -1 or phase_cos.hi > 1:
        raise ValueError("source phase is not a unit-circle cosine enclosure")


def source_parameters(ratios, transmissions, numerator, sqrt_denominator=1):
    packet = {"geometric_ratio": [str(F(value)) for value in ratios],
              "transmission_A": [str(F(value)) for value in transmissions[:2]],
              "transmission_B": [str(F(value)) for value in transmissions[2:]],
              "phase_cos": {"numerator": str(F(numerator)), "sqrt_denominator": str(F(sqrt_denominator))}}
    unpack_source(packet)
    return packet


def unpack_source(packet):
    ratios = list(map(F, packet["geometric_ratio"]))
    transmissions = list(map(F, packet["transmission_A"]+packet["transmission_B"]))
    if len(ratios) != 2 or len(packet["transmission_A"]) != 2 or len(packet["transmission_B"]) != 2:
        raise ValueError("the source has exactly two polarizations and two loss arms")
    phase = packet["phase_cos"]
    numerator, radicand = F(phase["numerator"]), F(phase["sqrt_denominator"])
    if radicand <= 0 or numerator*numerator > radicand:
        raise ValueError("source phase is not a valid exact unit-circle parameter")
    cosine = (Interval(numerator)/sqrt_endpoint(radicand)).intersect(-1, 1)
    valid_source(*ratios, transmissions, cosine)
    return {"tH": ratios[0], "tV": ratios[1],
            **dict(zip(("TAH", "TAV", "TBH", "TBV"), transmissions)), "phase_cos": cosine}


def map_seed(spec):
    seed_path = (HERE/spec["seed_report"]).resolve()
    report = json.loads(seed_path.read_text())
    branch = next(item for item in report["branches"] if item["model"] == spec["seed_model"])
    seed = {name: F(value) for name, value in branch["source_member"]["statistics"].items()}
    N = F(spec["window_pulses"])
    result = {}
    identities = {}
    for pol, a, b, coincidence in (("H", "AH", "BH", "H"), ("V", "AV", "BV", "V")):
        A, B, L = seed[a], seed[b], seed[coincidence]
        denominator = N*L-A*B
        if min(A, B, L, denominator) <= 0:
            raise ValueError("NO_VALID_CALIBRATION_SEED: nonpositive calibration denominator")
        n = A*B/denominator
        ta, tb = denominator/(N*B), denominator/(N*A)
        t = n/(1+n)
        if not 0 <= ta <= 1 or not 0 <= tb <= 1:
            raise ValueError("NO_VALID_CALIBRATION_SEED: actual transmission is outside [0,1]")
        result["t"+pol], result["TA"+pol], result["TB"+pol] = t, ta, tb
        identities[pol] = {"denominator": str(denominator), "n_from_raw_ratio": str(t/(1-t)),
                           "N_n_TA_matches_A": N*t/(1-t)*ta == A,
                           "N_n_TB_matches_B": N*t/(1-t)*tb == B,
                           "N_n_1plusn_TA_TB_matches_L": N*t/(1-t)*(1+t/(1-t))*ta*tb == L}
    if seed["X"]**2 > seed["H"]*seed["V"]:
        raise ValueError("NO_VALID_CALIBRATION_SEED: real Gram is not PSD")
    packet = source_parameters([result["tH"], result["tV"]],
                               [result[key] for key in ("TAH", "TAV", "TBH", "TBV")], seed["X"], seed["H"]*seed["V"])
    return packet, {"seed_model": spec["seed_model"], "seed_statistics": {name: str(value) for name, value in seed.items()},
                    "identities": identities, "phase_cos": unpack_source(packet)["phase_cos"].json(),
                    "role": "fixed source/loss construction seed, not observed photon means or actual apparatus parameters",
                    "source_mapping_identified": False}


def no_click_effect(transmission_H, transmission_V, degrees, pi):
    s, c = trigonometry(F(degrees), F(pi[0]), F(pi[1]))
    off_diagonal = -sqrt_endpoint(F(transmission_H)*F(transmission_V))*s*c
    return [[1-F(transmission_H)*s**2, off_diagonal], [off_diagonal, 1-F(transmission_V)*c**2]]


@functools.lru_cache(maxsize=256)
def gamma_blocks(transmission_H, transmission_V, degrees, pi_lo, pi_hi, cutoff):
    """Symmetric tensor powers of the actual one-photon no-click contraction."""
    effect = no_click_effect(transmission_H, transmission_V, degrees, (pi_lo, pi_hi))
    power = {}
    for i, j, exponent in itertools.product(range(2), range(2), range(cutoff+1)):
        power[(i, j, exponent)] = effect[i][j]**exponent
    blocks = []
    for total in range(cutoff+1):
        block = [[Interval(0) for _ in range(total+1)] for _ in range(total+1)]
        for mh in range(total+1):
            mv = total-mh
            for nh in range(mh, total+1):
                nv = total-nh
                coefficient = Interval(0)
                for k in range(max(0, mh-nv), min(nh, mh)+1):
                    l = mh-k
                    term = math.comb(nh, k)*math.comb(nv, l)
                    term *= power[(0, 0, k)]*power[(1, 0, nh-k)]*power[(0, 1, l)]*power[(1, 1, nv-l)]
                    coefficient += term
                coefficient *= sqrt_endpoint(F(math.factorial(mh)*math.factorial(mv), math.factorial(nh)*math.factorial(nv)))
                # Hermiticity gives the same coefficient for the transposed entry.
                coefficient = coefficient.intersect(0 if mh == nh else -1, 1)
                block[mh][nh] = block[nh][mh] = coefficient
        blocks.append(block)
    return tuple(tuple(tuple(row) for row in block) for block in blocks)


def cos_multiples(phase_cos, cutoff):
    values = [Interval(1)]
    if cutoff:
        values.append(phase_cos)
    for k in range(2, cutoff+1):
        values.append((2*phase_cos*values[-1]-values[-2]).intersect(-1, 1))
    return values


def geometric_mass(tH, tV, cutoff):
    return (1-tH)*(1-tV)*sum((tH**h*tV**(total-h) for total in range(cutoff+1) for h in range(total+1)), F(0))


def amplitude_product(tH, tV, h1, v1, h2, v2):
    hsum, vsum = h1+h2, v1+v2
    if hsum % 2 != vsum % 2:
        raise ValueError("source amplitudes are not in the same number sector")
    product = Interval(tH**(hsum//2)*tV**(vsum//2))
    return product*sqrt_endpoint(tH*tV) if hsum % 2 else product


def pulse_noclick(source, a, b, spec):
    source = unpack_source(source)
    tH, tV = source["tH"], source["tV"]
    transmissions = [source[key] for key in ("TAH", "TAV", "TBH", "TBV")]
    phase_cos = source["phase_cos"]
    valid_source(tH, tV, transmissions, phase_cos)
    cutoff = spec["source_pair_cutoff"]
    pi_lo, pi_hi = map(F, spec["pi"])
    alice = gamma_blocks(transmissions[0], transmissions[1], F(a), pi_lo, pi_hi, cutoff)
    bob = gamma_blocks(transmissions[2], transmissions[3], F(b), pi_lo, pi_hi, cutoff)
    phase = cos_multiples(phase_cos, cutoff)
    normalization = (1-tH)*(1-tV)
    p0a, p0b, p00 = Interval(0), Interval(0), Interval(0)
    for total in range(cutoff+1):
        for h in range(total+1):
            v = total-h
            probability = normalization*tH**h*tV**v
            p0a += probability*alice[total][h][h]
            p0b += probability*bob[total][h][h]
            for other_h in range(total+1):
                other_v = total-other_h
                weight = normalization*amplitude_product(tH, tV, h, v, other_h, other_v)*phase[abs(v-other_v)]
                p00 += weight*alice[total][other_h][h]*bob[total][other_h][h]
    mass = geometric_mass(tH, tV, cutoff)
    tail = 1-mass
    if not 0 <= tail <= 1:
        raise ValueError("geometric source tail is invalid")
    partial = {"P0A": p0a.intersect(0, mass), "P0B": p0b.intersect(0, mass), "P00": p00.intersect(0, mass)}
    full = {key: (value+Interval(0, tail)).intersect(0, 1) for key, value in partial.items()}
    return {"partial": partial, "full": full, "mass": mass, "tail": tail}


def window_rates(pulse, window, background):
    if window < 1:
        raise ValueError("window must contain a positive number of fresh source slots")
    p0a, p0b, p00 = (pulse["full"][key]**window for key in ("P0A", "P0B", "P00"))
    signal = {"sA": (1-p0a).intersect(0, 1), "sB": (1-p0b).intersect(0, 1),
              "j": (1-p0a-p0b+p00).intersect(0, 1)}
    ba, bb = (1-(1-F(value))**window for value in background)
    observed = {"sA": ba+(1-ba)*signal["sA"], "sB": bb+(1-bb)*signal["sB"],
                "j": (1-ba)*(1-bb)*signal["j"]+ba*(1-bb)*signal["sB"]+bb*(1-ba)*signal["sA"]+ba*bb}
    return {"signal": signal, "observed": observed, "background_window": [ba, bb]}


def interval_subset(inner, outer):
    return F(outer["exact_lower"]) <= inner.lo and inner.hi <= F(outer["exact_upper"])


def pulse_json(pulse):
    return {"partial": {key: value.json() for key, value in pulse["partial"].items()},
            "full": {key: value.json() for key, value in pulse["full"].items()},
            "mass": str(pulse["mass"]), "tail": str(pulse["tail"])}


def seed_prediction(source, spec):
    seed = json.loads((HERE/spec["seed_report"]).resolve().read_text())
    confidence = seed["common_mean_confidence"]
    angles = list(map(F, spec["angles_deg"]))
    signal = {"j": [], "sA_cell": [], "sB_cell": []}
    observed = {"j": [], "sA_cell": [], "sB_cell": []}
    pulse_rows = []
    for a_index, b_index in ((0, 0), (0, 1), (1, 0), (1, 1)):
        pulse = pulse_noclick(source, angles[a_index], angles[2+b_index], spec)
        rates = window_rates(pulse, spec["window_pulses"], spec["background_per_pulse"])
        for field, rate in (("j", "j"), ("sA_cell", "sA"), ("sB_cell", "sB")):
            signal[field].append(rates["signal"][rate].json())
            observed[field].append(rates["observed"][rate].json())
        pulse_rows.append(pulse_json(pulse))
    inclusion = {field: [interval_subset(Interval(value["exact_lower"], value["exact_upper"]), target)
                         for value, target in zip(observed[field], confidence[field])]
                 for field in observed}
    return {"signal_probability_enclosures": signal, "observed_probability_enclosures": observed,
            "pulse_noclick": pulse_rows, "confidence_inclusion": inclusion,
            "enclosure_status": "EXHIBITED_FULL_FOCK_WINDOW_MEMBER" if all(all(row) for row in inclusion.values()) else "NOT_CERTIFIED_BY_ENCLOSURE"}


def make_source(ratios, transmissions, phase_cos):
    return source_parameters(ratios, transmissions, phase_cos)


def source_controls(spec):
    controls = spec["controls"]
    rows = []
    normalized = valid_ranges = geometric_checks = True
    widest_tail = F(0)
    choices = (enumerate(controls["geometric_ratio_pairs"]), enumerate(controls["transmission_HV"]),
               enumerate(controls["phase_cos"]), enumerate(controls["angles_deg"]))
    for (r_index, ratios), (t_index, transmissions), (p_index, cosine), (angle_index, angles) in itertools.product(*choices):
        source = make_source(ratios, transmissions, cosine)
        raw = unpack_source(source)
        angles = list(map(F, angles))
        pulses = []
        for a_index, b_index in ((0, 0), (0, 1), (1, 0), (1, 1)):
            a, b = angles[a_index], angles[2+b_index]
            pulse = pulse_noclick(source, a, b, spec)
            pulses.append(pulse)
            widest_tail = max(widest_tail, pulse["tail"])
            normalized = normalized and pulse["mass"]+pulse["tail"] == 1
            valid_ranges = valid_ranges and all(0 <= value.lo <= value.hi <= 1 for value in pulse["full"].values())
            if raw["tH"] == 0 or raw["tV"] == 0:
                pol = 0 if raw["tV"] == 0 else 1
                ratio = raw["tH"] if pol == 0 else raw["tV"]
                ea = no_click_effect(raw["TAH"], raw["TAV"], a, spec["pi"])[pol][pol]
                eb = no_click_effect(raw["TBH"], raw["TBV"], b, spec["pi"])[pol][pol]
                one_pol = {"P0A": (1-ratio)/(1-ratio*ea), "P0B": (1-ratio)/(1-ratio*eb), "P00": (1-ratio)/(1-ratio*ea*eb)}
                geometric_checks = geometric_checks and all(max(pulse["full"][key].lo, value.lo) <= min(pulse["full"][key].hi, value.hi) for key, value in one_pol.items())
        for window in controls["windows"]:
            cells = []
            for pulse in pulses:
                rates = window_rates(pulse, window, spec["background_per_pulse"])
                cells.append({"pulse_noclick": pulse_json(pulse),
                              "signal": {key: value.json() for key, value in rates["signal"].items()},
                              "observed": {key: value.json() for key, value in rates["observed"].items()}})
            rows.append({"case_id": f"t{r_index}/loss{t_index}/ph{p_index}/a{angle_index}/N{window}",
                         "source_parameters": source, "angles_deg": [str(value) for value in angles],
                         "window_pulses": window, "cells": cells})
    # Nonvacuous controls use the frozen pure-H ratio, unit loss and endpoints.
    pure_h = make_source(controls["geometric_ratio_pairs"][1], controls["transmission_HV"][0], "1")
    endpoints = list(map(F, controls["endpoint_angles_deg"]))
    zero = endpoints[0]
    horizontal = endpoints[1]
    vertical_pulse = pulse_noclick(pure_h, zero, zero, spec)
    horizontal_pulse = pulse_noclick(pure_h, horizontal, horizontal, spec)
    pure_h_ratio = F(pure_h["geometric_ratio"][0])
    endpoint_h = vertical_pulse["full"]["P0A"].contains(1) and horizontal_pulse["full"]["P0A"].contains(1-pure_h_ratio)
    pure_v = make_source(controls["geometric_ratio_pairs"][2], controls["transmission_HV"][0], "1")
    v_vertical = pulse_noclick(pure_v, zero, zero, spec)
    v_horizontal = pulse_noclick(pure_v, horizontal, horizontal, spec)
    endpoint_v = v_vertical["full"]["P0A"].contains(1-F(pure_v["geometric_ratio"][1])) and v_horizontal["full"]["P0A"].contains(1)
    endpoint_ok = endpoint_h and endpoint_v
    wrong_swap_detected = vertical_pulse["full"]["P0A"].lo > horizontal_pulse["full"]["P0A"].hi
    closed = 1-pure_h_ratio
    renormalized = horizontal_pulse["partial"]["P0A"]/horizontal_pulse["mass"]
    renormalization_detected = not renormalized.contains(closed)
    tail_omission_detected = horizontal_pulse["tail"] > 0 and horizontal_pulse["mass"] < 1
    pulse_one = window_rates(horizontal_pulse, 1, ["0", "0"])["signal"]["j"]
    pulse_five = window_rates(horizontal_pulse, 5, ["0", "0"])["signal"]["j"]
    multipair_omission_detected = pulse_one.lo > (1-pure_h_ratio)*pure_h_ratio
    summed_pulses_detected = (5*pulse_one).lo > pulse_five.hi
    b = F(spec["background_per_pulse"][0])
    additive_background_detected = 1+b > 1
    two_pol = make_source(controls["geometric_ratio_pairs"][3], controls["transmission_HV"][0], "1")
    angles = list(map(F, controls["angles_deg"][0]))
    phase_zero = pulse_noclick(two_pol, angles[0], angles[2], spec)
    phase_right = pulse_noclick({**two_pol, "phase_cos": {"numerator": "0", "sqrt_denominator": "1"}}, angles[0], angles[2], spec)
    phase_changes_joint = max(phase_zero["full"]["P00"].lo, phase_right["full"]["P00"].lo) > min(phase_zero["full"]["P00"].hi, phase_right["full"]["P00"].hi)
    checks = {"geometric_source_mass_plus_tail": normalized, "number_born_valid_ranges": valid_ranges,
              "one_polarization_geometric_no_click": geometric_checks, "pure_H_V_reference_endpoints": endpoint_ok,
              "source_effect_only_swap_detected": wrong_swap_detected,
              "truncated_source_renormalization_detected": renormalization_detected,
              "omitted_source_tail_detected": tail_omission_detected,
              "multiple_pair_sectors_not_discarded": multipair_omission_detected,
              "sum_of_pulse_coincidences_not_window_detected": summed_pulses_detected,
              "additive_background_not_unbounded_POVM": additive_background_detected,
              "unit_circle_phase_changes_joint": phase_changes_joint}
    return {"rows": rows, "checks": checks, "passed": all(checks.values()), "largest_exact_tail": str(widest_tail),
            "case_count": len(rows), "cell_count": sum(len(row["cells"]) for row in rows),
            "gamma_cache": gamma_blocks.cache_info()._asdict()}


def compute():
    spec = load_frozen()
    program = executable_freeze()
    source_binding = bindings()
    try:
        source, seed = map_seed(spec)
    except ValueError as error:
        return {"schema": "p23-gaussian-window-independent-fock/v1", "version": spec["version"],
                "criterion_freeze": criterion_freeze(), "executable_freeze": program, "bindings": source_binding,
                "status": "NO_VALID_CALIBRATION_SEED", "reason": str(error)}
    candidate = seed_prediction(source, spec)
    controls = source_controls(spec)
    return {"schema": "p23-gaussian-window-independent-fock/v1", "version": spec["version"],
            "criterion_freeze": criterion_freeze(), "executable_freeze": program, "bindings": source_binding,
            "status": "PASS" if controls["passed"] else "FAIL", "calibration_seed": seed,
            "source_parameters": source,
            "candidate": candidate, "controls": controls,
            "public_probabilities": candidate["observed_probability_enclosures"],
            "confidence_inclusion": candidate["confidence_inclusion"], "outcome": candidate["enclosure_status"],
            "cutoff_tail": candidate["pulse_noclick"][0]["tail"], "prefix": candidate["pulse_noclick"],
            "arithmetic": {"digits": DIGITS, "Taylor_terms": 14, "pi": spec["pi"],
                           "sqrt": "integer-square-root rational enclosures", "source_pair_cutoff": spec["source_pair_cutoff"]},
            "primitive": "normalized geometric pair amplitudes and symmetric-tensor no-click effects; no Gaussian-vacuum probability primitive",
            "tail_role": "exact unbounded-source probability in untouched number sectors; contributions enclosed in [0,tail]; no renormalization",
            "publication_configuration_identified": False, "source_mapping_identified": False,
            "production_admitted": False, "actual_window_model_identified": False,
            "bell_event_files_read": 0, "other_implementation_output_used_as_input": False,
            "retrospective": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = compute()
    if not args.check_only:
        OUTPUT.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": result["status"], "candidate": result.get("candidate", {}).get("enclosure_status"),
                      "control_rows": len(result.get("controls", {}).get("rows", [])), "controls": result.get("controls", {}).get("checks", {})}))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
