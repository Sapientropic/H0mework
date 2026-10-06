"""Independent native optical amplitudes, CH response and rational enclosures."""
from __future__ import annotations

import argparse
import ast
import functools
import hashlib
import importlib.util
import itertools
import json
import math
import re
import subprocess
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
CRITERION = HERE / "criterion-r0001.1.md"
OUTPUT = HERE / "independent_response.json"
CS = HERE.parent / "investigation" / "collected-source"
FREEZE = "4a8e1753f4e19669e11b39ac2c8987dc890f8f6f"
SOURCE_FREEZE = "a26869a1f3e5ec4dbe94230623235a6fe4411e53"
CRITERION_SHA = "c9b4825832bba9cade516ba2319bd4f000775810436460793a75123506c5ee2d"
MATH_PATH = HERE.parent / "response" / "independent_response.py"
MATH_SHA = "83f8c6195985678a414cc78c618daff850b54c99a2df4e3f02f90be4e634027d"
SCIENCE_AST_SHA = "63b5f1337d8027626b03b1921ba7c6cb3cab76c15d4e4a57975ed640c039b852"
SCIENCE_NAMES = {
    "digest", "criterion_freeze", "load_frozen", "source_bindings", "module_from_path", "helpers", "interval_type",
    "split_coefficients", "proportional_coefficient", "generated_native_response", "polynomial_interval", "read_box",
    "response_interval", "continuous_result", "budget_receipt", "polarization_vector", "amplitude_channels",
    "source_statistics", "Model", "source_controls"
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def criterion_freeze():
    for path, commit in ((CRITERION, FREEZE), (HERE/"sources.json", SOURCE_FREEZE)):
        relative = str(path.relative_to(ROOT))
        saved = subprocess.check_output(["git", "show", commit+":"+relative], cwd=ROOT)
        if saved != path.read_bytes():
            raise ValueError("scientific freeze changed: "+relative)
        subprocess.check_call(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT)
    if digest(CRITERION) != CRITERION_SHA:
        raise ValueError("active criterion digest changed")
    return {"commit": FREEZE, "criterion_sha256": digest(CRITERION),
            "sources_commit": SOURCE_FREEZE, "sources_sha256": digest(HERE/"sources.json")}


def load_frozen():
    criterion_freeze()
    blocks = re.findall(r"```json\s*(.*?)\s*```", CRITERION.read_text(), re.S)
    if len(blocks) != 1:
        raise ValueError("exactly one frozen block is required")
    return json.loads(blocks[0])


def source_bindings():
    criterion_freeze()
    packet = json.loads((HERE/"sources.json").read_text())
    bindings = {}
    for row in packet["inputs"]:
        if digest(ROOT/row["path"]) != row["sha256"]:
            raise ValueError("source binding changed: "+row["path"])
        bindings[row["path"]] = row["sha256"]
    for commit in packet["source_commits"]:
        subprocess.check_call(["git", "merge-base", "--is-ancestor", commit, FREEZE], cwd=ROOT)
    if digest(MATH_PATH) != MATH_SHA:
        raise ValueError("reused interval implementation changed")
    for path in (CRITERION, HERE/"sources.json", MATH_PATH, Path(__file__)):
        bindings[str(path.relative_to(ROOT))] = digest(path)
    return bindings


def module_from_path(name, path):
    specification = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


@functools.lru_cache(maxsize=1)
def helpers():
    source_bindings()
    return module_from_path("cr_independent_math", MATH_PATH), module_from_path("cr_native_amplitudes", CS/"independent.py")


def interval_type():
    return helpers()[0].Interval


def split_coefficients(polynomial, variables):
    Poly = helpers()[0].Polynomial
    groups = {}
    for monomial, coefficient in polynomial.coefficients.items():
        selected = tuple((name, exponent) for name, exponent in monomial if name in variables)
        remaining = tuple((name, exponent) for name, exponent in monomial if name not in variables)
        group = groups.setdefault(selected, {})
        group[remaining] = group.get(remaining, F(0))+coefficient
    return {key: Poly(coefficients=value) for key, value in groups.items()}


def proportional_coefficient(actual, reference):
    if not reference.coefficients:
        raise ValueError("empty source reference")
    monomial, coefficient = next(iter(reference.coefficients.items()))
    scale = actual.coefficients.get(monomial, F(0))/coefficient
    if (actual-reference*scale).coefficients:
        raise ValueError("native response did not factor through generated source statistics")
    return scale


@functools.lru_cache(maxsize=1)
def generated_native_response():
    """Exact real two-bin source; all coefficients are generated from raw columns."""
    math_module, _ = helpers()
    Poly = math_module.Polynomial
    variable = Poly.variable
    state = {}
    for p, label in enumerate(("H", "V")):
        for i, j, ap, bp in itertools.product(range(2), range(2), range(2), range(2)):
            amplitude = variable("prep_"+label)*variable(f"F_{label}_{i}_{j}")
            amplitude *= variable(f"{'l' if ap else 't'}A_{label}_{i}")
            amplitude *= variable(f"{'l' if bp else 't'}B_{label}_{j}")
            state[(ap, p, i, bp, p, j)] = amplitude
    ab = [[Poly(0) for _ in range(4)] for _ in range(4)]
    a = [[Poly(0) for _ in range(2)] for _ in range(2)]
    b = [[Poly(0) for _ in range(2)] for _ in range(2)]
    for x, z in state.items():
        for y, w in state.items():
            product = z*w
            if x[0] == y[0] == x[3] == y[3] == 0 and (x[2], x[5]) == (y[2], y[5]):
                ab[2*x[1]+x[4]][2*y[1]+y[4]] += product
            if x[0] == y[0] == 0 and (x[2], x[3:]) == (y[2], y[3:]):
                a[x[1]][y[1]] += product
            if x[3] == y[3] == 0 and (x[:3], x[5]) == (y[:3], y[5]):
                b[x[4]][y[4]] += product
    trace = sum((ab[i][i] for i in range(4)), Poly(0))
    coherence = ab[0][3]
    da, db = a[1][1]-a[0][0], b[1][1]-b[0][0]
    s, c, dc, ds = (variable(name) for name in ("s", "c", "dc", "ds"))
    derivative = [[s, c], [c, -s]]
    difference = [[-dc/2, ds/2], [ds/2, dc/2]]
    scalar = math_module.trace_product
    tensor = math_module.kronecker
    coefficients = []
    for side in ("alice", "bob"):
        pair = scalar(ab, tensor(derivative, difference) if side == "alice" else tensor(difference, derivative))
        accident = scalar(a if side == "alice" else b, derivative)*scalar(b if side == "alice" else a, difference)
        pair_groups = split_coefficients(pair, {"s", "c", "dc", "ds"})
        accident_groups = split_coefficients(accident, {"s", "c", "dc", "ds"})
        sd, cd = (("dc", 1), ("s", 1)), (("c", 1), ("ds", 1))
        if set(pair_groups) != {sd, cd} or set(accident_groups) != {sd}:
            raise ValueError("unexpected angular monomial in native response")
        coefficients.append((proportional_coefficient(pair_groups[sd], trace),
                             proportional_coefficient(pair_groups[cd], coherence),
                             proportional_coefficient(accident_groups[sd], da*db)))
    if coefficients[0] != coefficients[1]:
        raise ValueError("native Alice/Bob response coefficients disagree")
    joint_z, joint_x, accidental_z = coefficients[0]
    reduced = (joint_z*s*dc + accidental_z*variable("t")*s*dc +
               joint_x/2*variable("gamma")*variable("chi_col")*c*ds)
    receipt = {"raw_source": "normalized preparation and F times local t/l columns; two-bin finite source before any target statistics",
               "partial_trace": "partner lost port, polarization and mode labels retained in singles",
               "symbolic_scope": "real finite source; complex frozen controls use actual independent amplitudes",
               "generated_coefficients": {"joint_Z": str(joint_z), "joint_K": str(joint_x), "accidental_DA_DB": str(accidental_z)},
               "factorization_verified": True, "normalization": "dCH/(Q uA uB T)",
               "normalized_response_polynomial": reduced.json(),
               "source_polynomial_monomials": {"T": len(trace.coefficients), "K": len(coherence.coefficients),
                                               "DA": len(da.coefficients), "DB": len(db.coefficients)}}
    return reduced, receipt


def polynomial_interval(polynomial, environment):
    Interval = interval_type()
    result = Interval(0)
    for monomial, coefficient in polynomial.coefficients.items():
        term = Interval(coefficient)
        for name, exponent in monomial:
            term *= environment[name]**exponent
        result += term
    return result


def read_box(config, lam):
    Interval = interval_type()
    half = F(config["angle_half_width_deg"])
    box = {"r_col": Interval(*config["r_col"]), "gamma": Interval(*config["gamma"]),
           "t": Interval(0) if lam == 0 else Interval(*config["relative_M3_Z_correction"])}
    for name, angle in zip(("a0", "a1", "b0", "b1"), config["angles_deg"]):
        box[name] = Interval(F(angle)-half, F(angle)+half)
    return box


def response_interval(box, side, pi):
    Interval = interval_type()
    math_module = helpers()[0]
    r = box["r_col"]
    if not 0 < r.lower <= r.upper < 1:
        raise ValueError("collected ratio monotonic chart not covered")
    chi = Interval(2*r.lower/(1+r.lower*r.lower), 2*r.upper/(1+r.upper*r.upper))
    own, other = ("a", "b") if side == "alice" else ("b", "a")
    s, c = math_module.trig_degrees(box[own+"1"], pi)
    s0, c0 = math_module.trig_degrees(box[other+"0"], pi)
    s1, c1 = math_module.trig_degrees(box[other+"1"], pi)
    environment = {"s": s, "c": c, "dc": c0-c1, "ds": s0-s1,
                   "gamma": box["gamma"], "chi_col": chi, "t": box["t"]}
    normalized = polynomial_interval(generated_native_response()[0], environment)
    required_gamma = (1+box["t"])*s*(c0-c1)/(chi*c*(s0-s1))
    required_t = box["gamma"]*chi*c*(s0-s1)/(s*(c0-c1))-1
    sign = "negative" if normalized.upper < 0 else "positive" if normalized.lower > 0 else "unresolved"
    return {"normalized": normalized, "required_gamma": required_gamma, "required_t": required_t,
            "sign": sign, "stationarity_excluded": sign != "unresolved"}


def continuous_result(config, lam):
    Interval = interval_type()
    pi = Interval(*config["pi"])
    box = read_box(config, lam)
    response = {side: response_interval(box, side, pi) for side in ("alice", "bob")}
    path = dict(box)
    steps = dict(zip(("a0", "a1", "b0", "b1"), map(F, config["paired_update_deg"])))
    for name, step in steps.items():
        path[name] = path[name].shifted_path(step)
    path_response = {side: response_interval(path, side, pi) for side in ("alice", "bob")}
    improvement = Interval(0)
    for name, side in (("a1", "alice"), ("b1", "bob")):
        improvement += steps[name]*pi/180*path_response[side]["normalized"]
    encode = lambda rows: {side: {key: value.json() if isinstance(value, Interval) else value for key, value in row.items()}
                           for side, row in rows.items()}
    case = "single_pair_lambda0" if lam == 0 else "M3_lambda1_calibration_envelope"
    passed = response["alice"]["sign"] == "negative" and response["bob"]["sign"] == "positive" and improvement.lower > 0
    return {"case": case, "lambda": str(lam), "box": {key: value.json() for key, value in box.items()},
            "responses": encode(response), "paired_path_box": {key: value.json() for key, value in path.items()},
            "paired_path_responses": encode(path_response), "paired_normalized_improvement": improvement.json(),
            "strict_paired_improvement": improvement.lower > 0, "status": "CERTIFIED" if passed else "NOT_CERTIFIED",
            "claim_is_conditional": True, "absolute_gain_lower_bound_asserted": False}


def budget_receipt(config):
    qmax = F(config["q_max"])
    minimum_product = F(config["klyshko_min"]["A"])*F(config["klyshko_min"]["B"])
    bounds = {"effective_pair": qmax, "collected_pair": qmax/minimum_product,
              "emitted_one_pair": qmax/minimum_product}
    shared = max(abs(F(x)) for x in config["relative_M3_Z_correction"])
    if list(bounds) != config["q_identities"] or any(value > shared for value in bounds.values()):
        raise ValueError("q identity budget does not fit the predeclared common domain")
    return {"bounds_on_abs_t": {key: str(value) for key, value in bounds.items()},
            "shared_bound": str(shared), "all_budgets_covered": True,
            "identities": ["q_eff=Q TA TB/T", "q_eff=Q uA uB T/(etaK_A etaK_B)", "|DA|<=TA, |DB|<=TB, 0<=T<=1"],
            "scope": "same preparation, same collection plane, unfiltered or corrected selection, background-subtracted S1 rates",
            "q_max_is_conditional_budget": True, "public_q_identity_assigned": False,
            "gamma_and_r_col_calibration_identity_assigned": False}


def polarization_vector(degrees, swapped=False):
    angle = math.radians(degrees)
    if degrees % 360 in (0, 90, 180, 270):
        sine, cosine = {0: (0., 1.), 90: (1., 0.), 180: (0., -1.), 270: (-1., 0.)}[degrees % 360]
    else:
        sine, cosine = math.sin(angle), math.cos(angle)
    return ((cosine, sine), (-sine, cosine)) if swapped else ((sine, cosine), (cosine, -sine))


def amplitude_channels(state, a, b, swapped=False, joint_only_singles=False):
    va, da = polarization_vector(a, swapped)
    vb, db = polarization_vector(b, swapped)
    groups = [{} for _ in range(7)]
    for (ap, pa, ai, bp, pb, bi), z in state.items():
        if ap == 0 and (not joint_only_singles or bp == 0):
            label = (ai, bp, pb, bi)
            for k, value in ((0, z*va[pa]), (1, z*da[pa])):
                groups[k][label] = groups[k].get(label, 0j)+value
        if bp == 0 and (not joint_only_singles or ap == 0):
            label = (ap, pa, ai, bi)
            for k, value in ((2, z*vb[pb]), (3, z*db[pb])):
                groups[k][label] = groups[k].get(label, 0j)+value
        if ap == bp == 0:
            label = (ai, bi)
            for k, value in ((4, z*va[pa]*vb[pb]), (5, z*da[pa]*vb[pb]), (6, z*va[pa]*db[pb])):
                groups[k][label] = groups[k].get(label, 0j)+value
    norm = lambda group: math.fsum(abs(z)**2 for z in group.values())
    tangent = lambda x, y: 2*math.fsum((z.conjugate()*y.get(label, 0j)).real for label, z in x.items())
    return {"PA": norm(groups[0]), "PB": norm(groups[2]), "J": norm(groups[4]),
            "dPA": tangent(groups[0], groups[1]), "dPB": tangent(groups[2], groups[3]),
            "dJA": tangent(groups[4], groups[5]), "dJB": tangent(groups[4], groups[6])}


def source_statistics(state):
    ta = tb = t = da = db = 0.
    collected = ({}, {})
    for (ap, pa, ai, bp, pb, bi), z in state.items():
        power = abs(z)**2
        if ap == 0:
            ta += power
            da += (1 if pa else -1)*power
        if bp == 0:
            tb += power
            db += (1 if pb else -1)*power
        if ap == bp == 0:
            t += power
            collected[pa][(ai, bi)] = z
    coherence = sum(z*collected[1].get(label, 0j).conjugate() for label, z in collected[0].items())
    return {"T": t, "TA": ta, "TB": tb, "DA": da, "DB": db, "K": coherence.real,
            "coherence": [coherence.real, coherence.imag], "norm": math.fsum(abs(z)**2 for z in state.values())}


class Model:
    def __init__(self, state, Q, uA, uB, background_A, background_B, lam, *, joint_only_singles=False, swapped=False):
        self.state = state
        self.Q, self.uA, self.uB = Q, uA, uB
        self.background_A, self.background_B = background_A, background_B
        self.lam = lam
        self.joint_only_singles, self.swapped = joint_only_singles, swapped

    def read(self, a, b, override=None):
        lam = self.lam if override is None else override
        channel = amplitude_channels(self.state, a, b, self.swapped, self.joint_only_singles)
        sa, sb = self.Q*self.uA*channel["PA"]+self.background_A, self.Q*self.uB*channel["PB"]+self.background_B
        pair_scale = self.Q*self.uA*self.uB
        return {"joint": pair_scale*channel["J"]+lam*sa*sb, "single_A": sa, "single_B": sb,
                "dA_joint": pair_scale*channel["dJA"]+lam*self.Q*self.uA*channel["dPA"]*sb,
                "dB_joint": pair_scale*channel["dJB"]+lam*self.Q*self.uB*channel["dPB"]*sa}

    def score(self, angles, override=None):
        a0, a1, b0, b1 = angles
        row = self.read(a0, b0, override)
        return (row["joint"]+self.read(a0, b1, override)["joint"]+self.read(a1, b0, override)["joint"]-
                self.read(a1, b1, override)["joint"]-row["single_A"]-row["single_B"])

    def primed(self, angles, side):
        a0, a1, b0, b1 = angles
        if side == "alice":
            return self.read(a1, b0)["dA_joint"]-self.read(a1, b1)["dA_joint"]
        if side == "bob":
            return self.read(a0, b1)["dB_joint"]-self.read(a1, b1)["dB_joint"]
        raise ValueError("side must be alice or bob")


def source_controls(config):
    source = helpers()[1]
    specification = source.specification()
    recipes = {recipe["name"]: recipe for recipe in specification["fixtures"]}
    declared = config["controls"]
    rates = [float(F(declared[key])) for key in ("Q", "uA", "uB", "background_A", "background_B")]
    h = float(F(declared["derivative_step_radians"]))
    tolerance = float(F(declared["derivative_tolerance"]))
    probability_tolerance = float(F(declared["probability_tolerance"]))
    results = []
    worst_fd = worst_identity = worst_coordinate_api = 0.
    states, statistics = {}, {}
    for fixture, r_s, phase_s in itertools.product(declared["fixtures"], declared["r_src"], declared["phase_pi"]):
        state = source.full_state(recipes[fixture], float(F(r_s)), float(F(phase_s)))
        key = (fixture, r_s, phase_s)
        states[key], statistics[key] = state, source_statistics(state)
        for lam_s, angles_s in itertools.product(declared["lambda"], declared["angles_deg"]):
            angles = list(map(lambda x: float(F(x)), angles_s))
            lam = int(F(lam_s))
            model = Model(state, *rates, lam)
            base = model.score(angles)
            update = [angle+float(F(step)) for angle, step in zip(angles, config["paired_update_deg"])]
            derivatives = {}
            for side, index in (("alice", 1), ("bob", 3)):
                direct = model.primed(angles, side)
                minus, plus = list(angles), list(angles)
                minus[index] -= math.degrees(h)
                plus[index] += math.degrees(h)
                fd = (model.score(plus)-model.score(minus))/(2*h)
                stats = statistics[key]
                own = angles[index]
                partner0, partner1 = angles[2:4] if side == "alice" else angles[0:2]
                sine, cosine = math.sin(2*math.radians(own)), math.cos(2*math.radians(own))
                dc = math.cos(2*math.radians(partner0))-math.cos(2*math.radians(partner1))
                ds = math.sin(2*math.radians(partner0))-math.sin(2*math.radians(partner1))
                # Generated coefficient readout, checked against actual amplitudes.
                generated = rates[0]*rates[1]*rates[2]/2*(-(stats["T"]+lam*rates[0]*stats["DA"]*stats["DB"])*sine*dc+2*stats["K"]*cosine*ds)
                worst_fd = max(worst_fd, abs(fd-direct))
                worst_identity = max(worst_identity, abs(generated-direct))
                derivatives[side] = {"amplitude_per_radian": direct, "finite_difference": fd,
                                     "generated_coefficient_readout": generated, "passed": abs(fd-direct) <= tolerance and abs(generated-direct) <= tolerance}
            for a, b in itertools.product(angles[:2], angles[2:]):
                own = amplitude_channels(state, a, b)
                native = source.amplitude_read(state, (0.5-a/180, 0), (0.5-b/180, 0), *rates[:3])
                worst_coordinate_api = max(worst_coordinate_api, abs(native["sA"]-rates[0]*rates[1]*own["PA"]),
                                           abs(native["sB"]-rates[0]*rates[2]*own["PB"]), abs(native["j"]-rates[0]*rates[1]*rates[2]*own["J"]))
            results.append({"fixture": fixture, "r_src": r_s, "phase_pi": phase_s, "lambda": lam_s,
                            "angles_deg": angles_s, "CH": base, "paired_update_CH": model.score(update),
                            "paired_improvement": model.score(update)-base, "derivatives": derivatives,
                            "source_statistics": statistics[key]})
    controls = []
    sample = next(iter(states.values()))
    angles = list(map(lambda x: float(F(x)), declared["angles_deg"][0]))
    for name, changed in (("Q_zero", [0., *rates[1:]]), ("uA_zero", [rates[0], 0., *rates[2:]]),
                          ("uB_zero", [*rates[:2], 0., *rates[3:]])):
        models = [Model(sample, *changed, lam) for lam in (0, 1)]
        maximum = max(abs(model.primed(angles, side)) for model in models for side in ("alice", "bob"))
        controls.append({"name": name, "maximum_primed_response": maximum, "passed": maximum <= tolerance})
    m3, single = Model(sample, *rates, 1), Model(sample, *rates, 0)
    controls.append({"name": "explicit_lambda0_override", "passed": abs(m3.score(angles, override=0)-single.score(angles)) <= probability_tolerance,
                     "default_M3_changes_score": abs(m3.score(angles)-single.score(angles)) > probability_tolerance})
    wrong = Model(sample, *rates, 1, joint_only_singles=True)
    gap = max(abs(wrong.read(angles[0], angles[2])[key]-m3.read(angles[0], angles[2])[key]) for key in ("single_A", "single_B"))
    controls.append({"name": "joint_partial_trace_single_lookalike_rejected", "single_difference": gap, "passed": gap > probability_tolerance})
    worst_same_joint = worst_lambda0 = worst_loss_identity = 0.
    nonzero_m3_difference = nonzero_lambda0_score = nonzero_phase_response = 0.
    index = {(row["fixture"], row["r_src"], row["phase_pi"], row["lambda"], tuple(row["angles_deg"])): row for row in results}
    for r_s, phase_s, angles_s in itertools.product(declared["r_src"], declared["phase_pi"], declared["angles_deg"]):
        k1, k2 = ("calibration_I", r_s, phase_s), ("calibration_II", r_s, phase_s)
        worst_same_joint = max(worst_same_joint, abs(statistics[k1]["T"]-statistics[k2]["T"]),
                               abs(complex(*statistics[k1]["coherence"])-complex(*statistics[k2]["coherence"])))
        product_difference = statistics[k2]["DA"]*statistics[k2]["DB"]-statistics[k1]["DA"]*statistics[k1]["DB"]
        worst_loss_identity = max(worst_loss_identity, abs(product_difference+9/400))
        first, second = index[(*k1, "0", tuple(angles_s))], index[(*k2, "0", tuple(angles_s))]
        worst_lambda0 = max(worst_lambda0, *(abs(first["derivatives"][side]["amplitude_per_radian"]-second["derivatives"][side]["amplitude_per_radian"]) for side in ("alice", "bob")))
        nonzero_lambda0_score = max(nonzero_lambda0_score, abs(first["CH"]-second["CH"]))
        first, second = index[(*k1, "1", tuple(angles_s))], index[(*k2, "1", tuple(angles_s))]
        nonzero_m3_difference = max(nonzero_m3_difference, *(abs(first["derivatives"][side]["amplitude_per_radian"]-second["derivatives"][side]["amplitude_per_radian"]) for side in ("alice", "bob")))
    for fixture, r_s, lam_s, angles_s in itertools.product(declared["fixtures"], declared["r_src"], declared["lambda"], declared["angles_deg"]):
        first, second = index[(fixture, r_s, "0", lam_s, tuple(angles_s))], index[(fixture, r_s, "1/2", lam_s, tuple(angles_s))]
        nonzero_phase_response = max(nonzero_phase_response, *(abs(first["derivatives"][side]["amplitude_per_radian"]-second["derivatives"][side]["amplitude_per_radian"]) for side in ("alice", "bob")))
    controls += [{"name": "same_joint_lambda0_response", "error": worst_same_joint+worst_lambda0, "passed": worst_same_joint <= probability_tolerance and worst_lambda0 <= tolerance},
                 {"name": "native_lost_partner_product_difference", "error_from_minus_9_over_400": worst_loss_identity, "passed": worst_loss_identity <= probability_tolerance and nonzero_m3_difference > tolerance},
                 {"name": "same_joint_lambda0_full_CH_can_differ", "score_difference": nonzero_lambda0_score, "passed": nonzero_lambda0_score > probability_tolerance},
                 {"name": "source_phase_changes_joint_response", "response_difference": nonzero_phase_response, "passed": nonzero_phase_response > tolerance}]
    coordinate = declared["coordinate_regression"]
    endpoints = []
    for preparation_s, angle_s in itertools.product(coordinate["preparations_HV"], coordinate["physical_vertical_angles_deg"]):
        preparation = tuple(float(F(x)) for x in preparation_s)
        state = source.state_from_preparation(recipes[coordinate["fixture"]], preparation)
        swapped_state = {(ap, 1-pa, ai, bp, 1-pb, bi): z for (ap, pa, ai, bp, pb, bi), z in state.items()}
        angle = float(F(angle_s))
        correct = Model(state, *rates, 0)
        common = Model(swapped_state, *rates, 0, swapped=True)
        wrong = Model(state, *rates, 0, swapped=True)
        expected_population = preparation[1]**2 if angle == 0 else preparation[0]**2
        read = correct.read(angle, angle)
        expected_a, expected_b = rates[0]*rates[1]*expected_population+rates[3], rates[0]*rates[2]*expected_population+rates[4]
        common_error = max(abs(read[key]-common.read(angle, angle)[key]) for key in ("single_A", "single_B", "joint"))
        bad_single = max(abs(read[key]-wrong.read(angle, angle)[key]) for key in ("single_A", "single_B"))
        bad_score = abs(correct.score([angle]*4)-wrong.score([angle]*4))
        passed = abs(read["single_A"]-expected_a) <= probability_tolerance and abs(read["single_B"]-expected_b) <= probability_tolerance and common_error <= probability_tolerance and bad_single > probability_tolerance and bad_score > probability_tolerance
        endpoints.append({"preparation_HV": preparation_s, "physical_vertical_angle_deg": angle_s,
                          "read": read, "common_permutation_error": common_error,
                          "effect_only_swap_single_difference": bad_single, "effect_only_swap_CH_difference": bad_score, "passed": passed})
    controls.append({"name": "H_V_endpoint_common_source_effect_permutation", "passed": all(row["passed"] for row in endpoints)})
    norm_error = max(abs(row["norm"]-1) for row in statistics.values())
    controls.append({"name": "whole_source_norm", "error": norm_error, "passed": norm_error <= probability_tolerance})
    passed = all(row["passed"] for row in controls) and all(all(v["passed"] for v in row["derivatives"].values()) for row in results) and worst_coordinate_api <= probability_tolerance
    return {"passed": passed, "rows": results, "controls": controls, "coordinate_endpoints": endpoints,
            "worst_finite_difference_error": worst_fd, "worst_source_response_identity_error": worst_identity,
            "worst_frozen_analyzer_embedding_error": worst_coordinate_api,
            "scope": "synthetic S1 native source controls, explicit lambda=1 M3 extension; neither public gamma nor q identity is assigned"}


def scientific_digest():
    tree = ast.parse(Path(__file__).read_text())
    definitions = [node for node in tree.body if isinstance(node, (ast.FunctionDef, ast.ClassDef)) and node.name in SCIENCE_NAMES]
    if {node.name for node in definitions} != SCIENCE_NAMES:
        raise ValueError("scientific definition missing")
    return hashlib.sha256(ast.dump(ast.Module(body=definitions, type_ignores=[]), include_attributes=False).encode()).hexdigest()


def append_comparison():
    if scientific_digest() != SCIENCE_AST_SHA:
        raise ValueError("independent scientific implementation changed after its first computation")
    config = load_frozen()
    own = json.loads(OUTPUT.read_text())
    primary_path = HERE/"response.json"
    primary = json.loads(primary_path.read_text())
    primary_hash = digest(primary_path)
    own_relative, primary_relative = str(Path(__file__).relative_to(ROOT)), str(primary_path.relative_to(ROOT))
    for path, expected in own["bindings"].items():
        if path not in (own_relative, primary_relative) and digest(ROOT/path) != expected:
            raise ValueError("independent source binding changed: "+path)
    for path, expected in primary["bindings"].items():
        if digest(ROOT/path) != expected:
            raise ValueError("primary source binding changed: "+path)
    shared = set(own["bindings"]) & set(primary["bindings"])
    source_agreement = all(own["bindings"][path] == primary["bindings"][path] for path in shared)
    freeze_agreement = (own["version"] == primary["version"] == config["version"] and
                        own["criterion_freeze"]["commit"] == primary["freeze"]["commit"] == FREEZE and
                        own["criterion_freeze"]["criterion_sha256"] == primary["freeze"]["criterion_sha256"] == CRITERION_SHA and
                        own["criterion_freeze"]["sources_sha256"] == primary["freeze"]["sources_sha256"])
    scope_agreement = all(own[name] is False and primary[name] is False for name in
                          ("source_mapping_identified", "publication_configuration_identified", "production_admitted")) and primary["actual_final_NIST_calibration_bound"] is False
    probability_tolerance = float(F(config["controls"]["probability_tolerance"]))
    derivative_tolerance = float(F(config["controls"]["derivative_tolerance"]))
    primary_cases = {row["case"]: row for row in primary["cases"]}
    key = lambda row: (row["fixture"], row["r_src"], row["phase_pi"], row["lambda"], tuple(row["angles_deg"]))
    primary_rows = {key(row): row for row in primary["source_controls"]["rows"]}
    deltas = {"CH": 0., "primed_derivative": 0., "paired_improvement": 0., "source_statistic": 0.}
    rows = []
    enclosure_points = []

    def contains(interval, value):
        return F(interval["exact_lower"]) <= F(value) <= F(interval["exact_upper"])

    for row in own["source_controls"]["rows"]:
        other = primary_rows[key(row)]
        deltas["CH"] = max(deltas["CH"], abs(row["CH"]-other["CH"]))
        deltas["paired_improvement"] = max(deltas["paired_improvement"], abs(row["paired_improvement"]-other["paired_CH_improvement"]))
        for side in ("alice", "bob"):
            deltas["primed_derivative"] = max(deltas["primed_derivative"], abs(row["derivatives"][side]["amplitude_per_radian"]-other["derivatives_per_radian"][side]))
        stats = row["source_statistics"]
        deltas["source_statistic"] = max(deltas["source_statistic"], abs(stats["T"]-other["trace_joint"]),
                                         abs(2*stats["K"]-other["real_joint_coherence"]), abs(stats["DA"]-other["single_contrasts"]["A"]),
                                         abs(stats["DB"]-other["single_contrasts"]["B"]))
        rows.append({"key": list(key(row)), "compared": True})
        if row["r_src"] == "276/961" and row["phase_pi"] == "0" and row["angles_deg"] == config["angles_deg"]:
            case_name = "single_pair_lambda0" if row["lambda"] == "0" else "M3_lambda1_calibration_envelope"
            case = next(item for item in own["cases"] if item["case"] == case_name)
            main = primary_cases[case_name]
            rates = config["controls"]
            scale = float(F(rates["Q"])*F(rates["uA"])*F(rates["uB"]))*stats["T"]
            normalized = {side: row["derivatives"][side]["amplitude_per_radian"]/scale for side in ("alice", "bob")}
            gain = row["paired_improvement"]/scale
            derivative_inside = all(contains(case["responses"][side]["normalized"], value) and contains(main["responses"][side]["normalized_per_radian"], value) for side, value in normalized.items())
            gain_inside = contains(case["paired_normalized_improvement"], gain) and contains(main["paired_update"]["normalized_CH_improvement"], gain)
            enclosure_points.append({"fixture": row["fixture"], "case": case_name,
                                     "native_normalized_derivatives": normalized, "native_normalized_paired_gain": gain,
                                     "derivatives_inside_both": derivative_inside, "gain_inside_both": gain_inside,
                                     "scope": "the point satisfies the mathematical r_col/gamma/t/angle box; synthetic q/calibration identities remain unassigned"})
    cases = []
    response_mapping = {"normalized": "normalized_per_radian", "required_gamma": "required_gamma", "required_t": "required_relative_Z_correction"}
    for own_case in own["cases"]:
        main = primary_cases[own_case["case"]]
        input_agreement = all(F(value[edge]) == F(main["box"][name][edge]) for name, value in own_case["box"].items() for edge in ("exact_lower", "exact_upper"))
        response_overlap = all(max(F(row[our_field]["exact_lower"]), F(main["responses"][side][main_field]["exact_lower"])) <=
                               min(F(row[our_field]["exact_upper"]), F(main["responses"][side][main_field]["exact_upper"]))
                               for side, row in own_case["responses"].items() for our_field, main_field in response_mapping.items())
        sign_agreement = all(row["sign"] == main["responses"][side]["sign"] and row["stationarity_excluded"] == main["responses"][side]["stationarity_excluded"]
                             for side, row in own_case["responses"].items())
        path_agreement = all(F(value[edge]) == F(main["paired_update"]["path_box"][name][edge]) for name, value in own_case["paired_path_box"].items() for edge in ("exact_lower", "exact_upper"))
        improvement_agreement = own_case["strict_paired_improvement"] == main["paired_update"]["certified_improvement"]
        cases.append({"case": own_case["case"], "input_boxes_match": input_agreement, "response_enclosures_overlap": response_overlap,
                      "response_signs_agree": sign_agreement, "update_path_boxes_match": path_agreement,
                      "strict_update_agrees": improvement_agreement, "passed": input_agreement and response_overlap and sign_agreement and path_agreement and improvement_agreement})
    numerical_agreement = (deltas["CH"] <= probability_tolerance and deltas["paired_improvement"] <= probability_tolerance and
                           deltas["source_statistic"] <= probability_tolerance and deltas["primed_derivative"] <= derivative_tolerance)
    passed = (source_agreement and freeze_agreement and scope_agreement and numerical_agreement and all(row["passed"] for row in cases) and
              all(row["derivatives_inside_both"] and row["gain_inside_both"] for row in enclosure_points) and len(enclosure_points) == 4)
    if digest(primary_path) != primary_hash:
        raise ValueError("primary output changed during comparison; retry comparison only")
    own.setdefault("calculation_implementation", {"program_source_sha256": own["bindings"][own_relative], "scientific_ast_sha256": SCIENCE_AST_SHA,
                                                  "primary_code_or_output_used_as_input": False})
    own["bindings"][own_relative] = digest(Path(__file__))
    own["bindings"][primary_relative] = primary_hash
    own["comparison"] = {"phase": "post hoc after independent native-source and continuous computations; no interval recomputation",
                         "primary_sha256": primary_hash, "primary_bindings": primary["bindings"],
                         "source_bindings_agree": source_agreement, "freeze_version_agree": freeze_agreement,
                         "conditional_scope_agrees": scope_agreement, "normalization_agrees": "dCH/(Q uA uB trace(OmegaAB)); per radian",
                         "source_coherence_convention": "primary real_joint_coherence=2 Re(OmegaAB[HH,VV]); independent source_statistics.K=Re(OmegaAB[HH,VV])",
                         "cases": cases, "source_control_rows_compared": len(rows), "worst_deltas": deltas,
                         "actual_native_enclosure_points": enclosure_points, "passed": passed}
    OUTPUT.write_text(json.dumps(own, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps({"comparison_passed": passed, "source_rows_compared": len(rows), "native_enclosure_points": len(enclosure_points)}))
    return 0 if passed else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare", "--compare-only", action="store_true", dest="compare")
    args = parser.parse_args()
    if args.compare:
        return append_comparison()
    config = load_frozen()
    bindings = source_bindings()
    if config["interval"]["independent_terms"] != 14:
        raise ValueError("independent Taylor count differs from the frozen method")
    response, source_certificate = generated_native_response()
    cases = [continuous_result(config, lam) for lam in (0, 1)]
    for case in cases:
        print(case["case"], case["status"], flush=True)
    controls = source_controls(config)
    budgets = budget_receipt(config)
    passed = all(case["status"] == "CERTIFIED" for case in cases) and controls["passed"] and budgets["all_budgets_covered"]
    result = {"schema": "p23-collected-response-independent/v1", "version": config["version"],
              "criterion_freeze": criterion_freeze(), "bindings": bindings,
              "source_mapping_identified": False, "publication_configuration_identified": False, "production_admitted": False,
              "status": "CERTIFIED" if passed else "NOT_CERTIFIED", "claim_is_conditional": True,
              "primitive": "frozen independent.full_state/state_from_preparation; new analyzer amplitude and tangent sums with partner-loss labels",
              "symbolic_source_certificate": source_certificate, "budgets": budgets,
              "arithmetic": {"method": "reused independent Fraction endpoint/monotonicity engine; 14-term Taylor with Lagrange remainder",
                             "implementation_binding": str(MATH_PATH.relative_to(ROOT)), "pi": config["pi"], "leaves": 1},
              "cases": cases, "source_controls": controls, "bell_event_files_read": 0,
              "other_implementation_output_used_as_input": False,
              "access_disclosure": "Independent source/interval computation did not read primary code or output; root only reported its completion."}
    OUTPUT.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n")
    print("native controls", "PASS" if controls["passed"] else "FAIL", "rows", len(controls["rows"]), flush=True)
    print(result["status"], flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
