"""Full optical amplitudes and an observable-only Gaussian inverse consumer."""
from __future__ import annotations

import argparse
import cmath
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
CRITERION = HERE / "criterion.md"
OUTPUT = HERE / "independent_prediction.json"
CS = HERE.parent / "investigation" / "collected-source"
CRITERION_COMMIT = "be90dbed91"
ORDER = ((0, 0), (0, 1), (1, 0), (1, 1))
TRAINING = (0, 1, 3)
MODEL_NAMES = ("S1_signal", "independent_OR", "named_M3")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def commit_file(commit, path):
    relative = str(path.relative_to(ROOT))
    return subprocess.check_output(["git", "show", commit+":"+relative], cwd=ROOT)


def criterion_freeze():
    commit = subprocess.check_output(["git", "rev-parse", CRITERION_COMMIT], cwd=ROOT, text=True).strip()
    for path in (CRITERION, HERE/"sources.json"):
        if commit_file(commit, path) != path.read_bytes():
            raise ValueError("frozen specification changed: "+str(path.relative_to(ROOT)))
    subprocess.check_call(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT)
    return {"commit": commit, "criterion_sha256": sha(CRITERION), "sources_sha256": sha(HERE/"sources.json")}


def executable_freeze():
    path = str(Path(__file__).relative_to(ROOT))
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", path], cwd=ROOT, text=True).strip()
    if not commit or commit_file(commit, Path(__file__)) != Path(__file__).read_bytes():
        raise ValueError("commit the complete executable before first numerical execution")
    subprocess.check_call(["git", "merge-base", "--is-ancestor", CRITERION_COMMIT, commit], cwd=ROOT)
    subprocess.check_call(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT)
    return {"commit": commit, "program_sha256": sha(Path(__file__))}


def load_frozen():
    criterion_freeze()
    blocks = re.findall(r"```json\s*(.*?)\s*```", CRITERION.read_text(), re.S)
    if len(blocks) != 1:
        raise ValueError("one machine-readable specification is required")
    spec = json.loads(blocks[0])
    if tuple(spec["models"]) != MODEL_NAMES or tuple(spec["calibration_rows"]) != TRAINING or spec["held_out_row"] != 2:
        raise ValueError("model or calibration/holdout routing changed")
    return spec


def source_bindings():
    criterion_freeze()
    packet = json.loads((HERE/"sources.json").read_text())
    answer = {}
    for row in packet["inputs"]:
        if sha(ROOT/row["path"]) != row["sha256"]:
            raise ValueError("source binding changed: "+row["path"])
        answer[row["path"]] = row["sha256"]
    for commit in packet["source_commits"]:
        subprocess.check_call(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT)
    for path in (CRITERION, HERE/"sources.json", Path(__file__)):
        answer[str(path.relative_to(ROOT))] = sha(path)
    return answer


@functools.lru_cache(maxsize=1)
def native_module():
    source_bindings()
    spec = importlib.util.spec_from_file_location("op_native_full_amplitudes", CS/"independent.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def vertical_vector(degrees):
    radians = math.radians(degrees)
    s, c = math.sin(radians), math.cos(radians)
    return (s, c), (c, -s)


def amplitude_read(state, a, b):
    va, da = vertical_vector(a)
    vb, db = vertical_vector(b)
    groups = [{} for _ in range(7)]
    for (ap, pa, ai, bp, pb, bi), z in state.items():
        entries = []
        if ap == 0:
            label = (ai, bp, pb, bi)
            entries += [(0, label, z*va[pa]), (1, label, z*da[pa])]
        if bp == 0:
            label = (ap, pa, ai, bi)
            entries += [(2, label, z*vb[pb]), (3, label, z*db[pb])]
        if ap == bp == 0:
            label = (ai, bi)
            entries += [(4, label, z*va[pa]*vb[pb]), (5, label, z*da[pa]*vb[pb]), (6, label, z*va[pa]*db[pb])]
        for k, label, value in entries:
            groups[k][label] = groups[k].get(label, 0j)+value
    squared = lambda values: math.fsum(abs(z)**2 for z in values.values())
    tangent = lambda values, derivatives: 2*math.fsum((z.conjugate()*derivatives.get(label, 0j)).real for label, z in values.items())
    return {"A": squared(groups[0]), "B": squared(groups[2]), "J": squared(groups[4]),
            "dA": tangent(groups[0], groups[1]), "dB": tangent(groups[2], groups[3]),
            "dJA": tangent(groups[4], groups[5]), "dJB": tangent(groups[4], groups[6])}


def native_joint_gram(state, scale):
    cc = ({}, {})
    for (ap, pa, ai, bp, pb, bi), z in state.items():
        if ap == bp == 0:
            if pa != pb:
                raise ValueError("native source is outside HH/VV support")
            cc[pa][(ai, bi)] = z
    return {"H": scale*math.fsum(abs(z)**2 for z in cc[0].values()),
            "V": scale*math.fsum(abs(z)**2 for z in cc[1].values()),
            "X": scale*sum(z*cc[1].get(label, 0j).conjugate() for label, z in cc[0].items()).real}


class Forward:
    def __init__(self, state, Q, uA, uB, background_A, background_B, model):
        if model not in MODEL_NAMES:
            raise ValueError("unknown named rate model")
        self.state, self.model = state, model
        self.Q, self.uA, self.uB = Q, uA, uB
        self.bA, self.bB = background_A, background_B

    def read(self, a, b, override=None):
        model = self.model if override is None else override
        z = amplitude_read(self.state, a, b)
        pA, pB, pJ = self.Q*self.uA*z["A"], self.Q*self.uB*z["B"], self.Q*self.uA*self.uB*z["J"]
        dA, dB = self.Q*self.uA*z["dA"], self.Q*self.uB*z["dB"]
        dJA, dJB = self.Q*self.uA*self.uB*z["dJA"], self.Q*self.uA*self.uB*z["dJB"]
        if model == "S1_signal":
            sA, sB, j = pA+self.bA, pB+self.bB, pJ
        elif model == "independent_OR":
            fA, fB = 1-self.bA, 1-self.bB
            sA, sB = self.bA+fA*pA, self.bB+fB*pB
            j = fA*fB*pJ+self.bA*fB*pB+self.bB*fA*pA+self.bA*self.bB
            dJA, dJB = fA*fB*dJA+self.bB*fA*dA, fA*fB*dJB+self.bA*fB*dB
        elif model == "named_M3":
            sA, sB = pA+self.bA, pB+self.bB
            j = pJ+sA*sB
            dJA, dJB = dJA+dA*sB, dJB+dB*sA
        else:
            raise ValueError("unknown rate override")
        return {"sA": sA, "sB": sB, "j": j, "pA": pA, "pB": pB, "pJ": pJ,
                "dJA": dJA, "dJB": dJB}

    def rates(self, angles, override=None):
        a0, a1, b0, b1 = angles
        rows = [self.read((a0, a1)[a], (b0, b1)[b], override) for a, b in ORDER]
        # Singles are read from calibration cells, not the withheld joint cell.
        rates = {"sA": [rows[0]["sA"], rows[3]["sA"]], "sB": [rows[0]["sB"], rows[1]["sB"]], "j": [row["j"] for row in rows]}
        signal = {"sA": [rows[0]["pA"], rows[3]["pA"]], "sB": [rows[0]["pB"], rows[1]["pB"]], "j": [row["pJ"] for row in rows]}
        return rates, signal

    def score(self, angles, override=None):
        rates, _ = self.rates(angles, override)
        j = rates["j"]
        return j[0]+j[1]+j[2]-j[3]-rates["sA"][0]-rates["sB"][0]

    def derivatives(self, angles):
        a0, a1, b0, b1 = angles
        return [self.read(a1, b0)["dJA"]-self.read(a1, b1)["dJA"],
                self.read(a0, b1)["dJB"]-self.read(a1, b1)["dJB"]]


def design_row(a, b):
    (sa, ca), _ = vertical_vector(a)
    (sb, cb), _ = vertical_vector(b)
    return [sa*sa*sb*sb, ca*ca*cb*cb, 2*sa*ca*sb*cb]


def design_matrix(angles):
    a0, a1, b0, b1 = angles
    return [design_row((a0, a1)[a], (b0, b1)[b]) for a, b in ORDER]


class NotIdentifiable(ValueError):
    pass


def gaussian(matrix, rhs=None, singular_tolerance=1e-14):
    """Partial-pivot elimination; the determinant uses the same row operations."""
    n = len(matrix)
    if any(len(row) != n for row in matrix) or rhs is not None and len(rhs) != n:
        raise ValueError("non-square Gaussian input")
    rows = [list(map(float, row))+([] if rhs is None else [float(rhs[i])]) for i, row in enumerate(matrix)]
    determinant = 1.
    for column in range(n):
        pivot = max(range(column, n), key=lambda index: abs(rows[index][column]))
        value = rows[pivot][column]
        if abs(value) <= singular_tolerance:
            raise NotIdentifiable("predeclared calibration minor is singular")
        if pivot != column:
            rows[column], rows[pivot] = rows[pivot], rows[column]
            determinant = -determinant
        determinant *= rows[column][column]
        for index in range(column+1, n):
            multiplier = rows[index][column]/rows[column][column]
            rows[index][column] = 0.
            for k in range(column+1, len(rows[index])):
                rows[index][k] -= multiplier*rows[column][k]
    if rhs is None:
        return determinant
    solution = [0.]*n
    for index in reversed(range(n)):
        solution[index] = (rows[index][n]-sum(rows[index][k]*solution[k] for k in range(index+1, n)))/rows[index][index]
    return solution, determinant


def cofactors(matrix, singular_tolerance):
    values = []
    for omitted in range(4):
        try:
            value = gaussian([row for index, row in enumerate(matrix) if index != omitted], singular_tolerance=singular_tolerance)
        except NotIdentifiable:
            value = 0.
        values.append((-1)**omitted*value)
    return values


def calibration_view(rates):
    """This view has no held-out joint value for the inverse to consume."""
    return {"sA": list(rates["sA"]), "sB": list(rates["sB"]),
            "j": [rates["j"][0], rates["j"][1], rates["j"][3]]}


def corrected_entry(j, sA, sB, model, background):
    bA, bB = background
    if model == "S1_signal":
        return j
    if model == "independent_OR":
        return j-bB*sA-bA*sB+bA*bB
    if model == "named_M3":
        return j-sA*sB
    raise ValueError("unknown correction branch")


def inverse_predictor(calibration, angles, model, background, *, singular_tolerance=1e-14):
    """Inputs are observables/effects/model/background only; j contains 00,01,11."""
    if len(calibration["j"]) != 3 or len(calibration["sA"]) != 2 or len(calibration["sB"]) != 2:
        raise ValueError("calibration view must contain exactly three training joints and two singles per side")
    matrix = design_matrix(angles)
    training_j = [corrected_entry(j, calibration["sA"][ORDER[index][0]], calibration["sB"][ORDER[index][1]], model, background)
                  for j, index in zip(calibration["j"], TRAINING)]
    values, determinant = gaussian([matrix[index] for index in TRAINING], training_j, singular_tolerance)
    H, V, X = values
    ca = [math.cos(2*math.radians(angle)) for angle in angles[:2]]
    cb = [math.cos(2*math.radians(angle)) for angle in angles[2:]]
    if abs(ca[0]-ca[1]) <= singular_tolerance or abs(cb[0]-cb[1]) <= singular_tolerance:
        raise NotIdentifiable("two-setting single readout is singular")
    beta_a = (calibration["sA"][0]-calibration["sA"][1])/(ca[0]-ca[1])
    beta_b = (calibration["sB"][0]-calibration["sB"][1])/(cb[0]-cb[1])
    alpha_a, alpha_b = calibration["sA"][0]-beta_a*ca[0], calibration["sB"][0]-beta_b*cb[0]
    bA, bB = background
    fA, fB = (1-bA, 1-bB) if model == "independent_OR" else (1., 1.)
    if fA <= 0 or fB <= 0:
        raise NotIdentifiable("OR background branch has no inverse")
    factor = fA*fB
    endpoint_a = ((alpha_a-bA-beta_a)/fA, (alpha_a-bA+beta_a)/fA)
    endpoint_b = ((alpha_b-bB-beta_b)/fB, (alpha_b-bB+beta_b)/fB)
    photon_H, photon_V = H/factor, V/factor
    AH, AV, BH, BV = *endpoint_a, *endpoint_b
    loss = [AH, AV, BH, BV, AH-photon_H, BH-photon_H, AV-photon_V, BV-photon_V,
            1-(AH+BH-photon_H+AV+BV-photon_V)]
    return {"gram": {"H": H, "V": V, "X": X}, "determinant": determinant,
            "held_out_prediction": sum(x*y for x, y in zip(matrix[2], values)),
            "cofactor": cofactors(matrix, singular_tolerance), "psd_slack": H*V-X*X, "loss_slacks": loss,
            "single_coefficients": {"alpha_A": alpha_a, "beta_A": beta_a, "alpha_B": alpha_b, "beta_B": beta_b},
            "OR_cone_scale": factor, "calibration_joint_values": training_j,
            "calibration_rows": list(TRAINING), "held_out_joint_consumed": False}


def prediction_read(inferred, a, b, model, background):
    gram = inferred["gram"]
    joint = sum(design*gram[name] for design, name in zip(design_row(a, b), ("H", "V", "X")))
    coefficients = inferred["single_coefficients"]
    sA = coefficients["alpha_A"]+coefficients["beta_A"]*math.cos(2*math.radians(a))
    sB = coefficients["alpha_B"]+coefficients["beta_B"]*math.cos(2*math.radians(b))
    bA, bB = background
    if model == "independent_OR":
        joint += bB*sA+bA*sB-bA*bB
    elif model == "named_M3":
        joint += sA*sB
    return {"j": joint, "sA": sA, "sB": sB}


def prediction_score(inferred, angles, model, background):
    a0, a1, b0, b1 = angles
    rows = [prediction_read(inferred, (a0, a1)[a], (b0, b1)[b], model, background) for a, b in ORDER]
    return rows[0]["j"]+rows[1]["j"]+rows[2]["j"]-rows[3]["j"]-rows[0]["sA"]-rows[0]["sB"]


def prediction_derivatives(inferred, angles, model):
    H, V, X = (inferred["gram"][name] for name in ("H", "V", "X"))
    coefficients = inferred["single_coefficients"]
    z = H+V+(4*coefficients["beta_A"]*coefficients["beta_B"] if model == "named_M3" else 0.)
    values = []
    for own, partner0, partner1 in ((angles[1], angles[2], angles[3]), (angles[3], angles[0], angles[1])):
        angle, p0, p1 = (2*math.radians(x) for x in (own, partner0, partner1))
        values.append(-z/2*math.sin(angle)*(math.cos(p0)-math.cos(p1))+X*math.cos(angle)*(math.sin(p0)-math.sin(p1)))
    return values


def corrected_joints(rates, model, background):
    # Fourth-cell consumption happens only after inverse_predictor returns.
    return [corrected_entry(rates["j"][index], rates["sA"][a], rates["sB"][b], model, background)
            for index, (a, b) in enumerate(ORDER)]


def evaluate_forward(forward, angles, spec):
    rates, signal = forward.rates(angles)
    background = (forward.bA, forward.bB)
    singular = float(F(spec["singular_absolute_tolerance"]))
    try:
        inferred = inverse_predictor(calibration_view(rates), angles, forward.model, background, singular_tolerance=singular)
    except NotIdentifiable as error:
        return {"status": "NOT_IDENTIFIABLE", "reason": str(error), "rates": rates, "signal": signal}
    corrected = corrected_joints(rates, forward.model, background)
    inferred["held_out_residual"] = corrected[2]-inferred["held_out_prediction"]
    inferred["cofactor_residual"] = sum(x*y for x, y in zip(inferred["cofactor"], corrected))
    paired = [angle+float(F(step)) for angle, step in zip(angles, spec["paired_update_deg"])]
    h = float(F(spec["derivative_step_radians"]))
    fd = []
    for index in (1, 3):
        minus, plus = list(angles), list(angles)
        minus[index] -= math.degrees(h)
        plus[index] += math.degrees(h)
        fd.append((forward.score(plus)-forward.score(minus))/(2*h))
    predicted_derivatives = prediction_derivatives(inferred, angles, forward.model)
    true_derivatives = forward.derivatives(angles)
    predicted_gain = prediction_score(inferred, paired, forward.model, background)-prediction_score(inferred, angles, forward.model, background)
    true_gain = forward.score(paired)-forward.score(angles)
    factor = (1-forward.bA)*(1-forward.bB) if forward.model == "independent_OR" else 1.
    source_gram = native_joint_gram(forward.state, forward.Q*forward.uA*forward.uB)
    probability_tolerance, derivative_tolerance = float(F(spec["probability_tolerance"])), float(F(spec["derivative_tolerance"]))
    checks = {"held_out": abs(inferred["held_out_residual"]) <= probability_tolerance,
              "cofactor": abs(inferred["cofactor_residual"]) <= probability_tolerance,
              "psd": min(inferred["gram"]["H"], inferred["gram"]["V"], inferred["psd_slack"]) >= -probability_tolerance,
              "loss": min(inferred["loss_slacks"]) >= -probability_tolerance,
              "source_gram": max(abs(inferred["gram"][name]/factor-source_gram[name]) for name in source_gram) <= probability_tolerance,
              "derivative": max(abs(x-y) for x, y in zip(predicted_derivatives, true_derivatives)) <= derivative_tolerance,
              "finite_difference": max(abs(x-y) for x, y in zip(predicted_derivatives, fd)) <= derivative_tolerance,
              "paired_gain": abs(predicted_gain-true_gain) <= probability_tolerance}
    return {"status": "PASS" if all(checks.values()) else "FAIL", "rates": rates, "signal": signal,
            "corrected_joint": corrected, "reconstruction": inferred,
            "response": {"derivatives": predicted_derivatives, "direct_derivatives": true_derivatives,
                         "finite_difference": fd, "paired_gain_prediction": predicted_gain, "paired_gain_direct": true_gain},
            "source_gram": source_gram, "checks": checks}


class NoHeldOut(list):
    def __getitem__(self, index):
        if index == 2:
            raise AssertionError("inverse read the held-out joint")
        return super().__getitem__(index)


def compute():
    spec = load_frozen()
    code_freeze = executable_freeze()
    bindings = source_bindings()
    source = native_module()
    recipes = {recipe["name"]: recipe for recipe in source.specification()["fixtures"]}
    parameters = [float(F(spec["rates"][name])) for name in ("Q", "uA", "uB", "background_A", "background_B")]
    rows, forward_map = [], {}
    worst_norm = 0.
    for fixture, p_index, phase_string, a_index, model in itertools.product(spec["fixtures"], range(len(spec["preparations"])),
                                                                          spec["source_phase_pi"], range(len(spec["angles_deg"])), spec["models"]):
        h_raw, v_raw = (float(F(value)) for value in spec["preparations"][p_index])
        normalization = math.hypot(h_raw, v_raw)
        preparation = (h_raw/normalization, v_raw/normalization*cmath.exp(1j*math.pi*float(F(phase_string))))
        state = source.state_from_preparation(recipes[fixture], preparation)
        worst_norm = max(worst_norm, abs(math.fsum(abs(z)**2 for z in state.values())-1))
        angles = [float(F(value)) for value in spec["angles_deg"][a_index]]
        forward = Forward(state, *parameters, model)
        row = evaluate_forward(forward, angles, spec)
        case_id = f"{fixture}/p{p_index}/ph{phase_string}/a{a_index}/{model}"
        row.update({"case_id": case_id, "fixture": fixture, "prep_index": p_index, "phase_pi": phase_string,
                    "angle_index": a_index, "angles_deg": spec["angles_deg"][a_index], "model": model})
        rows.append(row)
        forward_map[case_id] = (forward, angles)
    probability_tolerance = float(F(spec["probability_tolerance"]))
    derivative_tolerance = float(F(spec["derivative_tolerance"]))
    singular = float(F(spec["singular_absolute_tolerance"]))
    by_id = {row["case_id"]: row for row in rows}
    chosen = by_id["all_collected/p1/ph0/a1/named_M3"]
    forward, angles = forward_map[chosen["case_id"]]
    background = (forward.bA, forward.bB)
    guarded = {**chosen["rates"], "j": NoHeldOut(chosen["rates"]["j"])}
    safe_inferred = inverse_predictor(calibration_view(guarded), angles, forward.model, background, singular_tolerance=singular)
    poisoned = {**chosen["rates"], "j": list(chosen["rates"]["j"])}
    poisoned["j"][2] += 1000*probability_tolerance
    poison_inferred = inverse_predictor(calibration_view(poisoned), angles, forward.model, background, singular_tolerance=singular)
    poison_corrected = corrected_joints(poisoned, forward.model, background)
    wrong_gram = {**safe_inferred, "gram": {**safe_inferred["gram"], "X": 2*safe_inferred["gram"]["X"]}}
    wrong_prediction = sum(x*wrong_gram["gram"][name] for x, name in zip(design_matrix(angles)[2], ("H", "V", "X")))
    uncorrected = inverse_predictor(calibration_view(chosen["rates"]), angles, "S1_signal", background, singular_tolerance=singular)
    fake_gram = native_joint_gram(forward.state, forward.Q*forward.uA*forward.uB)
    fake_singles = [[fake_gram["H"]*math.sin(math.radians(angle))**2+fake_gram["V"]*math.cos(math.radians(angle))**2+bg
                     for angle in side] for side, bg in ((angles[:2], forward.bA), (angles[2:], forward.bB))]
    fake_rates = {"j": list(chosen["rates"]["j"]), "sA": fake_singles[0], "sB": fake_singles[1]}
    fake_inferred = inverse_predictor(calibration_view(fake_rates), angles, forward.model, background, singular_tolerance=singular)
    fake_score_difference = abs(prediction_score(fake_inferred, angles, forward.model, background)-forward.score(angles))
    controls = {"all_rows_identifiable": all(row["status"] != "NOT_IDENTIFIABLE" for row in rows),
                "all_held_out_predictions": all(row.get("checks", {}).get("held_out", False) for row in rows),
                "all_cofactor_relations": all(row.get("checks", {}).get("cofactor", False) for row in rows),
                "all_PSD_checks": all(row.get("checks", {}).get("psd", False) for row in rows),
                "all_loss_checks": all(row.get("checks", {}).get("loss", False) for row in rows),
                "all_source_gram_checks": all(row.get("checks", {}).get("source_gram", False) for row in rows),
                "all_analytic_response_checks": all(row.get("checks", {}).get("derivative", False) for row in rows),
                "all_finite_difference_checks": all(row.get("checks", {}).get("finite_difference", False) for row in rows),
                "all_paired_update_checks": all(row.get("checks", {}).get("paired_gain", False) for row in rows),
                "source_normalized": worst_norm <= probability_tolerance,
                "held_out_not_read": safe_inferred["held_out_joint_consumed"] is False,
                "held_out_mutation_keeps_reconstruction": poison_inferred == safe_inferred,
                "held_out_mutation_detected": abs(poison_corrected[2]-poison_inferred["held_out_prediction"]) > probability_tolerance,
                "wrong_coherence_prediction_detected": abs(wrong_prediction-chosen["corrected_joint"][2]) > probability_tolerance,
                "wrong_coherence_PSD_detected": wrong_gram["gram"]["H"]*wrong_gram["gram"]["V"]-wrong_gram["gram"]["X"]**2 < -probability_tolerance,
                "omitted_M3_correction_detected": abs(chosen["rates"]["j"][2]-uncorrected["held_out_prediction"]) > probability_tolerance,
                "joint_partial_trace_fake_singles_detected": fake_score_difference > probability_tolerance}
    first, second = (by_id[f"{fixture}/p0/ph0/a1/S1_signal"] for fixture in ("calibration_I", "calibration_II"))
    controls["same_joint_different_full_singles"] = (max(abs(first["source_gram"][name]-second["source_gram"][name]) for name in ("H", "V", "X")) <= probability_tolerance and
                                                   max(abs(x-y) for x, y in zip(first["rates"]["sA"]+first["rates"]["sB"], second["rates"]["sA"]+second["rates"]["sB"])) > probability_tolerance)
    for name, changed in (("Q_zero", [0., *parameters[1:]]), ("uA_zero", [parameters[0], 0., *parameters[2:]]),
                          ("uB_zero", [*parameters[:2], 0., *parameters[3:]])):
        samples = [Forward(forward.state, *changed, model) for model in spec["models"]]
        controls[name] = all(max(abs(value) for value in item.derivatives(angles)) <= derivative_tolerance and
                             evaluate_forward(item, angles, spec)["status"] == "PASS" for item in samples)
    signal = Forward(forward.state, *parameters, "S1_signal")
    controls["explicit_signal_override"] = abs(forward.score(angles, override="S1_signal")-signal.score(angles)) <= probability_tolerance
    controls["default_M3_changes_score"] = abs(forward.score(angles)-signal.score(angles)) > probability_tolerance
    passed = all(row["status"] == "PASS" for row in rows) and all(controls.values())
    return {"schema": "p23-observable-prediction-independent/v1", "version": spec["version"],
            "criterion_freeze": criterion_freeze(), "executable_freeze": code_freeze, "bindings": bindings,
            "source_mapping_identified": False, "publication_configuration_identified": False, "production_admitted": False,
            "status": "PASS" if passed else "FAIL", "rows": rows, "controls": controls,
            "diagnostics": {"source_norm_error": worst_norm, "fake_single_full_CH_error": fake_score_difference,
                            "held_out_mutation": 1000*probability_tolerance,
                            "omitted_M3_held_out_residual": chosen["rates"]["j"][2]-uncorrected["held_out_prediction"]},
            "inverse_inputs": ["three calibration joints", "two full singles per side", "physical angles", "named model", "background"],
            "coherence_convention": "X=scale*Re(OmegaAB[HH,VV]); design x=2 sin(a)cos(a)sin(b)cos(b)",
            "public_target_role": spec["public_target_role"], "statistical_verdict_enabled": False,
            "bell_event_files_read": 0, "other_implementation_output_used_as_input": False,
            "access_disclosure": "Independent amplitudes and inverse consumer do not read primary code or output; comparison is a separate post-computation mode."}


def append_comparison():
    """Compare existing receipts only; forward and inverse computation are not rerun."""
    spec = load_frozen()
    code_freeze = executable_freeze()
    own = json.loads(OUTPUT.read_text())
    primary_path = HERE/"prediction.json"
    primary = json.loads(primary_path.read_text())
    primary_hash = sha(primary_path)
    import ast
    original_code = commit_file(own["executable_freeze"]["commit"], Path(__file__)).decode()
    def scientific_ast(text):
        tree = ast.parse(text)
        tree.body = [node for node in tree.body if not isinstance(node, ast.FunctionDef) or node.name != "append_comparison"]
        return ast.dump(tree, include_attributes=False)
    original_ast, current_ast = scientific_ast(original_code), scientific_ast(Path(__file__).read_text())
    if original_ast != current_ast:
        raise ValueError("independent scientific implementation changed after first computation")
    own_path, main_path = str(Path(__file__).relative_to(ROOT)), str(primary_path.relative_to(ROOT))
    for path, expected in own["bindings"].items():
        if path not in (own_path, main_path) and sha(ROOT/path) != expected:
            raise ValueError("independent input binding changed: "+path)
    primary_bindings = primary.get("bindings")
    if primary_bindings is None:
        primary_bindings = {row["path"]: row["sha256"] for row in json.loads((HERE/"sources.json").read_text())["inputs"]}
        primary_bindings.update({str(CRITERION.relative_to(ROOT)): primary["criterion_sha256"],
                                 str((HERE/"sources.json").relative_to(ROOT)): primary["sources_sha256"],
                                 str((HERE/"predict.py").relative_to(ROOT)): primary["program_sha256"]})
    for path, expected in primary_bindings.items():
        if sha(ROOT/path) != expected:
            raise ValueError("primary input binding changed: "+path)
    shared = set(own["bindings"]) & set(primary_bindings)
    bindings_agree = all(own["bindings"][path] == primary_bindings[path] for path in shared)
    primary_freeze = primary.get("criterion_freeze", primary.get("freeze", primary))
    version_agrees = own["version"] == primary["version"] == spec["version"]
    freeze_agrees = (own["criterion_freeze"]["criterion_sha256"] == primary_freeze["criterion_sha256"] and
                     own["criterion_freeze"]["sources_sha256"] == primary_freeze["sources_sha256"])
    scope_agrees = all(own[name] is False and primary[name] is False for name in
                       ("source_mapping_identified", "publication_configuration_identified", "production_admitted"))
    index = {row["case_id"]: row for row in primary["rows"]}
    deltas = {"rates": 0., "signal": 0., "corrected_joint": 0., "gram": 0., "held_out": 0.,
              "cofactor": 0., "PSD": 0., "loss": 0., "source_gram": 0., "derivative": 0., "paired_gain": 0.}
    row_status_agrees = True
    for row in own["rows"]:
        other = index[row["case_id"]]
        row_status_agrees = row_status_agrees and row["status"] == other.get("status", "PASS" if all(primary["controls"].values()) else "FAIL")
        if row["status"] == "NOT_IDENTIFIABLE":
            continue
        for name in ("rates", "signal"):
            deltas[name] = max(deltas[name], *(abs(x-y) for field in ("sA", "sB", "j") for x, y in zip(row[name][field], other[name][field])))
        deltas["corrected_joint"] = max(deltas["corrected_joint"], *(abs(x-y) for x, y in zip(row["corrected_joint"], other["corrected_joint"])))
        r1, r2 = row["reconstruction"], other["reconstruction"]
        deltas["gram"] = max(deltas["gram"], *(abs(r1["gram"][name]-r2["gram"][name]) for name in ("H", "V", "X")))
        deltas["held_out"] = max(deltas["held_out"], abs(r1["held_out_prediction"]-r2["held_out_prediction"]), abs(r1["held_out_residual"]-r2["held_out_residual"]))
        norm1, norm2 = max(map(abs, r1["cofactor"])), max(map(abs, r2["cofactor"]))
        deltas["cofactor"] = max(deltas["cofactor"], abs(r1["cofactor_residual"]/norm1-r2["cofactor_residual"]/norm2),
                                 *(abs(x/norm1-y/norm2) for x, y in zip(r1["cofactor"], r2["cofactor"])))
        deltas["PSD"] = max(deltas["PSD"], abs(r1["psd_slack"]-r2["psd_slack"]))
        deltas["loss"] = max(deltas["loss"], *(abs(x-y) for x, y in zip(r1["loss_slacks"], r2["loss_slacks"])))
        deltas["source_gram"] = max(deltas["source_gram"], *(abs(row["source_gram"][name]-other["source_gram"][name]) for name in ("H", "V", "X")))
        deltas["derivative"] = max(deltas["derivative"], *(abs(x-y) for x, y in zip(row["response"]["derivatives"], other["response"]["derivatives"])))
        deltas["paired_gain"] = max(deltas["paired_gain"], *(abs(row["response"][name]-other["response"][name]) for name in ("paired_gain_prediction", "paired_gain_direct")))
    probability_tolerance, derivative_tolerance = float(F(spec["probability_tolerance"])), float(F(spec["derivative_tolerance"]))
    numbers_agree = all(value <= (derivative_tolerance if name == "derivative" else probability_tolerance) for name, value in deltas.items())
    count_agrees = len(own["rows"]) == len(primary["rows"]) == 336
    controls_pass = all(own["controls"].values()) and all(primary["controls"].values())
    passed = bindings_agree and version_agrees and freeze_agrees and scope_agrees and numbers_agree and count_agrees and row_status_agrees and controls_pass
    if sha(primary_path) != primary_hash:
        raise ValueError("primary output changed during comparison; retry comparison only")
    own.setdefault("calculation_implementation", {"program_sha256": own["executable_freeze"]["program_sha256"],
                                                  "first_scientific_receipt_sha256": sha(OUTPUT),
                                                  "scientific_ast_sha256": hashlib.sha256(original_ast.encode()).hexdigest(),
                                                  "primary_output_used_as_input": False})
    own["bindings"][own_path] = sha(Path(__file__))
    own["bindings"][main_path] = primary_hash
    own["comparison"] = {"phase": "post hoc after independent forward/inverse receipt; no scientific computation rerun",
                         "primary_sha256": primary_hash, "primary_bindings": primary_bindings,
                         "comparison_program_freeze": code_freeze, "scientific_implementation_unchanged": True,
                         "source_bindings_agree": bindings_agree, "version_agrees": version_agrees, "freeze_agrees": freeze_agrees,
                         "scope_agrees": scope_agrees, "rows_compared": len(own["rows"]), "row_status_agrees": row_status_agrees,
                         "worst_deltas": deltas, "both_control_sets_pass": controls_pass, "passed": passed}
    own["comparison"]["cofactor_convention"] = "left-null vectors and residuals compared after max-absolute-value normalization"
    OUTPUT.write_text(json.dumps(own, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps({"comparison_passed": passed, "rows_compared": len(own["rows"])}))
    return 0 if passed else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--compare-only", action="store_true")
    args = parser.parse_args()
    if args.compare_only:
        return append_comparison()
    result = compute()
    if not args.check_only:
        OUTPUT.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps({"status": result["status"], "rows": len(result["rows"]), "controls": result["controls"]}))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
