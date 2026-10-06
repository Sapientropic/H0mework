"""Source-generated rates and a predictor whose inputs are only observables/effects.

The three calibration joints exclude the held-out cell. Model names fix background
semantics before the comparison; tolerances certify implementations, not experiments.
"""
from __future__ import annotations

import argparse
import cmath
import hashlib
import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
CS = HERE.parent / "investigation" / "collected-source"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def criterion():
    text = (HERE / "criterion.md").read_text()
    block = text.split("<!-- OP-FROZEN-BEGIN -->")[1].split("<!-- OP-FROZEN-END -->")[0]
    return json.loads(block.split("```json")[1].split("```")[0])


def number(value):
    result = float(Fraction(value)) if isinstance(value, str) else float(value)
    if not math.isfinite(result):
        raise ValueError("nonfinite observable/effect")
    return result


def load_source():
    spec = importlib.util.spec_from_file_location("op_source", CS / "model.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def design(a, b):
    sa, ca, sb, cb = math.sin(a), math.cos(a), math.sin(b), math.cos(b)
    return [sa * sa * sb * sb, ca * ca * cb * cb, 2 * sa * ca * sb * cb]


def determinant(m):
    a, b, c = m
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def cramer(m, y, tolerance):
    det = determinant(m)
    if abs(det) <= tolerance:
        raise ValueError("NOT_IDENTIFIABLE: fixed calibration minor")
    out = []
    for k in range(3):
        replaced = [row.copy() for row in m]
        for i in range(3):
            replaced[i][k] = y[i]
        out.append(determinant(replaced) / det)
    return out, det


def dot(x, y):
    return math.fsum(a * b for a, b in zip(x, y))


def corrected_joint(rates, model, bg):
    ba, bb = bg
    if model == "S1_signal":
        return rates["j"].copy()
    if model == "named_M3":
        return [rates["j"][2*x+y] - rates["sA"][x] * rates["sB"][y]
                for x in range(2) for y in range(2)]
    if model == "independent_OR":
        return [rates["j"][2*x+y] - bb * rates["sA"][x] - ba * rates["sB"][y] + ba * bb
                for x in range(2) for y in range(2)]
    raise ValueError("unknown predeclared model")


def single_coefficients(values, angles, tolerance):
    cosines = [math.cos(2*a) for a in angles]
    delta = cosines[0] - cosines[1]
    if abs(delta) <= tolerance:
        raise ValueError("NOT_IDENTIFIABLE: single effect contrast")
    beta = (values[0] - values[1]) / delta
    return values[0] - beta * cosines[0], beta


def inverse(rates, angles, model, background, singular_tolerance=1e-14):
    """Only observable rates, public effects, and the named noise law enter here."""
    if len(angles) != 4 or len(background) != 2:
        raise ValueError("wrong effect/background shape")
    angles, background = list(map(number, angles)), list(map(number, background))
    rates = {k: list(map(number, rates[k])) for k in ("sA", "sB", "j")}
    if [len(rates[k]) for k in ("sA", "sB", "j")] != [2, 2, 4]:
        raise ValueError("wrong rate shape")
    if any(not 0 <= b <= 1 for b in background):
        raise ValueError("invalid background probability")
    ba, bb = background
    scale = (1-ba) * (1-bb) if model == "independent_OR" else 1.0
    if scale == 0:
        raise ValueError("NOT_IDENTIFIABLE: certain OR background")
    a0, a1, b0, b1 = angles
    rows = [design(a, b) for a in (a0, a1) for b in (b0, b1)]
    joints = corrected_joint(rates, model, background)
    # Do not pass joints[2] to the calibration solver.
    gram, det = cramer([rows[i] for i in (0, 1, 3)],
                       [joints[i] for i in (0, 1, 3)], singular_tolerance)
    h, v, coherence = gram
    predicted = dot(rows[2], gram)
    cofactor = [(-1)**i * determinant([row for k, row in enumerate(rows) if k != i])
                for i in range(4)]
    norm = max(abs(x) for x in cofactor)
    cofactor = [x/norm for x in cofactor]
    alpha_a, beta_a = single_coefficients(rates["sA"], (a0, a1), singular_tolerance)
    alpha_b, beta_b = single_coefficients(rates["sB"], (b0, b1), singular_tolerance)
    factor_a, factor_b = ((1-ba), (1-bb)) if model == "independent_OR" else (1.0, 1.0)
    ah, av = ((alpha_a-ba-beta_a)/factor_a, (alpha_a-ba+beta_a)/factor_a)
    bh, bv = ((alpha_b-bb-beta_b)/factor_b, (alpha_b-bb+beta_b)/factor_b)
    signal_h, signal_v = h/scale, v/scale
    loss_slacks = [ah, av, bh, bv, ah-signal_h, bh-signal_h,
                   av-signal_v, bv-signal_v,
                   1-(ah+bh-signal_h+av+bv-signal_v)]
    z = h + v + (4*beta_a*beta_b if model == "named_M3" else 0)
    derivatives = [
        (-z*math.sin(2*a1)*(math.cos(2*b0)-math.cos(2*b1))
         + 2*coherence*math.cos(2*a1)*(math.sin(2*b0)-math.sin(2*b1))) / 2,
        (-z*math.sin(2*b1)*(math.cos(2*a0)-math.cos(2*a1))
         + 2*coherence*math.cos(2*b1)*(math.sin(2*a0)-math.sin(2*a1))) / 2,
    ]
    return {"gram": dict(zip(("H", "V", "X"), gram)), "determinant": det,
            "held_out_prediction": predicted, "held_out_residual": joints[2]-predicted,
            "cofactor": cofactor, "cofactor_residual": dot(cofactor, joints),
            "psd_slack": h*v-coherence*coherence, "loss_slacks": loss_slacks,
            "single_coefficients": [alpha_a, beta_a, alpha_b, beta_b],
            "derivatives": derivatives, "corrected_joint": joints, "scale": scale}


def observable_rates(reconstructed, angles, model, bg):
    a0, a1, b0, b1 = angles
    alpha_a, beta_a, alpha_b, beta_b = reconstructed["single_coefficients"]
    sa = [alpha_a+beta_a*math.cos(2*a) for a in (a0, a1)]
    sb = [alpha_b+beta_b*math.cos(2*b) for b in (b0, b1)]
    gram = [reconstructed["gram"][k] for k in ("H", "V", "X")]
    joint = []
    for x, a in enumerate((a0, a1)):
        for y, b in enumerate((b0, b1)):
            value = dot(design(a, b), gram)
            if model == "named_M3":
                value += sa[x]*sb[y]
            elif model == "independent_OR":
                value += bg[1]*sa[x]+bg[0]*sb[y]-bg[0]*bg[1]
            joint.append(value)
    return {"sA": sa, "sB": sb, "j": joint}


def ch(rates):
    j = rates["j"]
    return math.fsum((j[0], j[1], j[2], -j[3], -rates["sA"][0], -rates["sB"][0]))


def read_objects(source_module, objects, angles, q, ua, ub):
    a, b = angles[:2], angles[2:]
    va = [(math.sin(t), math.cos(t)) for t in a]
    vb = [(math.sin(t), math.cos(t)) for t in b]
    return {"sA": [q*ua*source_module.expectation(objects["A"], x) for x in va],
            "sB": [q*ub*source_module.expectation(objects["B"], x) for x in vb],
            "j": [q*ua*ub*source_module.expectation(objects["AB"], [x*y for x in a for y in b])
                  for a in va for b in vb]}


def detection(signal, model, bg):
    ba, bb = bg
    if model == "independent_OR":
        sa = [ba+(1-ba)*p for p in signal["sA"]]
        sb = [bb+(1-bb)*p for p in signal["sB"]]
        joint = [(1-ba)*(1-bb)*signal["j"][2*x+y]
                 + ba*(1-bb)*signal["sB"][y]+bb*(1-ba)*signal["sA"][x]+ba*bb
                 for x in range(2) for y in range(2)]
    elif model in ("S1_signal", "named_M3"):
        sa = [p+ba for p in signal["sA"]]
        sb = [p+bb for p in signal["sB"]]
        joint = [signal["j"][2*x+y]+(sa[x]*sb[y] if model == "named_M3" else 0)
                 for x in range(2) for y in range(2)]
    else:
        raise ValueError("unknown predeclared model")
    return {"sA": sa, "sB": sb, "j": joint}


def generate():
    spec, source_module = criterion(), load_source()
    recipes = {x["name"]: x for x in source_module.frozen()["fixtures"]}
    q, ua, ub, ba, bb = [number(spec["rates"][k]) for k in
                         ("Q", "uA", "uB", "background_A", "background_B")]
    step = number(spec["derivative_step_radians"])
    tol = number(spec["singular_absolute_tolerance"])
    update = [math.radians(number(x)) for x in spec["paired_update_deg"]]
    rows = []
    for name in spec["fixtures"]:
        source = source_module.OpticalSource(recipes[name])
        for pi, preparation in enumerate(spec["preparations"]):
            c, s = map(number, preparation)
            norm = math.hypot(c, s)
            for phase in spec["source_phase_pi"]:
                obj = source.objects_from_preparation(c/norm, s/norm*cmath.exp(1j*math.pi*number(phase)))
                source_gram = {"H": q*ua*ub*obj["AB"][0][0].real,
                               "V": q*ua*ub*obj["AB"][3][3].real,
                               "X": q*ua*ub*obj["AB"][0][3].real}
                for ai, values in enumerate(spec["angles_deg"]):
                    angles = [math.radians(number(x)) for x in values]
                    signal = read_objects(source_module, obj, angles, q, ua, ub)
                    for model in spec["models"]:
                        rates = detection(signal, model, (ba, bb))
                        reconstruction = inverse(rates, angles, model, (ba, bb), tol)
                        finite = []
                        for index in (1, 3):
                            plus, minus = angles.copy(), angles.copy()
                            plus[index] += step
                            minus[index] -= step
                            finite.append((ch(detection(read_objects(source_module, obj, plus, q, ua, ub), model, (ba, bb)))
                                           - ch(detection(read_objects(source_module, obj, minus, q, ua, ub), model, (ba, bb))))/(2*step))
                        moved = [x+d for x, d in zip(angles, update)]
                        direct_gain = ch(detection(read_objects(source_module, obj, moved, q, ua, ub), model, (ba, bb)))-ch(rates)
                        prediction_gain = ch(observable_rates(reconstruction, moved, model, (ba, bb)))-ch(observable_rates(reconstruction, angles, model, (ba, bb)))
                        rows.append({"case_id": f"{name}/p{pi}/ph{phase}/a{ai}/{model}",
                                     "fixture": name, "preparation_index": pi, "phase_pi": phase,
                                     "angles_index": ai, "model": model,
                                     "rates": rates, "signal": signal, "corrected_joint": reconstruction["corrected_joint"],
                                     "reconstruction": {k: v for k, v in reconstruction.items()
                                                        if k not in ("derivatives", "corrected_joint")},
                                     "response": {"derivatives": reconstruction["derivatives"], "finite_difference": finite,
                                                  "paired_gain_prediction": prediction_gain, "paired_gain_direct": direct_gain},
                                     "source_gram": source_gram})
    controls = control_report(rows, recipes, source_module, spec)
    return {"schema": "p23-observable-prediction-primary/v1", "version": spec["version"],
            "criterion_sha256": digest(HERE/"criterion.md"), "sources_sha256": digest(HERE/"sources.json"),
            "program_sha256": digest(__file__), "private_optimizer_input_required": False,
            "source_mapping_identified": False, "publication_configuration_identified": False,
            "production_admitted": False, "bell_event_files_read": 0,
            "rows": rows, "controls": controls}


def control_report(rows, recipes, source_module, spec):
    tol = number(spec["probability_tolerance"])
    bg = [number(spec["rates"][k]) for k in ("background_A", "background_B")]
    angles = [math.radians(number(x)) for x in spec["angles_deg"][1]]
    chosen = {row["model"]: row for row in rows
              if row["fixture"] == "all_collected" and row["preparation_index"] == 1
              and row["phase_pi"] == "0" and row["angles_index"] == 1}
    raw = chosen["S1_signal"]["rates"]
    changed = {k: v.copy() for k, v in raw.items()}
    changed["j"][2] += 1e-7
    disturbed = inverse(changed, angles, "S1_signal", bg)
    original = chosen["S1_signal"]["reconstruction"]["gram"]
    wrong = [original["H"], original["V"], 2*original["X"]]
    wrong_coherence = abs(dot(design(angles[1], angles[2]), wrong)-raw["j"][2]) > tol
    uncorrected = inverse(chosen["named_M3"]["rates"], angles, "S1_signal", bg)["gram"]
    missing_m3 = max(abs(uncorrected[k]-chosen["named_M3"]["source_gram"][k]) for k in original) > tol
    calibration = [next(r for r in rows if r["fixture"] == name and r["preparation_index"] == 0
                        and r["phase_pi"] == "0" and r["angles_index"] == 0 and r["model"] == "S1_signal")
                   for name in ("calibration_I", "calibration_II")]
    joint_same = max(abs(x-y) for x, y in zip(calibration[0]["signal"]["j"], calibration[1]["signal"]["j"])) <= tol
    singles_different = max(abs(x-y) for side in ("sA", "sB")
                            for x, y in zip(calibration[0]["signal"][side], calibration[1]["signal"][side])) > tol
    q, ua, ub = [number(spec["rates"][k]) for k in ("Q", "uA", "uB")]
    obj = source_module.OpticalSource(recipes["calibration_I"]).objects(number("276/961"))
    joint_marginal = {"A": [[obj["AB"][0][0], 0j], [0j, obj["AB"][3][3]]],
                      "B": [[obj["AB"][0][0], 0j], [0j, obj["AB"][3][3]]], "AB": obj["AB"]}
    wrong_singles = read_objects(source_module, joint_marginal, angles, q, ua, ub)
    true_singles = read_objects(source_module, obj, angles, q, ua, ub)
    # The rejection is against this actual source; another source could fit wrong singles.
    marginal_rejected = max(abs(x-y) for side in ("sA", "sB")
                            for x, y in zip(wrong_singles[side], true_singles[side])) > tol
    zero_signal = {"sA": [0.0]*2, "sB": [0.0]*2, "j": [0.0]*4}
    zero_results = [inverse(detection(zero_signal, m, bg), angles, m, bg) for m in spec["models"]]
    singular_rejected = False
    try:
        inverse(raw, [angles[0], angles[0], angles[2], angles[3]], "S1_signal", bg)
    except ValueError as error:
        singular_rejected = "NOT_IDENTIFIABLE" in str(error)
    certain_or_rejected = False
    try:
        inverse(raw, angles, "independent_OR", [1.0, bg[1]])
    except ValueError as error:
        certain_or_rejected = "NOT_IDENTIFIABLE" in str(error)
    return {"held_out_change_rejected": abs(disturbed["held_out_residual"]) > tol,
            "held_out_not_used_for_reconstruction": disturbed["gram"] == original,
            "twice_coherence_lookalike_rejected": wrong_coherence,
            "missing_M3_correction_detected": missing_m3,
            "signal_override_changes_M3_joint": max(abs(x-y) for x,y in zip(chosen["S1_signal"]["rates"]["j"],chosen["named_M3"]["rates"]["j"])) > tol,
            "same_joint_different_complete_singles": joint_same and singles_different,
            "joint_marginal_single_rejected_by_source_consumer": marginal_rejected,
            "zero_Q_response": all(max(abs(v) for v in result["derivatives"]) <= tol for result in zero_results),
            "singular_effect_rejected": singular_rejected, "certain_OR_background_rejected": certain_or_rejected}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    report = generate()
    content = json.dumps(report, indent=2, sort_keys=True, allow_nan=False)+"\n"
    if args.check_only:
        print(content, end="")
    else:
        (HERE / "prediction.json").write_text(content)


if __name__ == "__main__":
    main()
