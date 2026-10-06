"""Six public rates generate all generic source branches and both held-out cells."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
VERSION = "p23-observable-closure-ef0001"


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


def frozen(path):
    path = Path(path).resolve()
    relative = path.relative_to(ROOT).as_posix()
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative],
                                     cwd=ROOT, text=True).strip()
    require(commit and subprocess.check_output(["git", "show", commit+":"+relative], cwd=ROOT)
            == path.read_bytes(), "UNFROZEN_SOURCE:"+relative)
    return {"path": relative, "commit": commit, "sha256": digest(path)}


def configuration():
    criterion = HERE/"criterion.md"
    freeze = frozen(criterion)
    executable = frozen(__file__)
    subprocess.run(["git", "merge-base", "--is-ancestor", freeze["commit"], executable["commit"]],
                   cwd=ROOT, check=True)
    blocks = re.findall(r"```json\s*(.*?)\s*```", criterion.read_text(), re.S)
    require(len(blocks) == 1, "NONUNIQUE_CRITERION")
    config = json.loads(blocks[0])
    manifest = json.loads((HERE/"sources.json").read_text())
    frozen(HERE/"sources.json")
    require(config["version"] == manifest["version"] == VERSION and
            config["status"] == "frozen_before_execution", "WRONG_CRITERION")
    require(config["training_rows"] == [0, 3] and config["held_out_rows"] == [1, 2] and
            config["lambda_domain"] == ["0", "1"] and config["all_real_branches_required"] is True,
            "SOURCE_CONTRACT_CHANGED")
    for item in manifest["inputs"]:
        path = (ROOT/item["path"]).resolve()
        require(path.is_relative_to(ROOT) and digest(path) == item["sha256"], "INPUT_BINDING_CHANGED")
    gaussian = module("_ef_gaussian", HERE.parent/"gaussian-window/gaussian.py")
    gaussian.SCALE = gaussian.arithmetic.PRECISION = 10**config["precision_digits"]
    utility = module("_ef_frame_utility", HERE.parent/"frame-window/forward.py")
    return config, manifest, gaussian, utility, freeze, executable


def training_view(counts):
    require(len(counts) == 4, "INCOMPLETE_PUBLIC_TABLE")
    view = {}
    for index in (0, 3):
        row = counts[index]
        require(len(row) == 4 and all(type(k) is int and k >= 0 for k in row) and sum(row) > 0,
                "INVALID_COMPLETE_TRAINING_ROW")
        view[str(index)] = {"sA": F(row[0]+row[1], sum(row)),
                            "sB": F(row[0]+row[2], sum(row)), "j": F(row[0], sum(row))}
    return view


def quadratic_roots(coefficients, gaussian):
    c, b, a = coefficients
    exact_zero = lambda x: x.lo == x.hi == 0
    if exact_zero(a):
        if exact_zero(b):
            return ("CONTINUOUS_FIBER" if exact_zero(c) else
                    "NO_REAL_CENTER_ROOT" if not c.contains(0) else "COEFFICIENT_UNRESOLVED"), []
        if b.contains(0):
            return "COEFFICIENT_UNRESOLVED", []
        return "LINEAR", [{"root_sign": 0, "multiplicity": 1, "e": -c/b}]
    if a.contains(0):
        return "COEFFICIENT_UNRESOLVED", []
    delta = b.square()-4*a*c
    if delta.hi < 0:
        return "NO_REAL_CENTER_ROOT", []
    if exact_zero(delta):
        return "QUADRATIC_REPEATED", [{"root_sign": 0, "multiplicity": 2, "e": -b/(2*a)}]
    if delta.lo <= 0:
        return "DISCRIMINANT_UNRESOLVED", []
    radical = gaussian.square_root(delta)
    if b.lo > 0 or b.hi < 0:
        bsign = 1 if b.lo > 0 else -1
        q = -(b+bsign*radical)/2
        roots = {-bsign: q/a, bsign: c/q}
    else:
        roots = {sign: (-b+sign*radical)/(2*a) for sign in (-1, 1)}
    return "QUADRATIC_TWO_REAL_ROOTS", [{"root_sign": sign, "multiplicity": 1,
                                          "e": roots[sign]} for sign in (-1, 1)]


def generate(training, config, gaussian, utility):
    require(set(training) == {"0", "3"} and all(set(x) == {"sA", "sB", "j"}
                                                for x in training.values()), "NONTRAINING_SOURCE_INPUT")
    I, sqrt = gaussian.I, gaussian.square_root
    ba, bb = map(F, config["background_per_pulse"])
    angles = list(map(F, config["angles_deg"]))
    means_a, means_b, w = [], [], []
    for key in ("0", "3"):
        row = training[key]
        require(all(isinstance(x, F) and 0 <= x <= 1 for x in row.values()) and
                0 <= 1-row["sA"]-row["sB"]+row["j"] <= 1,
                "INVALID_TRAINING_PROBABILITIES")
        qa = utility.nth_root(1-row["sA"], 5, config["precision_digits"], I)
        qb = utility.nth_root(1-row["sB"], 5, config["precision_digits"], I)
        qab = utility.nth_root(1-row["sA"]-row["sB"]+row["j"], 5,
                               config["precision_digits"], I)
        means_a.append((1-ba)/qa-1)
        means_b.append((1-bb)/qb-1)
        w.append(qab/((1-ba)*(1-bb)))
    trig = lambda a: utility.trig_deg(a, config, gaussian)
    sine, cosine = zip(*(trig(2*a) for a in angles[:2]))
    denominator = sine[1]*means_b[0]-sine[0]*means_b[1]
    if denominator.contains(0):
        return {"status": "DEGENERATE_OR_UNRESOLVED_FIBER", "reason": "SINGLE_RATIO_DENOMINATOR",
                "branches": []}
    r = (sine[1]*means_a[0]-sine[0]*means_a[1])/denominator
    if r.lo <= 0:
        return {"status": "DEGENERATE_OR_UNRESOLVED_FIBER", "reason": "NONPOSITIVE_LOSS_RATIO",
                "branches": []}
    u = [(a+r*b)/2 for a, b in zip(means_a, means_b)]
    z = (u[1]-u[0])/(cosine[0]-cosine[1])
    m = u[0]+z*cosine[0]
    x = -(means_a[0]-r*means_b[0])/(2*sine[0])
    C = sqrt(z.square()+x.square())
    if C.lo <= 0:
        return {"status": "DEGENERATE_OR_UNRESOLVED_FIBER", "reason": "UNIDENTIFIED_SOURCE_AXIS",
                "branches": []}
    h, v = m+C, m-C
    if h.lo <= 0 or v.lo <= 0:
        return {"status": "DEGENERATE_OR_UNRESOLVED_FIBER", "reason": "PURE_OR_NONPOSITIVE_MODE",
                "scaled_source": {"m": m, "z": z, "x": x, "h": h, "v": v}, "branches": []}
    Z, X = z/C, x/C
    U, V = [(c-Z)/2 for c in cosine], [(c+Z)/2 for c in cosine]
    D = [(1+a)*(1+b) for a, b in zip(means_a, means_b)]
    gs = [2*a*b/r for a, b in zip(U, V)]
    # Coefficients are stored in ascending degree. Each operation is directed outward.
    Tsq = [h.square()*v.square(), h*v*(h+v), h*v]
    L, H = [], []
    for i in range(2):
        l0 = D[i]-(h.square()*U[i].square()+v.square()*V[i].square())/r
        l1 = -(h*U[i].square()+v*V[i].square())/r
        L.append((l0, l1))
        square = [l0.square(), 2*l0*l1, l1.square()]
        H.append([w[i]*(square[k]-gs[i].square()*Tsq[k])-
                  (L[i][k] if k < 2 else 0) for k in range(3)])
    coefficients = [gs[1]*H[0][k]-gs[0]*H[1][k] for k in range(3)]
    polynomial_status, roots = quadratic_roots(coefficients, gaussian)
    source = {"status": polynomial_status, "training": training, "mean_A": means_a,
              "mean_B": means_b, "loss_ratio": r, "scaled_source": {"m": m, "z": z, "x": x,
              "h": h, "v": v}, "quadratic_coefficients_ascending": coefficients, "branches": []}
    if not roots:
        return source
    chosen = 0 if not gs[0].contains(0) else 1 if not gs[1].contains(0) else None
    if chosen is None:
        source["status"] = "DEGENERATE_OR_UNRESOLVED_FIBER"
        source["reason"] = "PHASE_UNIDENTIFIED"
        return source
    cr = sqrt((1+Z)/2)
    sr = X/(2*cr)
    vectors = []
    for angle in angles:
        s, c = trig(angle)
        vectors.append((s*cr-c*sr, s*sr+c*cr))
    for root in roots:
        e = root["e"]
        branch = {**root, "status": "PENDING", "exact_source_representation":
                  "real_root_of_source_owned_quadratic_then_rational_and_square_root_readouts"}
        source["branches"].append(branch)
        if e.hi <= 0 or e.lo > 1 or (e.lo > 0 and (e/r).lo > 1):
            branch["status"] = "REJECTED_ILLEGAL_LOSS"
            continue
        if e.lo <= 0 or e.hi > 1 or (e/r).hi > 1:
            branch["status"] = "UNRESOLVED_LOSS_BOUNDARY"
            continue
        T = sqrt(h*v*(h+e)*(v+e))
        hi = H[chosen][0]+e*(H[chosen][1]+e*H[chosen][2])
        coherence = hi/(gs[chosen]*T)
        branch["phase_coherence"] = coherence
        if coherence.hi < -1 or coherence.lo > 1:
            branch["status"] = "REJECTED_ILLEGAL_PHASE_WEIGHT"
            continue
        if coherence.lo < -1 or coherence.hi > 1:
            branch["status"] = "UNRESOLVED_PHASE_BOUNDARY"
            continue
        lam, eta_b = (1-coherence)/2, e/r
        nh, nv = h/e, v/e
        branch.update({"status": "LEGAL_EXACT_ROOT_BRANCH", "lambda": lam, "etaA": e,
                       "etaB": eta_b, "tH": h/(h+e), "tV": v/(v+e),
                       "rotation_cos": cr, "rotation_sin": sr, "cells": []})
        for ax in range(2):
            for by in range(2):
                ah, av = vectors[ax]
                bh, bv = vectors[2+by]
                mu_a, mu_b = e*(nh*ah.square()+nv*av.square()), eta_b*(nh*bh.square()+nv*bv.square())
                kh, kv = sqrt(nh*(1+nh)*e*eta_b), sqrt(nv*(1+nv)*e*eta_b)
                determinants = [(1+mu_a)*(1+mu_b)-(kh*ah*bh+phase*kv*av*bv).square()
                                for phase in (1, -1)]
                require(all(d.lo > 0 for d in determinants), "NONPOSITIVE_SOURCE_VACUUM_DETERMINANT")
                wxy = (1-lam)/determinants[0]+lam/determinants[1]
                p0a = gaussian.power((1-ba)/(1+mu_a), 5)
                p0b = gaussian.power((1-bb)/(1+mu_b), 5)
                p00 = gaussian.power((1-ba)*(1-bb)*wxy, 5)
                ga = 2*ah*bh*av*bv/r
                la = (1+mu_a)*(1+mu_b)-(h*(h+e)*(ah*bh).square()+v*(v+e)*(av*bv).square())/r
                eliminated = (la+(ga/gs[chosen])*hi)/(la.square()-ga.square()*T.square())
                require((eliminated-wxy).contains(0), "ELIMINATED_FORWARD_DISAGREEMENT")
                branch["cells"].append({"setting": [ax, by], "sA": 1-p0a, "sB": 1-p0b,
                                        "j": 1-p0a-p0b+p00, "pulse_no_click_AB": wxy,
                                        "eliminated_pulse_no_click_AB": eliminated,
                                        "outcomes": [1-p0a-p0b+p00, p0b-p00, p0a-p00, p00]})
        residuals = []
        for cell_index, key in ((0, "0"), (3, "3")):
            for feature in ("sA", "sB", "j"):
                residual = branch["cells"][cell_index][feature]-training[key][feature]
                require(residual.contains(0) and residual.hi-residual.lo <= F(config["implementation_tolerance"]),
                        "SIX_RATE_RECONSTRUCTION_UNRESOLVED")
                residuals.append(residual)
        branch["training_residuals"] = residuals
    return source


def confidence_consumer(source, counts, confidence):
    for branch in source["branches"]:
        if branch["status"] != "LEGAL_EXACT_ROOT_BRANCH":
            continue
        included = {feature: [] for feature in ("j", "sA_cell", "sB_cell")}
        for index, cell in enumerate(branch["cells"]):
            for feature, name in (("j", "j"), ("sA", "sA_cell"), ("sB", "sB_cell")):
                c = confidence[name][index]
                included[name].append(F(c["exact_lower"]) <= cell[feature].lo and
                                      cell[feature].hi <= F(c["exact_upper"]))
        branch["confidence_inclusion"] = included
        branch["outcome"] = ("EXHIBITED_CALIBRATION_FREE_SOURCE_MEMBER" if
                              all(all(x) for x in included.values()) else "CENTER_BRANCH_OUTSIDE_ORIGINAL_ENVELOPE")
        branch["held_out_observed_rates"] = [[F(k, sum(counts[index])) for k in counts[index]]
                                              for index in (1, 2)]
    return source


def serial(value, interval):
    if isinstance(value, interval):
        return value.receipt()
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: serial(v, interval) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [serial(v, interval) for v in value]
    return value


def run():
    config, manifest, gaussian, utility, freeze, executable = configuration()
    counts = json.loads((HERE/config["public_counts"]).read_text())["counts"]
    source = generate(training_view(counts), config, gaussian, utility)
    # Neither the training interface nor generate() accepts confidence or held-out rates.
    confidence = json.loads((HERE/config["public_confidence_report"]).read_text())["common_mean_confidence"]
    confidence_consumer(source, counts, confidence)
    return serial({"schema": "p23-observable-closure-primary/v1", "version": VERSION,
                   "criterion_freeze": freeze, "program_freeze": executable,
                   "manifest_sha256": digest(HERE/"sources.json"), "inputs": manifest["inputs"],
                   "training_rows": [0, 3], "held_out_rows": [1, 2], "source": source,
                   "statistics": {"confidence_report_sha256": digest(HERE/config["public_confidence_report"]),
                                  "alpha": config["alpha"], "full_statistical_fiber_certified": False},
                   "retrospective": True, "bell_event_files_read": 0,
                   "source_mapping_identified": False, "publication_configuration_identified": False,
                   "production_admitted": False, "actual_window_model_identified": False,
                   "private_optimizer_input_required": False, "public_Klyshko_input_required": False,
                   "visibility_input_required": False, "actual_pump_actuator_identified": False,
                   "gaussian_vacuum_law_kernel": False, "statistical_coverage_kernel": False,
                   "controller_advance": False}, gaussian.I)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE/"primary.json")
    args = parser.parse_args()
    require(not args.output.exists(), "OUTPUT_EXISTS_USE_NEW_PATH")
    result = run()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False)+"\n")
    print(json.dumps({"output": str(args.output), "status": result["source"]["status"],
                      "branches": [{"status": b["status"], "outcome": b.get("outcome")}
                                   for b in result["source"]["branches"]]}))


if __name__ == "__main__":
    main()
