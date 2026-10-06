#!/usr/bin/env python3
"""Blind six-observable elimination and coherent number-sector forward readback."""
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
FREEZE = "fde5c14df3"
VERSION = "p23-observable-closure-ef0001"
FLAGS = ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
         "actual_window_model_identified", "calibration_protocol_identified", "noise_channel_identified",
         "actual_pump_actuator_identified", "global_optimum_kernel_proof", "controller_advance",
         "full_statistical_fiber_certified")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def frozen(path, commit=None):
    path = Path(path).resolve()
    name = path.relative_to(ROOT).as_posix()
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", name], cwd=ROOT, text=True).strip()
    require(bool(commit) and subprocess.check_output(["git", "show", commit+":"+name], cwd=ROOT) == path.read_bytes(),
            "unfrozen_independent_elimination_program:"+name)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    return {"path": name, "commit": commit, "sha256": digest(path)}


def configuration():
    freeze = frozen(HERE/"criterion.md", FREEZE)
    frozen(HERE/"sources.json", FREEZE)
    text = (HERE/"criterion.md").read_text()
    blocks = re.findall(r"<!-- EF-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- EF-FROZEN-END -->", text, re.S)
    require(len(blocks) == 1, "nonunique_observable_elimination_contract")
    config = json.loads(blocks[0])
    manifest = json.loads((HERE/"sources.json").read_text())
    require(config["version"] == manifest["version"] == VERSION and config["status"] == "frozen_before_execution" and
            all(config[k] is False for k in FLAGS) and config["all_real_branches_required"] is True and
            config["precision_digits"] == 40 and config["independent_terms"] == 14 and config["source_pair_cutoff"] == 6,
            "observable_elimination_scope_changed")
    bindings = {}
    for row in manifest["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and digest(path) == row["sha256"], "observable_elimination_input_changed")
        bindings[row["path"]] = row["sha256"]
    # The library is a definitions-only import; its calibration, loss inverse and pulse are not called.
    utility = HERE.parent/"frame-window/independent.py"
    frozen(utility)
    spec = importlib.util.spec_from_file_location("p23_ef_frozen_coherent_utilities", utility)
    fw = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = fw
    spec.loader.exec_module(fw)
    require(fw.DIGITS == config["precision_digits"] and list(map(F, config["pi"])) == [fw.PI_LO, fw.PI_HI],
            "independent_precision_or_pi_changed")
    freeze["sources_sha256"] = digest(HERE/"sources.json")
    return config, freeze, bindings, fw


def training_view(path):
    """Decode only rows 00/11; the other JSON row values remain uninterpreted."""
    text = Path(path).read_text()
    header = re.search(r'"counts"\s*:\s*\[', text)
    require(header is not None, "missing_public_outcome_matrix")
    selected, index, depth, start = {}, 0, 0, None
    for offset in range(header.end(), len(text)):
        char = text[offset]
        if char == "[":
            if depth == 0:
                start = offset
            depth += 1
        elif char == "]":
            if depth == 0:
                break
            depth -= 1
            if depth == 0:
                if index in (0, 3):
                    selected[index] = json.loads(text[start:offset+1])
                index += 1
    require(index == 4 and set(selected) == {0, 3}, "incomplete_public_training_matrix")
    view = []
    for row_id in (0, 3):
        counts = selected[row_id]
        require(len(counts) == 4 and all(type(x) is int and x >= 0 for x in counts) and sum(counts) > 0,
                "invalid_training_full_outcomes")
        n = sum(counts)
        view.append({"row": row_id, "counts": counts, "denominator": n,
                     "A": F(counts[0]+counts[1], n), "B": F(counts[0]+counts[2], n), "J": F(counts[0], n)})
    return view


def serial(value):
    if isinstance(value, F):
        return str(value)
    if hasattr(value, "packet"):
        return value.packet()
    if isinstance(value, dict):
        return {k: serial(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [serial(v) for v in value]
    return value


def exact_zero(x):
    return x.lo == x.hi == 0


def excludes_zero(x):
    return x.hi < 0 or x.lo > 0


def normalized_shape(view, config, fw):
    I = fw.I
    ba, bb = map(F, config["background_per_pulse"])
    angles = list(map(F, config["angles_deg"]))
    trig = [fw.trig(2*a) for a in angles[:2]]
    s, c = [x[0] for x in trig], [x[1] for x in trig]
    alpha = [(1-ba)/fw.fifth_root(1-row["A"], 40)-1 for row in view]
    beta = [(1-bb)/fw.fifth_root(1-row["B"], 40)-1 for row in view]
    require(all(x.lo > 0 for x in (*alpha, *beta)), "nonpositive_local_mean_or_unresolved_training")
    a_ratio, b_ratio = alpha[1]/alpha[0], beta[1]/beta[0]
    matrix = ((a_ratio*c[0]-c[1], a_ratio*s[0]-s[1]),
              (b_ratio*c[0]-c[1], s[1]-b_ratio*s[0]))
    rhs = (a_ratio-1, b_ratio-1)
    determinant = matrix[0][0]*matrix[1][1]-matrix[0][1]*matrix[1][0]
    require(excludes_zero(determinant), "DEGENERATE_OR_UNRESOLVED_FIBER:normalized_single_ratio_determinant")
    zn = (rhs[0]*matrix[1][1]-matrix[0][1]*rhs[1])/determinant
    xn = (matrix[0][0]*rhs[1]-rhs[0]*matrix[1][0])/determinant
    local0 = 1-zn*c[0]-xn*s[0]
    require(local0.lo > 0, "DEGENERATE_OR_UNRESOLVED_FIBER:single_scale_denominator")
    m = alpha[0]/local0
    r = m*(1-zn*c[0]+xn*s[0])/beta[0]
    radius = zn.square()+xn.square()
    require(m.lo > 0 and r.lo > 0 and radius.lo > 0, "DEGENERATE_OR_UNRESOLVED_FIBER:nonpositive_m_ratio_or_axis")
    cn = radius.sqrt()
    z, x, C = m*zn, m*xn, m*cn
    h, v = m+C, m-C
    require(h.lo > 0 and v.lo > 0, "DEGENERATE_OR_UNRESOLVED_FIBER:nonpositive_or_unresolved_population")
    cos2, sin2 = zn/cn, xn/cn
    c_half = ((1+cos2)/2).sqrt()
    require(c_half.lo > 0, "DEGENERATE_OR_UNRESOLVED_FIBER:Jones_half_angle_boundary")
    s_half = sin2/(2*c_half)
    rotation = ((c_half, s_half), (-s_half, c_half))
    w = [fw.fifth_root(1-row["A"]-row["B"]+row["J"], 40)/((1-ba)*(1-bb)) for row in view]
    U, V = [(a-cos2)/2 for a in c], [(a+cos2)/2 for a in c]
    D = [(1+a)*(1+b) for a, b in zip(alpha, beta)]
    g = [2*u*v0/r for u, v0 in zip(U, V)]
    info = {"single_ratio_matrix": matrix, "single_ratio_rhs": rhs, "single_ratio_determinant": determinant,
            "A1_over_A0": a_ratio, "B1_over_B0": b_ratio, "Z_over_M": zn, "X_over_M": xn,
            "r": r, "m": m, "z": z, "x": x, "C": C, "h": h, "v": v, "R": rotation,
            "cos2delta": cos2, "sin2delta": sin2, "alpha": alpha, "beta": beta, "w": w,
            "U": U, "V": V, "D": D, "g": g,
            "four_single_reconstruction_residuals": [
                {"A": m-z*c[i]-x*s[i]-alpha[i], "B": (m-z*c[i]+x*s[i])/r-beta[i]} for i in range(2)],
            "source_quantization_used": False, "calibration_inputs_used": False}
    return info


def formal_T2(shape, e):
    return shape["h"]*shape["v"]*(shape["h"]+e)*(shape["v"]+e)


def formal_L_H(shape, e, i):
    h, v, r = (shape[k] for k in ("h", "v", "r"))
    u, w = shape["U"][i], shape["V"][i]
    L = shape["D"][i]-(h*(h+e)*u.square()+v*(v+e)*w.square())/r
    H = shape["w"][i]*(L.square()-shape["g"][i].square()*formal_T2(shape, e))-L
    return L, H


def formal_F(shape, e):
    # This polynomial evaluator has no physical source/loss/Born call, including at e=0.
    return shape["g"][1]*formal_L_H(shape, e, 0)[1]-shape["g"][0]*formal_L_H(shape, e, 1)[1]


def all_roots(shape, fw):
    values = [formal_F(shape, fw.I(k)) for k in (0, 1, 2)]
    q = (values[2]-2*values[1]+values[0])/2
    linear = values[1]-values[0]-q
    constant = values[0]
    record = {"formal_values_at_e_0_1_2": values, "coefficients_ascending": [constant, linear, q],
              "e_zero_is_formal_not_physical": True}
    if exact_zero(q):
        if exact_zero(linear):
            return [], {**record, "status": "DEGENERATE_OR_UNRESOLVED_FIBER" if exact_zero(constant) else "NO_REAL_CENTER_BRANCH",
                        "reason": "constant_or_zero_polynomial"}
        if not excludes_zero(linear):
            return [], {**record, "status": "DEGENERATE_OR_UNRESOLVED_FIBER", "reason": "linear_coefficient_unresolved"}
        return [-constant/linear], {**record, "status": "ALL_REAL_ROOT_ENCLOSURES", "degree": 1}
    if not excludes_zero(q):
        return [], {**record, "status": "DEGENERATE_OR_UNRESOLVED_FIBER", "reason": "leading_coefficient_unresolved"}
    discriminant = linear.square()-4*q*constant
    record["discriminant"] = discriminant
    if discriminant.hi < 0:
        return [], {**record, "status": "NO_REAL_CENTER_BRANCH", "degree": 2}
    if discriminant.lo < 0:
        return [], {**record, "status": "DEGENERATE_OR_UNRESOLVED_FIBER", "reason": "discriminant_boundary_unresolved"}
    radical = discriminant.sqrt()
    if excludes_zero(linear):
        sign = 1 if linear.lo > 0 else -1
        stable_numerator = -(linear+sign*radical)/2
        if excludes_zero(stable_numerator):
            roots = [stable_numerator/q, constant/stable_numerator]
            record["root_evaluation"] = "noncancelling_quadratic_numerator_and_product_of_roots"
        else:
            roots = [(-linear-radical)/(2*q), (-linear+radical)/(2*q)]
            record["root_evaluation"] = "direct_two_quadratic_branches"
    else:
        roots = [(-linear-radical)/(2*q), (-linear+radical)/(2*q)]
        record["root_evaluation"] = "direct_two_quadratic_branches"
    if exact_zero(discriminant):
        roots = roots[:1]
    roots.sort(key=lambda x: (x.lo, x.hi))
    return roots, {**record, "status": "ALL_REAL_ROOT_ENCLOSURES", "degree": 2,
                   "double_root": exact_zero(discriminant)}


def legal_source(shape, e, index, fw):
    def illegal(reason):
        return None, {"root_index": index, "e_enclosure": e, "status": "ILLEGAL_CENTER_BRANCH", "reason": reason}
    def unresolved(reason):
        return None, {"root_index": index, "e_enclosure": e, "status": "DEGENERATE_OR_UNRESOLVED_FIBER", "reason": reason}
    if e.hi <= 0 or e.lo > 1 or (e-shape["r"]).lo > 0:
        return illegal("absolute_loss_domain")
    if e.lo <= 0 or e.hi > 1 or (e/shape["r"]).hi > 1:
        return unresolved("absolute_loss_domain_boundary")
    i = 0
    if exact_zero(shape["g"][0]):
        i = 1
    if not excludes_zero(shape["g"][i]):
        return unresolved("selected_training_g_zero_or_unresolved")
    T2 = formal_T2(shape, e)
    if T2.lo <= 0:
        return unresolved("zero_or_unresolved_phase_radical")
    phase_radical = T2.sqrt()
    training = [formal_L_H(shape, e, k) for k in range(2)]
    for k, (L, _) in enumerate(training):
        if (L-shape["g"][k]*phase_radical).lo <= 0 or (L+shape["g"][k]*phase_radical).lo <= 0:
            return unresolved("phase_vacuum_denominator_not_positive")
    phase_coordinate = training[i][1]/(shape["g"][i]*phase_radical)
    if phase_coordinate.hi < -1 or phase_coordinate.lo > 1:
        return illegal("phase_weight_outside_complete_unit_interval")
    if phase_coordinate.lo < -1 or phase_coordinate.hi > 1:
        return unresolved("phase_weight_boundary")
    lam = (1-phase_coordinate)/2
    th = shape["h"]/(shape["h"]+e)
    tv = shape["v"]/(shape["v"]+e)
    require(0 <= tv.lo <= tv.hi < 1 and 0 <= th.lo <= th.hi < 1, "illegal_Fock_source_ratio")
    source = {"root_index": index, "e": e, "etaA": e, "etaB": e/shape["r"], "lambda": lam,
              "tH": th, "tV": tv, "R": shape["R"], "r": shape["r"], "m": shape["m"],
              "z": shape["z"], "x": shape["x"], "h": shape["h"], "v": shape["v"],
              "selected_training_joint": i, "phase_coordinate": phase_coordinate,
              "real_source_descriptor": "all_functions_of_the_selected_real_root_of_frozen_training_polynomial",
              "midpoint_is_source": False, "source_quantization_used": False}
    return source, {"root_index": index, "e_enclosure": e, "status": "LEGAL_CENTER_BRANCH_ENCLOSED",
                    "etaA_positive_le_one": True, "etaB_positive_le_one": True, "lambda_complete_unit_interval": True,
                    "phase_vacuum_denominators_positive": True}


def kernel(source, phase, fw):
    I = fw.I
    diagonal = ((source["tH"].sqrt(), I(0)), (I(0), phase*source["tV"].sqrt()))
    return fw.mm(fw.mm(source["R"], diagonal), fw.transpose(source["R"]))


def detector(angle, transmission, fw):
    s, c = fw.trig(angle)
    return ((1-transmission*s.square(), -transmission*s*c),
            (-transmission*s*c, 1-transmission*c.square()))


def omitted_mass(source, cutoff, fw):
    h, v = source["tH"], source["tV"]
    return h.power(cutoff+1)+(1-h)*sum((h.power(k)*v.power(cutoff+1-k) for k in range(cutoff+1)), fw.I(0))


def coherent_window(source, a, b, config, fw):
    I = fw.I
    cutoff = config["source_pair_cutoff"]
    ea, eb = detector(a, source["etaA"], fw), detector(b, source["etaB"], fw)
    norm = (1-source["tH"])*(1-source["tV"])
    tail = omitted_mass(source, cutoff, fw)
    require(tail.lo >= 0, "negative_omitted_source_mass")
    branches = []
    for phase in (1, -1):
        G = kernel(source, phase, fw)
        ma = fw.mm(fw.mm(fw.transpose(G), ea), G)
        mb = fw.mm(fw.mm(fw.transpose(G), G), fw.transpose(eb))
        mj = fw.mm(ma, fw.transpose(eb))
        values = {}
        for name, matrix in (("A", ma), ("B", mb), ("AB", mj)):
            prefix = norm*sum(fw.complete_homogeneous(fw.trace(matrix), fw.det(matrix), cutoff), I(0))
            values[name] = prefix+I(0, tail.hi)
        branches.append(values)
    # Difference form preserves the shared phase weight without interval dependency on near-one probabilities.
    mixed = {name: branches[0][name]+source["lambda"]*(branches[1][name]-branches[0][name]) for name in ("A", "B", "AB")}
    ba, bb = map(F, config["background_per_pulse"])
    n = config["window_pulses"]
    A = ((1-ba)*mixed["A"]).power(n)
    B = ((1-bb)*mixed["B"]).power(n)
    AB = ((1-ba)*(1-bb)*mixed["AB"]).power(n)
    values = {"j": 1-A-B+AB, "sA": 1-A, "sB": 1-B,
              "outcomes": [1-A-B+AB, B-AB, A-AB, AB]}
    return values, {"source_omitted_mass": tail, "finite_prefix_renormalized": False,
                    "phase_flip_before_explicit_source_R": True, "receiver_effects_unrotated": True,
                    "coherent_Gamma_trace_prefix": True, "cutoff": cutoff, "phase_mixture_before_window": True}


def solve(view, config, fw):
    shape = normalized_shape(view, config, fw)
    roots, polynomial = all_roots(shape, fw)
    sources, root_records = [], []
    for k, root in enumerate(roots):
        source, record = legal_source(shape, root, k, fw)
        root_records.append(record)
        if source is not None:
            sources.append(source)
    return shape, polynomial, root_records, sources


def science():
    executable = frozen(__file__)
    config, freeze, bindings, fw = configuration()
    counts_path = (HERE/config["public_counts"]).resolve()
    view = training_view(counts_path)
    body = {"schema": "p23-observable-closure-independent/v1", "version": VERSION,
            "criterion_freeze": freeze, "executable_freeze": executable, "bindings": bindings,
            "training_rows": view, "retrospective": True, "bell_event_files_read": 0,
            "primary_code_or_outputs_read_before_first": False, "training_centers_are_true_probabilities": False,
            **{k: False for k in FLAGS}}
    try:
        shape, polynomial, root_records, sources = solve(view, config, fw)
    except (ValueError, ArithmeticError) as error:
        return serial({**body, "status": "DEGENERATE_OR_UNRESOLVED_FIBER", "reason": str(error),
                       "source_branches": [], "source_branches_complete_before_heldout_or_confidence_decode": True})
    a0, a1, b0, b1 = map(F, config["angles_deg"])
    probabilities, records = [], []
    tolerance = F(config["implementation_tolerance"])
    # Every source and all predictions are constructed before heldout counts or confidence numbers are decoded.
    for source in sources:
        cells, tails = [], []
        for a, b in ((a0, b0), (a0, b1), (a1, b0), (a1, b1)):
            value, tail = coherent_window(source, a, b, config, fw)
            cells.append(value)
            tails.append(tail)
        residuals = []
        for index, training in zip((0, 3), view):
            residuals.append({name: cells[index][field]-training[name] for name, field in (("A", "sA"), ("B", "sB"), ("J", "j"))})
        readback = all(x.lo <= 0 <= x.hi and x.width <= tolerance for row in residuals for x in row.values())
        feature = {"j": [c["j"] for c in cells], "sA_cell": [c["sA"] for c in cells], "sB_cell": [c["sB"] for c in cells]}
        records.append({"source": source, "status": "SIX_TRAINING_SOURCE_PROBABILITIES_RECONSTRUCTED" if readback else "TRAINING_SOURCE_READBACK_UNRESOLVED",
                        "six_training_residuals": residuals, "all_six_training_centers_contained": readback,
                        "cells": cells, "public_probabilities": feature, "source_pair_tails": tails,
                        "heldout_complete_outcomes_generated_before_comparison": [cells[1]["outcomes"], cells[2]["outcomes"]]})
        probabilities.append(feature)
    # Source phase ends here. Only now are the two heldout rows and original statistical intervals decoded.
    public = json.loads(counts_path.read_text())
    require(public["row_order"] == ["ab", "ab_prime", "a_prime_b", "a_prime_b_prime"] and
            public["outcome_order"] == ["++", "+0", "0+", "00"], "public_row_or_outcome_order_changed")
    confidence = json.loads((HERE/config["public_confidence_report"]).resolve().read_text())["common_mean_confidence"]
    heldout = []
    for index in (1, 2):
        counts = public["counts"][index]
        n = sum(counts)
        heldout.append({"row": index, "counts": counts, "denominator": n, "outcome_rates": [F(x, n) for x in counts]})
    for record in records:
        inclusion = {key: [box.contained(ci["exact_lower"], ci["exact_upper"]) for box, ci in zip(values, confidence[key])]
                     for key, values in record["public_probabilities"].items()}
        record["original_CI_inclusion"] = inclusion
        record["all_twelve_original_CI_contained"] = all(all(v) for v in inclusion.values())
        record["member_outcome"] = ("EXHIBITED_CALIBRATION_FREE_SOURCE_MEMBER" if record["all_twelve_original_CI_contained"] and
            record["all_six_training_centers_contained"] else "CENTER_BRANCH_NOT_CERTIFIED_BY_ORIGINAL_ENCLOSURES")
        record["heldout_outcome_center_residuals"] = [[x-y for x, y in zip(record["cells"][index]["outcomes"], data["outcome_rates"])]
                                                      for index, data in zip((1, 2), heldout)]
    status = ("ALL_CENTER_SOURCE_BRANCHES_RETAINED" if records else
              "DEGENERATE_OR_UNRESOLVED_FIBER" if any(x["status"] == "DEGENERATE_OR_UNRESOLVED_FIBER" for x in root_records) else
              "NO_LEGAL_CENTER_BRANCH" if root_records else polynomial["status"])
    return serial({**body, "status": status, "normalized_source_shape": shape, "polynomial_elimination": polynomial,
                   "all_real_root_checks": root_records, "real_root_count": len(root_records), "legal_branch_count": len(records),
                   "source_branches": records, "heldout_observations": heldout,
                   "source_branches_complete_before_heldout_or_confidence_decode": True,
                   "unknown_loss_and_phase_eliminated_without_calibration": True,
                   "nuisance_inputs_used": [], "no_legal_center_is_not_a_statistical_fiber_rejection": True})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = science()
    text = json.dumps(result, indent=2, allow_nan=False)+"\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
