#!/usr/bin/env python3
"""Independent scalar-source cover and coherent Fock witness for ef0002."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from math import comb
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
FREEZE = "e71683e0bf"
VERSION = "p23-observable-closure-ef0002"
FLAGS = ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
         "actual_window_model_identified", "calibration_protocol_identified", "noise_channel_identified",
         "actual_pump_actuator_identified", "global_optimum_kernel_proof", "controller_advance",
         "full_statistical_fiber_certified", "apparatus_optimum_verified")


def require(value, reason):
    if not value:
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
    require(bool(commit), "uncommitted_independent_slice_program")
    require(subprocess.check_output(["git", "show", commit+":"+name], cwd=ROOT) == path.read_bytes(),
            "unfrozen_independent_slice_program:"+name)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    return {"path": name, "commit": commit, "sha256": digest(path)}


def definitions(path, name):
    frozen(path)
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def configuration():
    freeze = frozen(HERE/"criterion-ef0002.md", FREEZE)
    frozen(HERE/"sources-ef0002.json", FREEZE)
    def block(path, marker):
        sections = re.findall(r"<!-- "+marker+r"-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- "+marker+r"-FROZEN-END -->",
                              path.read_text(), re.S)
        require(len(sections) == 1, "nonunique_independent_slice_contract")
        return json.loads(sections[0])
    parent = block(HERE/"criterion.md", "EF")
    revision = block(HERE/"criterion-ef0002.md", "EF2")
    manifest = json.loads((HERE/"sources-ef0002.json").read_text())
    require(revision["version"] == manifest["version"] == VERSION and
            revision["status"] == manifest["status"] == "frozen_before_execution" and
            revision["training_center_quantities"] == ["sA0", "sB0", "j00", "sA1", "sB1"] and
            revision["training_interval_quantity"] == "joint11_original_po0003_CI" and
            revision["training_rows"] == [0, 3] and revision["held_out_rows"] == [1, 2] and
            revision["scalar_cover_width"] == "1/1099511627776" and
            revision["scalar_cover_depth_cap"] == 64 and revision["scalar_cover_split_cap"] == 32768 and
            revision["boundary_segments_preserved"] is True and
            revision["witness_rule"] == "midpoint_of_first_complete_inside_interval_in_ascending_loss_order",
            "independent_slice_contract_changed")
    config = {**parent, **revision}
    require(config["precision_digits"] == 40 and config["independent_terms"] == 14 and
            config["source_pair_cutoff"] == 6 and config["window_pulses"] == 5 and
            config["lambda_domain"] == ["0", "1"] and config["implementation_tolerance"] == "1/1000000000000" and
            all(config[k] is False for k in FLAGS), "independent_slice_scope_changed")
    bindings = {}
    for row in manifest["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and digest(path) == row["sha256"], "independent_slice_binding_changed")
        require(row["path"] not in bindings, "duplicate_independent_slice_binding")
        bindings[row["path"]] = row["sha256"]
    old = definitions(HERE/"independent.py", "p23_ef2_independent_number_sector_definitions")
    fw = definitions(HERE.parent/"frame-window/independent.py", "p23_ef2_independent_interval_definitions")
    require(fw.DIGITS == 40 and list(map(F, config["pi"])) == [fw.PI_LO, fw.PI_HI],
            "independent_slice_precision_or_pi_changed")
    freeze["sources_sha256"] = digest(HERE/"sources-ef0002.json")
    return config, freeze, bindings, fw, old


def closing(text, start):
    require(text[start] in "[{", "expected_json_container")
    stack, quoted, escaped = [], False, False
    for k in range(start, len(text)):
        c = text[k]
        if quoted:
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                quoted = False
            continue
        if c == '"':
            quoted = True
        elif c in "[{":
            stack.append(c)
        elif c in "]}":
            require(bool(stack) and (stack[-1], c) in (("[", "]"), ("{", "}")), "unbalanced_json_container")
            stack.pop()
            if not stack:
                return k+1
    raise ValueError("unterminated_json_container")


def field_container(text, key, opener):
    matches = list(re.finditer('"'+re.escape(key)+r'"\s*:\s*'+re.escape(opener), text))
    require(len(matches) == 1, "nonunique_selective_json_field:"+key)
    start = matches[0].end()-1
    return text[start:closing(text, start)]


def selected_packets(text, indices):
    require(text[0] == "[", "expected_selected_packet_list")
    chosen, index, pos = {}, 0, 1
    while pos < len(text):
        if text[pos] in " \t\r\n,":
            pos += 1
            continue
        if text[pos] == "]":
            break
        require(text[pos] == "{", "unexpected_confidence_packet")
        end = closing(text, pos)
        if index in indices:
            chosen[index] = json.loads(text[pos:end])
        index, pos = index+1, end
    require(index == 4 and set(chosen) == set(indices), "missing_training_confidence_packet")
    return chosen


def training_intervals(path):
    # Scan past heldout JSON objects without decoding their numbers.
    text = field_container(Path(path).read_text(), "common_mean_confidence", "{")
    result = {}
    for key in ("j", "sA_cell", "sB_cell"):
        packets = selected_packets(field_container(text, key, "["), (0, 3))
        result[key] = {}
        for index, packet in packets.items():
            lo, hi = F(packet["exact_lower"]), F(packet["exact_upper"])
            require(0 <= lo <= hi <= 1, "invalid_training_confidence_interval")
            result[key][index] = (lo, hi)
    return result


def source_view(path, confidence, old):
    rows = old.training_view(path)
    centers = {"sA0": rows[0]["A"], "sB0": rows[0]["B"], "j00": rows[0]["J"],
               "sA1": rows[1]["A"], "sB1": rows[1]["B"]}
    selectors = (("sA0", "sA_cell", 0), ("sB0", "sB_cell", 0), ("j00", "j", 0),
                 ("sA1", "sA_cell", 3), ("sB1", "sB_cell", 3))
    for name, key, index in selectors:
        lo, hi = confidence[key][index]
        require(lo <= centers[name] <= hi, "training_center_outside_original_CI:"+name)
    return {"centers": centers, "joint11_CI": confidence["j"][3],
            "row_denominators": {"00": rows[0]["denominator"], "11": rows[1]["denominator"]},
            "source_input_quantities": ["sA0", "sB0", "j00", "sA1", "sB1", "joint11_CI_lower", "joint11_CI_upper"],
            "joint11_center_used": False, "heldout_outcomes_or_CI_used": False}


def excludes_zero(x):
    return x.hi < 0 or x.lo > 0


def single_shape(view, config, fw):
    ba, bb = map(F, config["background_per_pulse"])
    means = view["centers"]
    trig = [fw.trig(2*a) for a in map(F, config["angles_deg"][:2])]
    s, c = [v[0] for v in trig], [v[1] for v in trig]
    alpha = [(1-ba)/fw.fifth_root(1-means["sA"+str(i)], 40)-1 for i in (0, 1)]
    beta = [(1-bb)/fw.fifth_root(1-means["sB"+str(i)], 40)-1 for i in (0, 1)]
    require(all(v.lo > 0 for v in (*alpha, *beta)), "nonpositive_local_mean")
    ar, br = alpha[1]/alpha[0], beta[1]/beta[0]
    matrix = ((ar*c[0]-c[1], ar*s[0]-s[1]), (br*c[0]-c[1], s[1]-br*s[0]))
    rhs = (ar-1, br-1)
    det = matrix[0][0]*matrix[1][1]-matrix[0][1]*matrix[1][0]
    require(excludes_zero(det), "DEGENERATE_OR_UNRESOLVED_FIBER:single_ratio_determinant")
    zn = (rhs[0]*matrix[1][1]-matrix[0][1]*rhs[1])/det
    xn = (matrix[0][0]*rhs[1]-rhs[0]*matrix[1][0])/det
    local0 = 1-zn*c[0]-xn*s[0]
    require(local0.lo > 0, "DEGENERATE_OR_UNRESOLVED_FIBER:single_scale_denominator")
    m = alpha[0]/local0
    r = m*(1-zn*c[0]+xn*s[0])/beta[0]
    radius = zn.square()+xn.square()
    require(m.lo > 0 and r.lo > 0 and radius.lo > 0, "DEGENERATE_OR_UNRESOLVED_FIBER:axis_or_scale")
    cn = radius.sqrt()
    z, x, C = m*zn, m*xn, m*cn
    h, v = m+C, m-C
    require(v.lo > 0 and h.lo > v.hi, "DEGENERATE_OR_UNRESOLVED_FIBER:pure_or_unresolved_source_modes")
    cos2, sin2 = zn/cn, xn/cn
    ch = ((1+cos2)/2).sqrt()
    require(ch.lo > 0, "DEGENERATE_OR_UNRESOLVED_FIBER:Jones_half_angle_boundary")
    sh = sin2/(2*ch)
    R = ((ch, sh), (-sh, ch))
    window00 = 1-means["sA0"]-means["sB0"]+means["j00"]
    require(0 < window00 <= 1, "invalid_joint00_inverse_root_input")
    w0 = fw.fifth_root(window00, 40)/((1-ba)*(1-bb))
    lo, hi = view["joint11_CI"]
    root_inputs = (1-means["sA1"]-means["sB1"]+lo, 1-means["sA1"]-means["sB1"]+hi)
    require(0 < root_inputs[0] <= root_inputs[1] <= 1, "unresolved_joint11_interval_inverse_root_domain")
    wlo, whi = [fw.fifth_root(k, 40)/((1-ba)*(1-bb)) for k in root_inputs]
    require(wlo.hi <= whi.lo, "unresolved_joint11_pulse_interval_order")
    U, V = [(ci-cos2)/2 for ci in c], [(ci+cos2)/2 for ci in c]
    g = [2*u*vv/r for u, vv in zip(U, V)]
    require(excludes_zero(g[0]), "DEGENERATE_OR_UNRESOLVED_FIBER:g0_zero_or_unresolved")
    return {"r": r, "m": m, "z": z, "x": x, "C": C, "h": h, "v": v, "R": R,
            "cos2delta": cos2, "sin2delta": sin2, "Z_over_M": zn, "X_over_M": xn,
            "single_ratio_matrix": matrix, "single_ratio_rhs": rhs, "single_ratio_determinant": det,
            "A1_over_A0": ar, "B1_over_B0": br, "alpha": alpha, "beta": beta,
            "U": U, "V": V, "D": [(1+a)*(1+b) for a, b in zip(alpha, beta)], "g": g,
            "w0": w0, "wlo": wlo, "whi": whi, "joint11_inverse_root_inputs": root_inputs,
            "four_single_reconstruction_residuals": [
                {"A": m-z*c[i]-x*s[i]-alpha[i], "B": (m-z*c[i]+x*s[i])/r-beta[i]} for i in (0, 1)],
            "source_quantization_used": False, "joint11_center_used": False, "calibration_inputs_used": False}


def padd(a, b, I):
    return [(a[k] if k < len(a) else I(0))+(b[k] if k < len(b) else I(0)) for k in range(max(len(a), len(b)))]


def pscale(a, scalar):
    return [v*scalar for v in a]


def pmul(a, b, I):
    out = [I(0) for _ in range(len(a)+len(b)-1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = out[i+j]+x*y
    return out


def horner(coefficients, e, I):
    result = I(0)
    for value in reversed(coefficients):
        result = result*e+value
    return result


def polynomial_range(coefficients, e, I):
    """Intersect two outward enclosures of the same polynomial on the entire interval."""
    natural = horner(coefficients, e, I)
    mid, radius = e.midpoint(), e.width/2
    translated = [sum((coefficients[j]*comb(j, k)*mid**(j-k) for j in range(k, len(coefficients))), I(0))
                  for k in range(len(coefficients))]
    taylor = translated[0]
    for k in range(1, len(translated)):
        power = I(0, radius**k) if k % 2 == 0 else I(-radius**k, radius**k)
        taylor = taylor+translated[k]*power
    lo, hi = max(natural.lo, taylor.lo), min(natural.hi, taylor.hi)
    require(lo <= hi, "inconsistent_independent_polynomial_enclosures")
    return I(lo, hi)


def formal_T2(shape, e):
    return shape["h"]*shape["v"]*(shape["h"]+e)*(shape["v"]+e)


def formal_L(shape, e, i):
    h, v, r = (shape[k] for k in ("h", "v", "r"))
    return shape["D"][i]-(h*(h+e)*shape["U"][i].square()+v*(v+e)*shape["V"][i].square())/r


def formal_H0(shape, e):
    L = formal_L(shape, e, 0)
    return shape["w0"]*(L.square()-shape["g"][0].square()*formal_T2(shape, e))-L


def polynomials(shape, fw):
    I = fw.I
    h, v, r = (shape[k] for k in ("h", "v", "r"))
    t2 = [h.square()*v.square(), h*v*(h+v), h*v]
    L = [[shape["D"][i]-(h.square()*shape["U"][i].square()+v.square()*shape["V"][i].square())/r,
          -(h*shape["U"][i].square()+v*shape["V"][i].square())/r] for i in (0, 1)]
    values = [formal_H0(shape, I(k)) for k in (0, 1, 2)]
    quadratic = (values[2]-2*values[1]+values[0])/2
    H = [values[0], values[1]-values[0]-quadratic, quadratic]
    Q1 = padd(pmul(L[1], L[1], I), pscale(t2, -shape["g"][1].square()), I)
    N1 = padd(L[1], pscale(H, shape["g"][1]/shape["g"][0]), I)
    phase = padd(pmul(H, H, I), pscale(t2, -shape["g"][0].square()), I)
    low = padd(N1, pscale(Q1, -shape["wlo"]), I)
    high = padd(pscale(Q1, shape["whi"]), pscale(N1, -1), I)
    return {"T2": t2, "L0": L[0], "L1": L[1], "H0": H, "Pphase": phase, "Q1": Q1,
            "N1": N1, "Plow": low, "Phigh": high,
            "formal_H0_values_at_e_0_1_2": values, "e_zero_is_formal_not_physical": True,
            "coefficient_order": "ascending", "range_method": "outward_Horner_intersect_centered_Taylor"}


def partition(shape, polys, config, fw):
    I = fw.I
    upper = min(F(1), shape["r"].hi)
    require(upper > 0, "unresolved_empty_scalar_outer_domain")
    width = F(config["scalar_cover_width"])
    depth_cap, split_cap = config["scalar_cover_depth_cap"], config["scalar_cover_split_cap"]
    stack, leaves, splits, caps = [(F(0), upper, 0)], [], 0, 0
    while stack:
        lo, hi, depth = stack.pop()
        e = I(lo, hi)
        bounds = {key: polynomial_range(polys[key], e, I) for key in ("Pphase", "Plow", "Phigh", "Q1")}
        reasons = []
        if lo > 1 or lo > shape["r"].hi or hi <= 0:
            reasons.append("strict_physical_loss_violation")
        if bounds["Pphase"].lo > 0:
            reasons.append("strict_phase_violation")
        if bounds["Plow"].hi < 0:
            reasons.append("strict_joint11_lower_violation")
        if bounds["Phigh"].hi < 0:
            reasons.append("strict_joint11_upper_violation")
        if bounds["Q1"].hi <= 0:
            reasons.append("joint11_denominator_nonpositive")
        physical = lo > 0 and hi <= min(F(1), shape["r"].lo)
        inside = physical and bounds["Pphase"].hi <= 0 and bounds["Plow"].lo >= 0 and bounds["Phigh"].lo >= 0 and bounds["Q1"].lo > 0
        if reasons:
            status, reason = "outside", reasons
        elif inside:
            status, reason = "inside", ["whole_interval_physical_phase_and_training_constraints"]
        elif hi-lo <= width:
            status, reason = "boundary", ["frozen_width_reached_without_whole_interval_decision"]
        elif depth >= depth_cap or splits >= split_cap:
            status, reason = "boundary", ["frozen_resource_cap_without_whole_interval_decision"]
            caps += 1
        else:
            mid = (lo+hi)/2
            splits += 1
            stack.append((mid, hi, depth+1))
            stack.append((lo, mid, depth+1))
            continue
        leaves.append({"e": e, "depth": depth, "status": status, "classification_evidence": bounds, "reasons": reason})
    require(leaves and leaves[0]["e"].lo == 0 and leaves[-1]["e"].hi == upper and
            all(a["e"].hi == b["e"].lo for a, b in zip(leaves, leaves[1:])), "independent_cover_gap_or_overlap")
    require(all(leaf["e"].width > 0 for leaf in leaves), "zero_width_independent_cover_leaf")
    return leaves, {"outer_domain": I(0, upper), "split_count": splits, "leaf_count": len(leaves),
                    "inside_count": sum(x["status"] == "inside" for x in leaves),
                    "outside_count": sum(x["status"] == "outside" for x in leaves),
                    "boundary_count": sum(x["status"] == "boundary" for x in leaves),
                    "resource_cap_leaf_count": caps, "resource_cap_triggered": caps > 0,
                    "complete_no_gap_no_overlap_partition": True, "all_boundary_segments_preserved": True,
                    "e_zero_only_outer_closure": True}


def cell_polynomials(shape, polys, x, y, config, fw):
    I = fw.I
    angles = list(map(F, config["angles_deg"]))
    sa, ca = fw.trig(angles[x])
    sb, cb = fw.trig(angles[2+y])
    R = shape["R"]
    va = [R[0][k]*sa+R[1][k]*ca for k in (0, 1)]
    vb = [R[0][k]*sb+R[1][k]*cb for k in (0, 1)]
    U, V = va[0]*vb[0], va[1]*vb[1]
    h, v, r = (shape[k] for k in ("h", "v", "r"))
    g = 2*U*V/r
    L = [(1+shape["alpha"][x])*(1+shape["beta"][y])-(h.square()*U.square()+v.square()*V.square())/r,
         -(h*U.square()+v*V.square())/r]
    Q = padd(pmul(L, L, I), pscale(polys["T2"], -g.square()), I)
    N = padd(L, pscale(polys["H0"], g/shape["g"][0]), I)
    return {"x": x, "y": y, "U": U, "V": V, "g": g, "L": L, "Q": Q, "N": N}


def legal_probability_outer(value, I):
    lo, hi = max(F(0), value.lo), min(F(1), value.hi)
    require(lo <= hi, "empty_legal_probability_projection")
    return I(lo, hi)


def analytic_cell_projection(e, cell, shape, config, fw):
    I = fw.I
    ba, bb = map(F, config["background_per_pulse"])
    Q = polynomial_range(cell["Q"], e, I)
    require(Q.lo > 0, "unresolved_cell_vacuum_denominator")
    N = polynomial_range(cell["N"], e, I)
    pulse00 = N/Q
    x, y = cell["x"], cell["y"]
    A = ((1-ba)/(1+shape["alpha"][x])).power(config["window_pulses"])
    B = ((1-bb)/(1+shape["beta"][y])).power(config["window_pulses"])
    AB = ((1-ba)*(1-bb)*pulse00).power(config["window_pulses"])
    raw = {"j": 1-A-B+AB, "sA": 1-A, "sB": 1-B, "outcomes": [1-A-B+AB, B-AB, A-AB, AB]}
    constrained = {k: ([legal_probability_outer(v, I) for v in values] if k == "outcomes" else legal_probability_outer(values, I))
                   for k, values in raw.items()}
    return {"probabilities": constrained, "unconstrained_probabilities": raw, "Q": Q, "N": N,
            "pulse_double_no_click": pulse00, "status": "LEGAL_FIBER_PROJECTION_ENCLOSED",
            "probability_intersection_is_legal_fiber_constraint": True, "source_parameter_clipping_used": False}


def project_regions(leaves, shape, polys, config, fw):
    cells = [cell_polynomials(shape, polys, x, y, config, fw) for x, y in ((0, 1), (1, 0))]
    regions = []
    for index, leaf in enumerate(leaves):
        if leaf["status"] == "outside":
            continue
        paired, failures = [], []
        for cell in cells:
            try:
                value = analytic_cell_projection(leaf["e"], cell, shape, config, fw)
            except (ValueError, ArithmeticError) as error:
                value = {"status": "UNRESOLVED_LEGAL_FIBER_PROJECTION", "reason": str(error),
                         "probabilities": {"j": fw.I(0, 1), "sA": fw.I(0, 1), "sB": fw.I(0, 1),
                                           "outcomes": [fw.I(0, 1) for _ in range(4)]}}
                failures.append(str(error))
            paired.append(value)
        regions.append({"cover_index": index, "e": leaf["e"], "cover_status": leaf["status"],
                        "heldout_rows": [1, 2], "paired_cells": paired, "same_e_for_both_cells": True,
                        "status": "PAIRED_LEGAL_FIBER_PROJECTION_ENCLOSED" if not failures else "PAIRED_PROJECTION_UNRESOLVED",
                        "no_boundary_dropped": True})
    require(len(regions) == sum(x["status"] != "outside" for x in leaves), "missing_independent_slice_region")
    hulls = []
    for slot in (0, 1):
        if not regions:
            hulls.append(None)
            continue
        hull = {}
        for field in ("j", "sA", "sB"):
            values = [r["paired_cells"][slot]["probabilities"][field] for r in regions]
            hull[field] = fw.I(min(v.lo for v in values), max(v.hi for v in values))
        hull["outcomes"] = []
        for k in range(4):
            values = [r["paired_cells"][slot]["probabilities"]["outcomes"][k] for r in regions]
            hull["outcomes"].append(fw.I(min(v.lo for v in values), max(v.hi for v in values)))
        hulls.append(hull)
    return regions, {"heldout_rows": [1, 2], "component_hulls": hulls,
                     "component_hulls_are_joint_feasibility_certificates": False,
                     "unresolved_region_count": sum(r["status"] != "PAIRED_LEGAL_FIBER_PROJECTION_ENCLOSED" for r in regions)}


def canonical_source(shape, polys, e, fw):
    I = fw.I
    require(type(e) is F and 0 < e <= min(F(1), shape["r"].lo), "illegal_canonical_slice_midpoint")
    loss = I(e)
    T2 = formal_T2(shape, loss)
    require(T2.lo > 0, "unresolved_canonical_source_radical")
    coherence = formal_H0(shape, loss)/(shape["g"][0]*T2.sqrt())
    require(-1 <= coherence.lo <= coherence.hi <= 1, "unresolved_canonical_phase_weight")
    lam = (1-coherence)/2
    th, tv = shape["h"]/(shape["h"]+loss), shape["v"]/(shape["v"]+loss)
    require(0 < tv.lo <= tv.hi < 1 and 0 < th.lo <= th.hi < 1, "illegal_canonical_Fock_ratios")
    source = {"e": loss, "etaA": loss, "etaB": loss/shape["r"], "lambda": lam,
              "tH": th, "tV": tv, "R": shape["R"], "r": shape["r"], "m": shape["m"],
              "z": shape["z"], "x": shape["x"], "h": shape["h"], "v": shape["v"],
              "phase_coordinate": coherence,
              "real_source_descriptor": "exact_rational_witness_e_and_observation_generated_real_functions",
              "e_is_chosen_rational_slice_coordinate": True, "parameter_interval_midpoints_used_as_source": False,
              "source_quantization_used": False, "source_parameter_clipping_used": False}
    # The independent polynomial readout is checked against its separately evaluated formal law.
    residual = polynomial_range(polys["H0"], loss, I)-formal_H0(shape, loss)
    require(residual.lo <= 0 <= residual.hi, "canonical_H0_readouts_disagree")
    return source


def canonical_member(leaves, shape, polys, view, config, fw, old):
    index = next((i for i, leaf in enumerate(leaves) if leaf["status"] == "inside"), None)
    if index is None:
        return None
    e = leaves[index]["e"].midpoint()
    source = canonical_source(shape, polys, e, fw)
    a0, a1, b0, b1 = map(F, config["angles_deg"])
    cells, tails = [], []
    for a, b in ((a0, b0), (a0, b1), (a1, b0), (a1, b1)):
        cell, tail = old.coherent_window(source, a, b, config, fw)
        cells.append(cell)
        tails.append(tail)
    pairs = (("sA0", 0, "sA"), ("sB0", 0, "sB"), ("j00", 0, "j"), ("sA1", 3, "sA"), ("sB1", 3, "sB"))
    residuals = {name: cells[row][key]-view["centers"][name] for name, row, key in pairs}
    tolerance = F(config["implementation_tolerance"])
    centers_ok = all(r.lo <= 0 <= r.hi and r.width <= tolerance for r in residuals.values())
    joint_ok = cells[3]["j"].contained(*view["joint11_CI"])
    return {"cover_index": index, "selected_e": e, "source": source, "cells": cells, "source_pair_tails": tails,
            "five_training_center_residuals": residuals, "all_five_training_centers_contained": centers_ok,
            "joint11_original_training_CI_contained": joint_ok,
            "all_six_training_constraints_verified": centers_ok and joint_ok,
            "public_probabilities": {"j": [c["j"] for c in cells], "sA_cell": [c["sA"] for c in cells],
                                     "sB_cell": [c["sB"] for c in cells]},
            "heldout_complete_outcomes_generated_before_comparison": [cells[1]["outcomes"], cells[2]["outcomes"]],
            "witness_rule": config["witness_rule"], "joint11_center_used": False}


def generate(view, config, fw, old):
    shape = single_shape(view, config, fw)
    polys = polynomials(shape, fw)
    leaves, coverage = partition(shape, polys, config, fw)
    regions, projection = project_regions(leaves, shape, polys, config, fw)
    member = canonical_member(leaves, shape, polys, view, config, fw, old)
    return {"source_input_view": view, "normalized_source_shape": shape, "scalar_polynomials": polys,
            "cover": leaves, "coverage": coverage, "paired_regions": regions, "projection_summary": projection,
            "canonical_member": member, "all_source_cover_and_predictions_complete_before_heldout_decode": True,
            "full_statistical_fiber_certified": False}


def compare(result, config, fw):
    public = json.loads((HERE/config["public_counts"]).resolve().read_text())
    require(public["row_order"] == ["ab", "ab_prime", "a_prime_b", "a_prime_b_prime"] and
            public["outcome_order"] == ["++", "+0", "0+", "00"], "changed_public_count_order")
    confidence = json.loads((HERE/config["public_confidence_report"]).resolve().read_text())["common_mean_confidence"]
    heldout = []
    for row in (1, 2):
        counts = public["counts"][row]
        require(len(counts) == 4 and all(type(v) is int and v >= 0 for v in counts) and sum(counts) > 0,
                "invalid_heldout_full_outcomes")
        n = sum(counts)
        heldout.append({"row": row, "counts": counts, "denominator": n, "outcome_rates": [F(v, n) for v in counts]})
    member = result["canonical_member"]
    if member is not None:
        inclusion = {key: [box.contained(ci["exact_lower"], ci["exact_upper"]) for box, ci in zip(values, confidence[key])]
                     for key, values in member["public_probabilities"].items()}
        member["original_CI_inclusion"] = inclusion
        member["all_twelve_original_CI_contained"] = all(all(values) for values in inclusion.values())
        member["member_outcome"] = ("EXHIBITED_CALIBRATION_FREE_SLICE_MEMBER" if member["all_twelve_original_CI_contained"] and
                                    member["all_six_training_constraints_verified"] else "SLICE_MEMBER_NOT_CERTIFIED_BY_ORIGINAL_ENCLOSURES")
        member["heldout_outcome_center_residuals"] = [[x-y for x, y in zip(member["cells"][row]["outcomes"], observed["outcome_rates"])]
                                                     for row, observed in zip((1, 2), heldout)]
    envelope_inclusion = []
    for row, hull in zip((1, 2), result["projection_summary"]["component_hulls"]):
        inclusion = None if hull is None else {
            name: hull[field].contained(confidence[name][row]["exact_lower"], confidence[name][row]["exact_upper"])
            for name, field in (("j", "j"), ("sA_cell", "sA"), ("sB_cell", "sB"))}
        envelope_inclusion.append({"row": row, "original_CI_inclusion": inclusion})
    contained = bool(result["paired_regions"]) and all(row["original_CI_inclusion"] is not None and
                    all(row["original_CI_inclusion"].values()) for row in envelope_inclusion)
    result["projection_summary"]["original_heldout_CI_inclusion"] = envelope_inclusion
    result["projection_summary"]["whole_slice_envelope_contained_in_heldout_CI"] = contained
    result["projection_summary"]["outcome"] = ("SLICE_PREDICTION_ENVELOPE_CONTAINED" if contained else
                                                "SLICE_PREDICTION_ENVELOPE_NOT_CONTAINED")
    result["heldout_observations"] = heldout
    result["status"] = (member["member_outcome"] if member is not None else
                        "SCALAR_COVER_UNRESOLVED_WITHOUT_INSIDE_MEMBER" if result["coverage"]["boundary_count"] else
                        "NO_LEGAL_MEMBER_IN_FIXED_CENTER_SLICE")
    result["statistical_independence_claimed"] = False
    return result


def science():
    executable = frozen(__file__)
    config, freeze, bindings, fw, old = configuration()
    base = {"schema": "p23-observable-closure-independent-slice/v1", "version": VERSION,
            "criterion_freeze": freeze, "executable_freeze": executable, "bindings": bindings,
            "retrospective": True, "bell_event_files_read": 0, "primary_slice_code_or_outputs_read_before_first": False,
            "training_centers_are_true_probabilities": False, "unknown_calibration_inputs_used": [],
            "statistical_independence_claimed": False, **{k: False for k in FLAGS}}
    try:
        ci = training_intervals((HERE/config["public_confidence_report"]).resolve())
        view = source_view((HERE/config["public_counts"]).resolve(), ci, old)
        result = generate(view, config, fw, old)
    except (ValueError, ArithmeticError) as error:
        return old.serial({**base, "status": "DEGENERATE_OR_UNRESOLVED_FIBER", "reason": str(error),
                           "canonical_member": None, "heldout_observations_decoded": False})
    result["source_receipt_sha256_before_heldout_decode"] = hashlib.sha256(canonical(old.serial(result))).hexdigest()
    result = compare(result, config, fw)
    return old.serial({**base, **result})


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
