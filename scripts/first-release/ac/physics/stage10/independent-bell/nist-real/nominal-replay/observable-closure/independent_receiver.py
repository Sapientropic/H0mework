#!/usr/bin/env python3
"""Independent branch-vacuum receiver derivatives and coherent endpoint updates."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re

import independent_slice as ef

HERE = Path(__file__).resolve().parent
FREEZE = "db322615f4"
VERSION = "p23-observable-closure-rx0001"
DIRECTIONS = {"Acommon": [1, 1, 0, 0], "Bcommon": [0, 0, 1, 1],
              "mirror0": [1, 0, -1, 0], "mirror1": [0, 1, 0, -1]}


def load():
    config, _, _, fw, old = ef.configuration()
    freeze = ef.frozen(HERE/"receiver-criterion.md", FREEZE)
    ef.frozen(HERE/"receiver-sources.json", FREEZE)
    blocks = re.findall(r"<!-- RX-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- RX-FROZEN-END -->",
                        (HERE/"receiver-criterion.md").read_text(), re.S)
    ef.require(len(blocks) == 1, "nonunique_independent_receiver_contract")
    rx = json.loads(blocks[0])
    manifest = json.loads((HERE/"receiver-sources.json").read_text())
    ef.require(rx["version"] == manifest["version"] == VERSION and rx["status"] == manifest["status"] == "frozen_before_execution" and
               rx["directions"] == DIRECTIONS and rx["direction_order"] == list(DIRECTIONS) and
               rx["signed_update_order"] == [1, -1] and rx["initial_step_degree"] == "1/100" and
               rx["receiver_rounding_half_width_degree"] == "1/20" and rx["halving_candidates"] == 16 and
               rx["strict_improvement_lower_bound"] == "1/10000000000" and
               all(rx[k] is True for k in ("all_retained_scalar_segments_required", "boundary_segments_preserved",
                                           "training_phase_held_fixed_under_receiver_update")) and
               all(rx[k] is False for k in ("source_mapping_identified", "actual_hardware_drive_identified",
                                            "apparatus_optimum_verified", "controller_advance")), "independent_receiver_contract_changed")
    bindings = {}
    for entry in manifest["inputs"]:
        path = (ef.ROOT/entry["path"]).resolve()
        ef.require(path.is_relative_to(ef.ROOT) and ef.digest(path) == entry["sha256"] and entry["path"] not in bindings,
                   "independent_receiver_input_changed")
        bindings[entry["path"]] = entry["sha256"]
    freeze["sources_sha256"] = ef.digest(HERE/"receiver-sources.json")
    return {**config, **rx}, freeze, bindings, fw, old


def source_domain(config, fw, old):
    ci = ef.training_intervals((HERE/config["public_confidence_report"]).resolve())
    view = ef.source_view((HERE/config["public_counts"]).resolve(), ci, old)
    shape = ef.single_shape(view, config, fw)
    polys = ef.polynomials(shape, fw)
    leaves, coverage = ef.partition(shape, polys, config, fw)
    retained = []
    for index, leaf in enumerate(leaves):
        if leaf["status"] == "outside":
            continue
        e = leaf["e"]
        ef.require(e.lo > 0 and e.hi <= min(F(1), shape["r"].lo), "unresolved_receiver_scalar_loss_domain")
        T2 = ef.formal_T2(shape, e)
        ef.require(T2.lo > 0, "unresolved_receiver_source_radical")
        coherence = ef.formal_H0(shape, e)/(shape["g"][0]*T2.sqrt())
        raw = (1-coherence)/2
        lo, hi = max(F(0), raw.lo), min(F(1), raw.hi)
        ef.require(lo <= hi, "empty_receiver_possible_legal_phase_fiber")
        lam = fw.I(lo, hi)
        if leaf["status"] == "inside":
            ef.require(leaf["classification_evidence"]["Pphase"].hi <= 0,
                       "inside_receiver_phase_qualification_missing")
        retained.append({"cover_index": index, "cover_status": leaf["status"], "e": e,
                         "lambda_unconstrained_enclosure": raw, "lambda_legal_fiber_enclosure": lam,
                         "phase_constraint_is_set_intersection": True,
                         "phase_domain_basis": "whole_interval_quartic_inside_qualification" if leaf["status"] == "inside" else
                                               "possible_legal_boundary_fiber_constraint",
                         "source_parameter_clipping_or_recalibration_used": False,
                         "kh": (shape["h"]*(shape["h"]+e)/shape["r"]).sqrt(),
                         "kv": (shape["v"]*(shape["v"]+e)/shape["r"]).sqrt()})
    ef.require(retained and len(retained) == coverage["inside_count"]+coverage["boundary_count"],
               "missing_receiver_scalar_boundary_segment")
    index = next((k for k, leaf in enumerate(leaves) if leaf["status"] == "inside"), None)
    ef.require(index is not None, "receiver_no_canonical_inside_member")
    e = leaves[index]["e"].midpoint()
    canonical = ef.canonical_source(shape, polys, e, fw)
    return view, shape, polys, leaves, coverage, retained, index, canonical


def interval_trig(angle, fw):
    """Fourteen-term endpoint bounds and exact monotonicity on the admitted angular chart."""
    ef.require(-90 <= angle.lo <= angle.hi <= 90, "receiver_trig_chart_unresolved")
    slo, clo = fw.trig(angle.lo)
    shi, chi = fw.trig(angle.hi)
    sin = fw.I(slo.lo, shi.hi)
    cos = fw.I(min(clo.lo, chi.lo), F(1) if angle.lo <= 0 <= angle.hi else max(clo.hi, chi.hi))
    return sin, cos


def projections(angles, direction, shape, fw):
    rate = fw.I(fw.PI_LO, fw.PI_HI)/180
    R = shape["R"]
    values = []
    for angle, speed in zip(angles, direction):
        s, c = interval_trig(angle, fw)
        h, v = R[0][0]*s+R[1][0]*c, R[0][1]*s+R[1][1]*c
        hd, vd = speed*rate*(R[0][0]*c-R[1][0]*s), speed*rate*(R[0][1]*c-R[1][1]*s)
        values.append({"h": h, "v": v, "h_directional_derivative": hd, "v_directional_derivative": vd})
    return values


def local_mean(projection, h, v, scale):
    a, b = projection["h"], projection["v"]
    da, db = projection["h_directional_derivative"], projection["v_directional_derivative"]
    return (h*a.square()+v*b.square())/scale, (2*h*a*da+2*v*b*db)/scale


def branch_cell(a, b, A, B, dA, dB, region, fw):
    U, V = a["h"]*b["h"], a["v"]*b["v"]
    dU = a["h_directional_derivative"]*b["h"]+a["h"]*b["h_directional_derivative"]
    dV = a["v_directional_derivative"]*b["v"]+a["v"]*b["v_directional_derivative"]
    vacua, derivatives, denominators = [], [], []
    for phase in (1, -1):
        k = region["kh"]*U+phase*region["kv"]*V
        dk = region["kh"]*dU+phase*region["kv"]*dV
        D = (1+A)*(1+B)-k.square()
        dD = dA*(1+B)+(1+A)*dB-2*k*dk
        ef.require(D.lo > 0, "receiver_branch_vacuum_denominator_unresolved")
        vacua.append(1/D)
        derivatives.append(-dD/D.square())
        denominators.append(D)
    lam = region["lambda_legal_fiber_enclosure"]
    w = vacua[0]+lam*(vacua[1]-vacua[0])
    dw = derivatives[0]+lam*(derivatives[1]-derivatives[0])
    ef.require(w.lo > 0, "receiver_mixed_vacuum_unresolved")
    return w, dw, denominators


def directional_readback(projected, region, shape, config, fw):
    h, v, r = (shape[k] for k in ("h", "v", "r"))
    meanA = [local_mean(p, h, v, fw.I(1)) for p in projected[:2]]
    meanB = [local_mean(p, h, v, r) for p in projected[2:]]
    ba, bb = map(F, config["background_per_pulse"])
    backgrounds = ((1-ba)*(1-bb))**config["window_pulses"]
    ab, dab, den = [], [], []
    for x, y in ((0, 0), (0, 1), (1, 0), (1, 1)):
        A, dA = meanA[x]
        B, dB = meanB[y]
        w, dw, denominators = branch_cell(projected[x], projected[2+y], A, B, dA, dB, region, fw)
        ab.append(backgrounds*w.power(5))
        dab.append(5*backgrounds*w.power(4)*dw)
        den.extend(denominators)
    A0, dA0 = meanA[0]
    B0, dB0 = meanB[0]
    qa, qb = ((1-ba)/(1+A0)).power(5), ((1-bb)/(1+B0)).power(5)
    dqa, dqb = -5*qa*dA0/(1+A0), -5*qb*dB0/(1+B0)
    ch = ab[0]+ab[1]+ab[2]-ab[3]-qa-qb
    derivative = dab[0]+dab[1]+dab[2]-dab[3]-dqa-dqb
    return {"raw_CH": ch, "directional_derivative_per_degree": derivative,
            "all_eight_branch_vacuum_denominators_positive": True,
            "branch_vacuum_denominator_lower_bound": min(k.lo for k in den),
            "training_phase_held_fixed_under_receiver_update": True}


def mixed_projections(angles, direction, coordinate, shape, fw):
    rate = fw.I(fw.PI_LO, fw.PI_HI)/180
    R, values = shape["R"], []
    for index, (angle, speed) in enumerate(zip(angles, direction)):
        s, c = interval_trig(angle, fw)
        h, v = R[0][0]*s+R[1][0]*c, R[0][1]*s+R[1][1]*c
        hp, vp = rate*(R[0][0]*c-R[1][0]*s), rate*(R[0][1]*c-R[1][1]*s)
        selected = int(index == coordinate)
        values.append({"h": h, "v": v, "hd": speed*hp, "vd": speed*vp,
                       "hj": selected*hp, "vj": selected*vp,
                       "hdj": -speed*selected*rate.square()*h, "vdj": -speed*selected*rate.square()*v})
    return values


def mixed_local_mean(p, h, v, scale):
    return {"value": (h*p["h"].square()+v*p["v"].square())/scale,
            "d": (2*h*p["h"]*p["hd"]+2*v*p["v"]*p["vd"])/scale,
            "j": (2*h*p["h"]*p["hj"]+2*v*p["v"]*p["vj"])/scale,
            "dj": (2*h*(p["hd"]*p["hj"]+p["h"]*p["hdj"])+
                   2*v*(p["vd"]*p["vj"]+p["v"]*p["vdj"]))/scale}


def mixed_branch_cell(a, b, A, B, region, fw):
    U, V = a["h"]*b["h"], a["v"]*b["v"]
    Ud, Vd = a["hd"]*b["h"]+a["h"]*b["hd"], a["vd"]*b["v"]+a["v"]*b["vd"]
    Uj, Vj = a["hj"]*b["h"]+a["h"]*b["hj"], a["vj"]*b["v"]+a["v"]*b["vj"]
    Udj = a["hdj"]*b["h"]+a["hd"]*b["hj"]+a["hj"]*b["hd"]+a["h"]*b["hdj"]
    Vdj = a["vdj"]*b["v"]+a["vd"]*b["vj"]+a["vj"]*b["vd"]+a["v"]*b["vdj"]
    branches = []
    for sign in (1, -1):
        k = region["kh"]*U+sign*region["kv"]*V
        kd, kj = region["kh"]*Ud+sign*region["kv"]*Vd, region["kh"]*Uj+sign*region["kv"]*Vj
        kdj = region["kh"]*Udj+sign*region["kv"]*Vdj
        D = (1+A["value"])*(1+B["value"])-k.square()
        Dd = A["d"]*(1+B["value"])+(1+A["value"])*B["d"]-2*k*kd
        Dj = A["j"]*(1+B["value"])+(1+A["value"])*B["j"]-2*k*kj
        Ddj = (A["dj"]*(1+B["value"])+A["d"]*B["j"]+A["j"]*B["d"]+
               (1+A["value"])*B["dj"]-2*(kd*kj+k*kdj))
        ef.require(D.lo > 0, "receiver_mixed_derivative_vacuum_denominator_unresolved")
        branches.append({"value": 1/D, "d": -Dd/D.square(), "j": -Dj/D.square(),
                         "dj": 2*Dd*Dj/D.power(3)-Ddj/D.square()})
    lam = region["lambda_legal_fiber_enclosure"]
    return {key: branches[0][key]+lam*(branches[1][key]-branches[0][key]) for key in ("value", "d", "j", "dj")}


def explicit_mixed_hessian(projected, region, shape, config, fw):
    h, v, r = (shape[k] for k in ("h", "v", "r"))
    A = [mixed_local_mean(p, h, v, fw.I(1)) for p in projected[:2]]
    B = [mixed_local_mean(p, h, v, r) for p in projected[2:]]
    ba, bb = map(F, config["background_per_pulse"])
    back = ((1-ba)*(1-bb))**config["window_pulses"]
    ab = []
    for x, y in ((0, 0), (0, 1), (1, 0), (1, 1)):
        w = mixed_branch_cell(projected[x], projected[2+y], A[x], B[y], region, fw)
        ab.append(back*(20*w["value"].power(3)*w["d"]*w["j"]+5*w["value"].power(4)*w["dj"]))
    def single(mean, background):
        q = ((1-background)/(1+mean["value"])).power(5)
        return 30*q*mean["d"]*mean["j"]/(1+mean["value"]).square()-5*q*mean["dj"]/(1+mean["value"])
    return ab[0]+ab[1]+ab[2]-ab[3]-single(A[0], ba)-single(B[0], bb)


def whole_hessian_row(angles, direction, retained, shape, config, fw):
    projected = [mixed_projections(angles, direction, coordinate, shape, fw) for coordinate in range(4)]
    rows = []
    for region in retained:
        try:
            row = [explicit_mixed_hessian(p, region, shape, config, fw) for p in projected]
            rows.append({"cover_index": region["cover_index"], "mixed_angle_derivatives_per_degree_squared": row,
                         "status": "FOUR_EXPLICIT_MIXED_ANGLE_DERIVATIVES_ENCLOSED"})
        except (ValueError, ArithmeticError) as error:
            rows.append({"cover_index": region["cover_index"], "status": "MIXED_ANGLE_DERIVATIVES_UNRESOLVED",
                         "reason": str(error)})
    return {"angles_deg": angles, "direction": direction, "scalar_segment_checks": rows,
            "hessian_method": "explicit_source_means_and_two_phase_branch_inverse_determinant_derivatives",
            "all_retained_segments_including_boundaries_checked": len(rows) == len(retained),
            "all_segments_resolved": all(r["status"] == "FOUR_EXPLICIT_MIXED_ANGLE_DERIVATIVES_ENCLOSED" for r in rows),
            "training_phase_held_fixed_under_receiver_update": True}


def whole_domain(angles, direction, retained, shape, config, fw):
    projected = projections(angles, direction, shape, fw)
    checks = []
    for region in retained:
        try:
            value = directional_readback(projected, region, shape, config, fw)
            checks.append({"cover_index": region["cover_index"], "e": region["e"], "cover_status": region["cover_status"],
                           "status": "COMPLETE_SCALAR_SEGMENT_DERIVATIVE_ENCLOSED", **value})
        except (ValueError, ArithmeticError) as error:
            checks.append({"cover_index": region["cover_index"], "e": region["e"], "cover_status": region["cover_status"],
                           "status": "SCALAR_SEGMENT_DERIVATIVE_UNRESOLVED", "reason": str(error)})
    resolved = all(c["status"] == "COMPLETE_SCALAR_SEGMENT_DERIVATIVE_ENCLOSED" for c in checks)
    if resolved:
        values = [c["directional_derivative_per_degree"] for c in checks]
        hull = fw.I(min(v.lo for v in values), max(v.hi for v in values))
    else:
        hull = None
    return {"angles_deg": angles, "direction": direction, "scalar_segment_checks": checks,
            "all_retained_segments_including_boundaries_checked": len(checks) == len(retained),
            "all_segments_resolved": resolved, "directional_derivative_enclosure": hull,
            "uniform_strictly_positive": resolved and hull.lo > 0,
            "uniform_strictly_negative": resolved and hull.hi < 0,
            "pump_response_inputs_used": False}


def centered_refinement(readback, point, hessian, initial, fw):
    for box, outer in zip(readback["angles_deg"], hessian["angles_deg"]):
        ef.require(outer.lo <= box.lo <= box.hi <= outer.hi, "receiver_refinement_outside_paid_hessian_box")
    if not (readback["all_segments_resolved"] and point["all_segments_resolved"] and hessian["all_segments_resolved"]):
        readback["centered_refinement_applied"] = False
        return readback
    offsets = [box-a for box, a in zip(readback["angles_deg"], initial)]
    for check, center, row in zip(readback["scalar_segment_checks"], point["scalar_segment_checks"], hessian["scalar_segment_checks"]):
        ef.require(check["cover_index"] == center["cover_index"] == row["cover_index"], "receiver_mixed_source_segment_mismatch")
        mvt = center["directional_derivative_per_degree"]+sum(
            (h*offset for h, offset in zip(row["mixed_angle_derivatives_per_degree_squared"], offsets)), fw.I(0))
        direct = check["directional_derivative_per_degree"]
        lo, hi = max(direct.lo, mvt.lo), min(direct.hi, mvt.hi)
        ef.require(lo <= hi, "receiver_direct_and_mean_value_gradient_enclosures_disagree")
        check["direct_directional_derivative_enclosure"] = direct
        check["centered_mean_value_directional_derivative_enclosure"] = mvt
        check["directional_derivative_per_degree"] = fw.I(lo, hi)
    values = [c["directional_derivative_per_degree"] for c in readback["scalar_segment_checks"]]
    hull = fw.I(min(v.lo for v in values), max(v.hi for v in values))
    readback.update(directional_derivative_enclosure=hull, uniform_strictly_positive=hull.lo > 0,
                    uniform_strictly_negative=hull.hi < 0, centered_refinement_applied=True,
                    point_angles_deg=initial, paid_hessian_angles_deg=hessian["angles_deg"],
                    mean_value_transport_preserves_same_source=True)
    return readback


def tube_angles(initial, half, direction, step, fw):
    return [fw.I(a-half+min(F(0), d*step), a+half+max(F(0), d*step)) for a, d in zip(initial, direction)]


def fock_score(source, angles, config, fw, old):
    cells, tails = [], []
    for a, b in ((angles[0], angles[2]), (angles[0], angles[3]), (angles[1], angles[2]), (angles[1], angles[3])):
        value, tail = old.coherent_window(source, a, b, config, fw)
        cells.append(value)
        tails.append(tail)
    ch = cells[0]["j"]+cells[1]["j"]+cells[2]["j"]-cells[3]["j"]-cells[0]["sA"]-cells[0]["sB"]
    return {"raw_CH": ch, "cells": cells, "source_pair_tails": tails,
            "finite_prefix_renormalized": False, "same_original_source_used": True}


def updates(initial, retained, shape, canonical, config, fw, old):
    half = F(config["receiver_rounding_half_width_degree"])
    threshold = F(config["strict_improvement_lower_bound"])
    records = []
    point_angles = [fw.I(a) for a in initial]
    box_angles = [fw.I(a-half, a+half) for a in initial]
    partials = []
    for index in range(4):
        unit = [int(k == index) for k in range(4)]
        partials.append({"angle_index": index, "readback": whole_domain(point_angles, unit, retained, shape, config, fw)})
    before = fock_score(canonical, initial, config, fw, old)
    for name in config["direction_order"]:
        direction = config["directions"][name]
        point = whole_domain(point_angles, direction, retained, shape, config, fw)
        rounding = whole_domain(box_angles, direction, retained, shape, config, fw)
        probes, selected, hessian_records, excluded_signs = [], None, [], []
        for sign in config["signed_update_order"]:
            signed = [sign*d for d in direction]
            maximum_tube = tube_angles(initial, half, signed, F(config["initial_step_degree"]), fw)
            hessian = whole_hessian_row(maximum_tube, signed, retained, shape, config, fw)
            hessian_records.append({"sign": sign, "readback": hessian})
            signed_point = whole_domain(point_angles, signed, retained, shape, config, fw)
            signed_rounding = centered_refinement(whole_domain(box_angles, signed, retained, shape, config, fw),
                                                 signed_point, hessian, initial, fw)
            if signed_rounding["all_segments_resolved"] and signed_rounding["directional_derivative_enclosure"].hi <= 0:
                excluded_signs.append({"sign": sign, "rounding_box_readback": signed_rounding,
                                       "reason": "all_candidate_tubes_contain_original_nonpositive_rounding_box",
                                       "all_sixteen_candidates_excluded_by_common_subdomain": True})
                continue
            for k in range(config["halving_candidates"]):
                step = F(config["initial_step_degree"])/(2**k)
                tube = centered_refinement(whole_domain(tube_angles(initial, half, signed, step, fw), signed, retained, shape, config, fw),
                                           signed_point, hessian, initial, fw)
                gain = step*tube["directional_derivative_enclosure"].lo if tube["uniform_strictly_positive"] else None
                passed = gain is not None and gain > threshold
                probe = {"sign": sign, "halving_index": k, "step_degree": step, "tube_readback": tube,
                         "mean_value_improvement_lower_bound": gain,
                         "strict_gain_exceeds_original_raw_CH_tolerance": passed}
                probes.append(probe)
                if passed:
                    new = [a+step*d for a, d in zip(initial, signed)]
                    after = fock_score(canonical, new, config, fw, old)
                    delta = after["raw_CH"]-before["raw_CH"]
                    ef.require(delta.lo > threshold, "independent_Fock_endpoint_strict_gain_unresolved")
                    ef.require(delta.hi >= gain, "independent_Fock_endpoint_and_mean_value_lower_bound_disagree")
                    selected = {"name": name, "sign": sign, "halving_index": k, "step_degree": step,
                                "direction": signed, "updated_angles_deg": new,
                                "mean_value_improvement_lower_bound": gain,
                                "Fock_before": before, "Fock_after": after, "Fock_raw_CH_improvement": delta,
                                "Fock_strict_improvement_verified": True,
                                "covers_entire_printed_rounding_box": True,
                                "first_passing_candidate_in_frozen_signed_halving_order": True,
                                "actual_hardware_drive_identified": False}
                    break
            if selected is not None:
                break
        records.append({"name": name, "direction": direction, "printed_point": point, "rounding_box": rounding,
                        "explicit_mixed_hessian_readbacks": hessian_records, "excluded_signs": excluded_signs,
                        "probes": probes, "selected_update": selected,
                        "outcome": "UNIFORM_SAME_SOURCE_RECEIVER_UPDATE_CERTIFIED" if selected is not None else
                                   "NO_STRICT_RECEIVER_UPDATE_CERTIFIED_UNDER_FROZEN_CANDIDATES"})
    chosen = next((r["selected_update"] for r in records if r["selected_update"] is not None), None)
    return partials, records, chosen


def run():
    program = ef.frozen(__file__)
    config, freeze, bindings, fw, old = load()
    base = {"schema": "p23-independent-receiver-update/v1", "version": VERSION, "program_freeze": program,
            "criterion_freeze": freeze, "bindings": bindings, "retrospective": True, "bell_event_files_read": 0,
            "primary_receiver_code_or_output_read_before_first": False, "source_mapping_identified": False,
            "actual_hardware_drive_identified": False, "apparatus_optimum_verified": False, "controller_advance": False,
            "global_optimum_kernel_proof": False, "whole_Born_identity_kernel_proof": False,
            "full_statistical_fiber_certified": False, "training_phase_held_fixed_under_receiver_update": True,
            "source_parameters_reconstructed_at_perturbed_angles": False,
            "science_first_isolation": "mutually_blind_until_both_first_receipts_completed",
            "first_science_bytes_preserved": True, "stable_math_refinement_after_first_receipts": True,
            "source_model_statistical_domain_and_candidate_rules_changed": False,
            "trig_interval_method": "fourteen_term_endpoint_enclosures_and_monotonicity_on_minus90_to90_degrees"}
    try:
        view, shape, polys, leaves, coverage, retained, index, canonical = source_domain(config, fw, old)
        initial = list(map(F, config["angles_deg"]))
        partials, directions, chosen = updates(initial, retained, shape, canonical, config, fw, old)
        body = {"source_input_view": view, "normalized_source_shape": shape, "source_polynomials": polys,
                "scalar_cover": leaves, "scalar_coverage": coverage, "retained_source_segments": retained,
                "canonical_source": canonical, "canonical_cover_index": index,
                "source_generated_before_receiver_probes": True, "source_receipt_sha256": hashlib.sha256(
                    ef.canonical(old.serial({"view": view, "shape": shape, "retained": retained}))).hexdigest(),
                "single_angle_partials_are_diagnostics": True, "single_angle_partial_diagnostics": partials,
                "direction_records": directions, "canonical_update": chosen,
                "status": "UNIFORM_SAME_SOURCE_RECEIVER_UPDATE_CERTIFIED" if chosen is not None else
                          "NO_STRICT_RECEIVER_UPDATE_CERTIFIED_UNDER_FROZEN_CANDIDATES"}
    except (ValueError, ArithmeticError) as error:
        body = {"status": "RECEIVER_SOURCE_OR_NUMERIC_DOMAIN_UNRESOLVED", "reason": str(error), "canonical_update": None}
    return old.serial({**base, **body})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE/"receiver-independent.json")
    args = parser.parse_args()
    ef.require(not args.output.exists(), "independent_receiver_output_exists_use_new_path")
    result = run()
    text = json.dumps(result, indent=2, allow_nan=False)+"\n"
    args.output.write_text(text)
    print(json.dumps({"output": str(args.output), "status": result["status"], "sha256": hashlib.sha256(text.encode()).hexdigest()}))


if __name__ == "__main__":
    main()
