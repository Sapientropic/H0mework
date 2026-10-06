#!/usr/bin/env python3
"""Public nominal readouts generate one fixed-gain environment source."""
from __future__ import annotations

import argparse
from functools import lru_cache
from fractions import Fraction as F
import itertools
import json
import math
from pathlib import Path
import re
import subprocess
import time

import counts as arithmetic

I, C = arithmetic.I, arithmetic.C
require, rational = arithmetic.require, arithmetic.rational
HERE, ROOT = arithmetic.HERE, arithmetic.ROOT
VERSION = "p23-nominal-environment-calibration-nec0001"
SCHEMA = "p23-nominal-environment-calibration/v1"
CONTRACT_COMMIT = "23294e59d9"
TOL = F("1e-12")
ROOT_WIDTH = F("1e-16")
G_WIDTH = F("1e-22")
A_WIDTH = F("1e-24")
FALSE_FLAGS = ("CH_optimization_executed", "old_scalar_inverse_gain_or_published_controls_admitted",
               "source_mapping_identified", "exact_calibration_inverse_kernel_claim",
               "new_full_Born_or_Gaussian_determinant_kernel_claim",
               "actual_source_or_hardware_identity_verified", "apparatus_optimum_verified", "controller_advance")


class MathUnresolved(ValueError):
    def __init__(self, reason, details):
        super().__init__(reason)
        self.details = details


def close_to(value, target):
    value = I.of(value)
    target = F(target)
    return value.contains(target) or max(value.lo - target, target - value.hi, F(0)) <= TOL


def unit_mapping(text, config):
    pattern = r"(\d+(?:\.\d+)?)\s+\+-\s+(\d+(?:\.\d+)?)\s*%\s*\((Alice|Bob)\)"
    rows = re.findall(pattern, text)
    require(len(rows) == 2 and {r[2] for r in rows} == {"Alice", "Bob"}, "ambiguous_efficiency_unit_text")
    result = {name: (F(center) / 100, F(half) / 100) for center, half, name in rows}
    for party, axis in (("Alice", "K_A"), ("Bob", "K_B")):
        require(result[party] == (rational(config[axis]["center"]), rational(config[axis]["half_width"])),
                "text_machine_efficiency_unit_mismatch")
    return {party: {"center_probability": str(x[0]), "half_width_probability": str(x[1])}
            for party, x in result.items()}


def inputs():
    program = arithmetic.frozen(__file__)
    criterion = arithmetic.frozen(HERE / "calibration-criterion.md", CONTRACT_COMMIT)
    manifest_freeze = arithmetic.frozen(HERE / "calibration-sources.json", CONTRACT_COMMIT)
    subprocess.run(["git", "merge-base", "--is-ancestor", CONTRACT_COMMIT, program["commit"]],
                   cwd=ROOT, check=True)
    blocks = re.findall(r"```json\s*(.*?)\s*```", (HERE / "calibration-criterion.md").read_text(), re.S)
    require(len(blocks) == 1, "nonunique_nominal_calibration_contract")
    config = json.loads(blocks[0])
    manifest = json.loads((HERE / "calibration-sources.json").read_text())
    require(config["version"] == manifest["version"] == VERSION and
            config["status"] == manifest["status"] == "frozen_before_execution", "wrong_calibration_contract")
    require(config["precision_digits"] == 40 and config["source_grid_digits"] == 15 and
            config["source_grid_tie_rule"] == "toward_positive_infinity" and
            rational(config["root_interval_max_width"]) == ROOT_WIDTH and
            rational(config["readout_tolerance"]) == TOL and config["calibration_pulses"] == 1 and
            config["total_pair_prefix"] == 6 and config["prefix_renormalized"] is False,
            "calibration_arithmetic_or_measurement_scope_changed")
    require(all(config[k] is False for k in FALSE_FLAGS) and
            manifest["published_r_angles_or_Table_SII_used_as_inverse_inputs"] is False and
            config["event_files_read"] == manifest["event_files_read"] == 0, "calibration_claim_scope_changed")
    require(config["reference_pump_beta_deg"] == "16" and config["balanced_pump_beta_deg"] == "45" and
            config["source_phase"] == ["1", "0"] and
            config["pair_quantity"] == "probability_at_least_one_total_pair_at_reference_drive" and
            config["coherence_low_domain"] == ["0", ".9"] and
            config["coherence_inverse_domain"] == [".9", "1"], "calibration_source_role_changed")
    bindings = {}
    for row in manifest["inputs"]:
        path = (ROOT / row["path"]).resolve()
        require(path.is_relative_to(ROOT) and arithmetic.digest(path) == row["sha256"],
                "calibration_source_binding_changed:" + row["path"])
        arithmetic.frozen(path)
        bindings[row["path"]] = row["sha256"]
    text = (HERE.parents[1] / "shalm2015-channel-inputs.txt").read_text()
    mapping = unit_mapping(text, config)
    return config, bindings, mapping, {"criterion": criterion, "manifest": manifest_freeze, "program": program}


def hyperbolic(value):
    value = I.of(value)
    require(0 <= value.lo and value.hi <= 1, "hyperbolic_argument_outside_frozen_reduction_domain")
    sh, ch = I(0), I(0)
    for k in range(20):
        sh += value ** (2 * k + 1) / math.factorial(2 * k + 1)
        ch += value ** (2 * k) / math.factorial(2 * k)
    sh += I(0, 2 * value.hi ** 41 / math.factorial(41))
    ch += I(0, 2 * value.hi ** 40 / math.factorial(40))
    return sh / ch


def drive_source(gain, beta):
    gain = I.of(gain)
    beta = rational(beta)
    if beta == 45:
        sine = cosine = I(F(1, 2)).sqrt()
    else:
        sine, cosine = arithmetic.trig_sin_cos(beta)
    gh, gv = gain * cosine, gain * sine
    th, tv = hyperbolic(gh).square(), hyperbolic(gv).square()
    return {"gH": gh, "gV": gv, "tH": th, "tV": tv,
            "Z": (1 - th) * (1 - tv), "q": 1 - (1 - th) * (1 - tv)}


def monotone_root(function, target, low, high, width, cap=256):
    target, low, high, width = map(F, (target, low, high, width))
    left, right = function(I(low)), function(I(high))
    require(left.hi < target < right.lo, "monotone_target_not_strictly_bracketed")
    probes = 2
    for iteration in range(cap):
        if high - low <= width:
            return I(low, high), {"iterations": iteration, "function_probes": probes,
                                  "left_value": function(I(low)).packet(),
                                  "right_value": function(I(high)).packet(),
                                  "entire_root_bracket_transported": True}
        middle = (low + high) / 2
        value = function(I(middle)); probes += 1
        if value.hi < target:
            low = middle
        elif value.lo > target:
            high = middle
        else:
            quarter_low, quarter_high = (low + middle) / 2, (middle + high) / 2
            ql, qh = function(I(quarter_low)), function(I(quarter_high)); probes += 2
            if ql.hi < target < qh.lo:
                low, high = quarter_low, quarter_high
            else:
                raise ValueError("monotone_root_interval_dependency_unresolved")
    raise ValueError("monotone_root_resource_cap")


def nearest_grid(value):
    value = I.of(value)
    scale = 10 ** 15
    def rounded(point):
        shifted = point * scale + F(1, 2)
        return shifted.numerator // shifted.denominator
    a, b = rounded(value.lo), rounded(value.hi)
    require(a == b, "SOURCE_GRID_UNRESOLVED")
    grid = F(a, scale)
    return grid, {"grid_digits": 15, "tie_rule": "toward_positive_infinity",
                  "unique_grid_point": str(grid), "source_interval": value.packet(),
                  "quantization_error": I(value.lo - grid, value.hi - grid).packet()}


@lru_cache(maxsize=16)
def source_from_q(q):
    q = rational(q)
    require(0 < q < 1, "pair_probability_outside_domain")
    function = lambda g: drive_source(g, F(16))["q"]
    gain, root = monotone_root(function, q, 0, 1, G_WIDTH)
    grid_g, grid_g_receipt = nearest_grid(gain)
    reference = drive_source(gain, F(16))
    balanced = drive_source(gain, F(45))
    n = balanced["tH"] / (1 - balanced["tH"])
    grid_n, grid_n_receipt = nearest_grid(n)
    sine, cosine = arithmetic.trig_sin_cos(F(16))
    derivative = 2 * reference["Z"] * (cosine * hyperbolic(reference["gH"]) +
                                         sine * hyperbolic(reference["gV"]))
    require(derivative.lo > 0 and close_to(reference["q"], q), "source_gain_inverse_readback_unresolved")
    return {"G": gain, "G_grid": grid_g, "n": n, "n_grid": grid_n, "t": balanced["tH"],
            "reference": reference, "balanced": balanced,
            "receipt": {"definition": "unique_G_with_q_at_16_degrees", "q_target": str(q),
                "G": gain.packet(), "G_root_certificate": root, "G_grid": grid_g_receipt,
                "balanced_n": n.packet(), "balanced_n_grid": grid_n_receipt,
                "q_readback": reference["q"].packet(), "source_derivative_on_root": derivative.packet(),
                "reference_drive": {k: x.packet() for k, x in reference.items()},
                "balanced_drive": {k: x.packet() for k, x in balanced.items()},
                "grid_is_exact_calibration_kernel": False}}


def ptrim(p):
    p = list(map(F, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p)


def padd(a, b):
    return ptrim([(a[i] if i < len(a) else F(0)) + (b[i] if i < len(b) else F(0))
                  for i in range(max(len(a), len(b)))])


def pscale(p, k):
    return ptrim([x * k for x in p])


def pmul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return ptrim(out)


def pderivative(p):
    return ptrim([i * p[i] for i in range(1, len(p))] or [0])


def peval(p, x):
    value = F(0)
    for coefficient in reversed(p):
        value = value * x + coefficient
    return value


def pdiv(a, b):
    a, b = list(ptrim(a)), ptrim(b)
    require(b != (F(0),), "zero_polynomial_divisor")
    quotient = [F(0)] * max(1, len(a) - len(b) + 1)
    while ptrim(a) != (F(0),) and len(a) >= len(b):
        offset, factor = len(a) - len(b), a[-1] / b[-1]
        quotient[offset] += factor
        for i, coefficient in enumerate(b):
            a[offset + i] -= factor * coefficient
        a = list(ptrim(a))
    return ptrim(quotient), ptrim(a)


def square_free(p):
    a, b = ptrim(p), pderivative(p)
    while b != (F(0),):
        _, remainder = pdiv(a, b)
        a, b = b, remainder
    factor = pscale(a, 1 / a[-1])
    quotient, remainder = pdiv(p, factor)
    require(remainder == (F(0),), "square_free_division_failed")
    return quotient, factor


def sturm_chain(p):
    p, repeated = square_free(p)
    chain = [p, pderivative(p)]
    while chain[-1] != (F(0),):
        _, remainder = pdiv(chain[-2], chain[-1])
        if remainder == (F(0),):
            break
        chain.append(pscale(remainder, -1))
    return p, tuple(chain), repeated


def variation(chain, x):
    signs = [1 if v > 0 else -1 for p in chain if (v := peval(p, x)) != 0]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def root_count_open(p, chain, low, high):
    return variation(chain, low) - variation(chain, high) - int(peval(p, high) == 0)


def all_real_roots(p, width=A_WIDTH):
    original = ptrim(p)
    require(len(original) > 1, "constant_or_zero_calibration_polynomial")
    sf, chain, repeated = sturm_chain(original)
    bound = 1 + max(abs(x / sf[-1]) for x in sf[:-1])
    total = root_count_open(sf, chain, -bound, bound)
    pending = [(-bound, bound, total)]
    roots, nodes = [], 0
    while pending:
        low, high, count = pending.pop(); nodes += 1
        require(nodes <= 10000, "Sturm_isolation_resource_cap")
        if count == 0:
            continue
        if count == 1 and high - low <= width:
            roots.append(I(low, high)); continue
        middle = (low + high) / 2
        middle_root = peval(sf, middle) == 0
        left = root_count_open(sf, chain, low, middle)
        right = root_count_open(sf, chain, middle, high)
        require(left + right + int(middle_root) == count, "Sturm_partition_lost_root")
        if middle_root:
            roots.append(I(middle))
        pending.extend([(middle, high, right), (low, middle, left)])
    roots.sort(key=lambda r: r.lo)
    require(len(roots) == total, "Sturm_root_inventory_incomplete")
    root_receipts = []
    for r in roots:
        count = 1 if r.lo == r.hi else root_count_open(sf, chain, r.lo, r.hi)
        require(count == 1, "Sturm_final_root_not_unique")
        root_receipts.append({"interval": r.packet(), "distinct_root_count": 1,
            "left_variation": variation(chain, r.lo), "right_variation": variation(chain, r.hi),
            "exact_rational_root": r.lo == r.hi})
    return roots, {"polynomial": [str(x) for x in original], "square_free_polynomial": [str(x) for x in sf],
        "repeated_factor": [str(x) for x in repeated], "Sturm_sequence": [[str(x) for x in p] for p in chain],
        "Cauchy_bound": str(bound), "all_real_distinct_root_count": total,
        "isolation_nodes": nodes, "all_real_roots_retained": True, "roots": root_receipts}


def calibration_polynomial(n, ka, kb, ba, bb):
    n, ka, kb, ba, bb = map(F, (n, ka, kb, ba, bb))
    require(n > 0 and 0 < ka < 1 and 0 < kb < 1, "invalid_calibration_seed")
    r, w = kb / ka, 1 + kb / ka - kb
    q = (1 - ba - bb - ba * bb / n,
         ba * r + bb + (bb + r * ba) / n, -r * (1 + 1 / n))
    zeta = (1 - ba) * (1 - bb)
    polynomial = padd(pmul((1, -w), q), pscale(pmul((1, -1), (1, -r)), -zeta))
    low = max(ba, bb / r)
    high = min((ba + n) / (1 + n), (bb + n) / (r * (1 + n)))
    return polynomial, r, (low, high)


def raw_matched(n, ta, tb, ba, bb):
    n, ta, tb = map(I.of, (n, ta, tb))
    pa, pb = 1 / (1 + n * ta), 1 / (1 + n * tb)
    pab = 1 / (1 + n * (ta + tb - ta * tb))
    sa, sb = 1 - (1 - ba) * pa, 1 - (1 - bb) * pb
    joint = 1 - (1 - ba) * pa - (1 - bb) * pb + (1 - ba) * (1 - bb) * pab
    require(sa.lo > 0 and sb.lo > 0, "nonpositive_herald")
    return {"K_A": joint / sb, "K_B": joint / sa, "single_A": sa,
            "single_B": sb, "joint": joint, "no_click_A": pa, "no_click_B": pb, "no_click_AB": pab}


@lru_cache(maxsize=32)
def loss_roots(n_grid, ka, kb, ba, bb):
    p, r, domain = calibration_polynomial(n_grid, ka, kb, ba, bb)
    roots, receipt = all_real_roots(p)
    candidates = []
    for index, a in enumerate(roots):
        row = {"root_index": index, "a": a.packet()}
        if a.hi < domain[0] or a.lo > domain[1]:
            row.update(status="outside_physical_domain", reason="raw_single_outside_scalar_transmission_range")
            candidates.append((None, None, row)); continue
        if a.lo < domain[0] or a.hi > domain[1]:
            row.update(status="UNRESOLVED", reason="root_intersects_physical_boundary")
            candidates.append((None, None, row)); continue
        ta = (a - ba) / (n_grid * (1 - a))
        tb = (r * a - bb) / (n_grid * (1 - r * a))
        if not (0 <= ta.lo <= ta.hi <= 1 and 0 <= tb.lo <= tb.hi <= 1):
            row.update(status="UNRESOLVED", reason="transmission_domain_not_certified")
            candidates.append((None, None, row)); continue
        grid_readout = raw_matched(I(n_grid), ta, tb, ba, bb)
        require(close_to(grid_readout["K_A"], ka) and close_to(grid_readout["K_B"], kb),
                "exact_grid_calibration_root_readback_failed")
        row.update(status="legal_loss_root", TA=ta.packet(), TB=tb.packet(),
                   grid_K_readback={k: v.packet() for k, v in grid_readout.items()})
        candidates.append((ta, tb, row))
    receipt.update(physical_a_domain=[str(x) for x in domain], r=str(r),
                   legal_root_count=sum(ta is not None for ta, _, _ in candidates))
    return candidates, receipt


def allocation(c, name):
    c = I.of(c)
    require(0 <= c.lo <= c.hi <= 1, "coherence_root_outside_domain")
    if name == "symmetric":
        return c, c, I(1), I(1)
    if name == "Alice_rank_one":
        return I(1), c.square(), I(0), 2 * c
    if name == "Bob_rank_one":
        return c.square(), I(1), 2 * c, I(0)
    raise ValueError("unknown_environment_allocation")


def environment_xi(c, name):
    c = I.of(c)
    if name == "symmetric":
        return c.sqrt(), c.sqrt()
    if name == "Alice_rank_one":
        return I(1), c
    if name == "Bob_rank_one":
        return c, I(1)
    raise ValueError("unknown_environment_allocation")


def context(source, ta, tb, ba, bb, name):
    return {"t": source["t"], "TA": ta, "TB": tb, "bA": ba, "bB": bb, "allocation": name}


def fringe_readout(ctx, parameter, c, basis, derivative):
    t, a, b, ba, bb = (ctx[k] for k in ("t", "TA", "TB", "bA", "bB"))
    parameter, c = I.of(parameter), I.of(c)
    ua, ub, dua, dub = allocation(c, ctx["allocation"])
    z = (1 - t).square()
    sa, sb, zeta = 1 - ba, 1 - bb, (1 - ba) * (1 - bb)
    if basis == "HV":
        h2 = parameter * (1 - parameter)
        da = 1 - a + a.square() * (1 - ua) * h2
        db = 1 - b
        trace = t * (2 - a - b + a * b * parameter)
        if derivative == "parameter":
            da_d = a.square() * (1 - ua) * (1 - 2 * parameter)
            db_d, trace_d = I(0), t * a * b
        else:
            da_d = -a.square() * dua * h2
            db_d, trace_d = I(0), I(0)
    else:
        require(basis == "DA", "unknown_fringe_basis")
        h2 = parameter.square() / 4
        da = 1 - a + a.square() * (1 - ua) * h2
        db = 1 - b + b.square() * (1 - ub) / 4
        trace = t * (2 - a - b + a * b / 2 + a * b * c * parameter / 2)
        if derivative == "parameter":
            da_d = a.square() * (1 - ua) * parameter / 2
            db_d, trace_d = I(0), t * a * b * c / 2
        else:
            da_d = -a.square() * dua * h2
            db_d = -b.square() * dub / 4
            trace_d = t * a * b * parameter / 2
    qa = 1 - t * (2 - a) + t.square() * da
    qb = 1 - t * (2 - b) + t.square() * db
    qab = 1 - trace + t.square() * da * db
    require(min(qa.lo, qb.lo, qab.lo) > 0, "fringe_denominator_not_positive")
    qa_d, qb_d = t.square() * da_d, t.square() * db_d
    qab_d = -trace_d + t.square() * (da_d * db + da * db_d)
    joint = 1 - sa * z / qa - sb * z / qb + zeta * z / qab
    joint_d = sa * z * qa_d / qa.square() + sb * z * qb_d / qb.square() - zeta * z * qab_d / qab.square()
    return joint, joint_d


def visibility(ctx, c):
    jp, dp = fringe_readout(ctx, I(1), c, "DA", "coherence")
    jm, dm = fringe_readout(ctx, I(-1), c, "DA", "coherence")
    den = jp + jm
    require(den.lo > 0, "raw_visibility_denominator_not_positive")
    value = (jp - jm) / den
    slope = ((dp - dm) * den - (jp - jm) * (dp + dm)) / den.square()
    return value, slope


def low_coherence_bound(ctx):
    t, a, b, ba, bb = (ctx[k] for k in ("t", "TA", "TB", "bA", "bB"))
    z, zeta = (1 - t).square(), (1 - ba) * (1 - bb)
    one_joint_scale = zeta * z * t * a * b / 2
    base = ba * bb + (1 - ba) * bb * z * t * a + (1 - bb) * ba * z * t * b + one_joint_scale
    tail = t.square() * (3 - 2 * t)
    raw_tail = (1 - ba * bb) * tail
    upper = (2 * one_joint_scale * F(9, 10) + raw_tail) / (2 * base + raw_tail)
    return upper, {"domain": ["0", ".9"], "zero_pair_mass": z.packet(),
        "one_pair_mass": (2 * z * t).packet(), "one_pair_joint_linear_scale": one_joint_scale.packet(),
        "raw_constant_term": base.packet(), "full_n_ge_2_mass": tail.packet(),
        "raw_higher_sector_budget": raw_tail.packet(), "full_fringe_visibility_upper_bound": upper.packet(),
        "method": "complete_n0_n1_Born_plus_positive_full_numberMass_tail_and_OR_background"}


def certify_fringe(ctx, target):
    hv_joint, hv_slope = fringe_readout(ctx, I(0, 1), I(0, 1), "HV", "parameter")
    da_joint, da_slope = fringe_readout(ctx, I(-1, 1), I(F(9, 10), 1), "DA", "parameter")
    _, c_slope = visibility(ctx, I(F(9, 10), 1))
    lower_upper, low_receipt = low_coherence_bound(ctx)
    details = {"HV_whole_z_derivative": hv_slope.packet(), "DA_whole_y_derivative": da_slope.packet(),
               "visibility_whole_c_derivative": c_slope.packet(), "low_coherence_bound": low_receipt}
    for condition, reason in ((hv_slope.lo > 0, "UNRESOLVED_HV_FULL_FRINGE_DERIVATIVE"),
            (da_slope.lo > 0, "UNRESOLVED_DA_FULL_FRINGE_DERIVATIVE"),
            (c_slope.lo > 0, "UNRESOLVED_VISIBILITY_COHERENCE_DERIVATIVE"),
            (lower_upper.hi < F(".995"), "UNRESOLVED_LOW_COHERENCE_EXCLUSION")):
        if not condition:
            raise MathUnresolved(reason, details)
    try:
        c, root = monotone_root(lambda x: visibility(ctx, x)[0], target, F(9, 10), 1, ROOT_WIDTH)
    except ValueError as error:
        details.update(endpoint_values={".9": visibility(ctx, I(F(9, 10)))[0].packet(),
                                        "1": visibility(ctx, I(1))[0].packet()}, target=str(target))
        raise MathUnresolved(str(error), details) from error
    da, _ = visibility(ctx, c)
    hv_max, _ = fringe_readout(ctx, I(1), c, "HV", "parameter")
    hv_min, _ = fringe_readout(ctx, I(0), c, "HV", "parameter")
    hv = (hv_max - hv_min) / (hv_max + hv_min)
    details.update(c_root=c.packet(), c_root_certificate=root, HV_visibility=hv.packet(), DA_visibility=da.packet())
    if not F(".998") <= hv.lo and hv.hi <= 1:
        raise MathUnresolved("HV_FULL_FRINGE_OUTSIDE_PUBLIC_DOMAIN", details)
    if not (da.width <= TOL and close_to(da, target)):
        raise MathUnresolved("DA_FULL_FRINGE_READBACK_UNRESOLVED", details)
    return c, {"HV": {"parameter": "z=cos_squared_Alice", "whole_domain": ["0", "1"],
            "coherence_domain": ["0", "1"], "derivative_enclosure": hv_slope.packet(),
            "strict_monotonicity_certified": True, "raw_visibility": hv.packet(),
            "global_minimum": hv_min.packet(), "global_maximum": hv_max.packet()},
        "DA": {"parameter": "y=sin_twice_Alice", "whole_domain": ["-1", "1"],
            "coherence_domain": [".9", "1"], "derivative_enclosure": da_slope.packet(),
            "strict_monotonicity_certified": True, "raw_visibility": da.packet(),
            "coherence_derivative_enclosure": c_slope.packet(), "coherence_inverse_strictly_monotone": True,
            "coherence_root": c.packet(), "coherence_root_certificate": root,
            "low_domain_exclusion": low_receipt},
        "extrema_obtained_only_after_whole_domain_derivative_certificate": True,
        "source_rows_and_same_pair_D_define_fringe": True, "old_six_root_cap_used": False}


def native_rows(eta, xi, norm, sine, cosine):
    root = eta.sqrt()
    complement, loss = (1 - norm).sqrt(), (1 - eta).sqrt()
    return ((C(root * sine), C(root * xi * cosine)), (C(0), C(root * complement * cosine)),
            (C(root * cosine), C(-root * xi * sine)), (C(0), C(-root * complement * sine)),
            (C(loss), C(0)), (C(0), C(loss)))


def native_forward(th, tv, ta, tb, c, name, a, b, ba, bb):
    ua, ub, _, _ = allocation(c, name)
    xia, xib = environment_xi(c, name)
    sa, ca = arithmetic.trig_sin_cos(F(a))
    sb, cb = arithmetic.trig_sin_cos(F(b))
    ra, rb = native_rows(ta, xia, ua, sa, ca), native_rows(tb, xib, ub, sb, cb)
    xa, xb = arithmetic.gram(ra[2:]), arithmetic.gram(rb[2:])
    d = ((C(th.sqrt()), C(0)), (C(0), C(tv.sqrt())))
    z = (1 - th) * (1 - tv)
    pulse, _ = arithmetic.gaussian_no_click(d, z, xa, xb)
    pulse = {"A": (1 - ba) * pulse["A"], "B": (1 - bb) * pulse["B"],
             "AB": (1 - ba) * (1 - bb) * pulse["AB"]}
    outcomes = arithmetic.window(pulse, 1)
    return pulse, outcomes


def native_fringe_checks(ctx, c):
    result = []
    for basis, a, b, parameter in (("HV", 0, 0, 1), ("HV", 90, 0, 0),
                                    ("HV", 45, 0, F(1, 2)), ("DA", 45, 45, 1),
                                    ("DA", -45, 45, -1), ("DA", 0, 45, 0)):
        _, outcomes = native_forward(ctx["t"], ctx["t"], ctx["TA"], ctx["TB"], c,
                                     ctx["allocation"], a, b, ctx["bA"], ctx["bB"])
        compact, _ = fringe_readout(ctx, I(parameter), c, basis, "parameter")
        residual = outcomes["++"] - compact
        require(residual.contains(0) and residual.width <= TOL, "native_rows_compact_fringe_disagree")
        result.append({"basis": basis, "Alice_degrees": str(a), "Bob_degrees": str(b),
                       "native_joint": outcomes["++"].packet(), "compact_joint": compact.packet(),
                       "residual": residual.packet()})
    return result


def point_inventory(config):
    axes = []
    for key in config["four_box_axes_order"]:
        row = config[key]
        if "half_width" in row:
            center, half = rational(row["center"]), rational(row["half_width"])
            axes.append((center - half, center + half))
        else:
            axes.append((rational(row["box_low"]), rational(row["box_high"])))
    center = tuple(rational(config[key]["center"]) for key in config["four_box_axes_order"])
    points = [("center", center, config["default_allocation"], True)]
    points.extend(("corner_%02d" % i, tuple(v), config["default_allocation"], True)
                  for i, v in enumerate(itertools.product(*axes)))
    points.extend(("center_override_" + name, center, name, False)
                  for name in config["center_allocation_overrides"])
    require(len(points) == config["total_source_points_with_overrides"] == 19 and
            sum(x[3] for x in points) == config["default_point_count"] == 17, "nominal_source_point_inventory_changed")
    return points


def produce_point(identifier, values, name, default, config):
    ka, kb, q, target = values
    ba, bb = map(rational, config["background_per_pulse"])
    receipt = {"id": identifier, "input": {"K_A": str(ka), "K_B": str(kb),
        "pair_probability": str(q), "DA_raw_visibility": str(target), "allocation": name},
        "included_in_default_source_box": default, "branches": []}
    try:
        generated = source_from_q(q)
        receipt["gain_source"] = generated["receipt"]
        candidates, root_receipt = loss_roots(generated["n_grid"], ka, kb, ba, bb)
        receipt["K_cubic_all_roots"] = root_receipt
        for ta, tb, candidate in candidates:
            branch = dict(candidate)
            receipt["branches"].append(branch)
            if ta is None:
                continue
            try:
                true_k = raw_matched(generated["n"], ta, tb, ba, bb)
                branch["true_source_calibration_K"] = {k: v.packet() for k, v in true_k.items()}
                require(close_to(true_k["K_A"], ka) and close_to(true_k["K_B"], kb),
                        "TRUE_SOURCE_K_READBACK_UNRESOLVED")
                ctx = context(generated, ta, tb, ba, bb, name)
                c, fringe = certify_fringe(ctx, target)
                branch["full_fringe_certificate"] = fringe
                branch["native_rows_fringe_checks"] = native_fringe_checks(ctx, c)
                ua, ub, _, _ = allocation(c, name)
                xia, xib = environment_xi(c, name)
                branch["source"] = {"G": generated["G"].packet(), "G_grid": str(generated["G_grid"]),
                    "n_balanced": generated["n"].packet(), "n_grid": str(generated["n_grid"]),
                    "t_balanced": generated["t"].packet(), "TA": ta.packet(), "TB": tb.packet(),
                    "c": c.packet(), "c_descriptor": "unique_raw_DA_visibility_root_with_fixed_source_and_allocation",
                    "xi_A": xia.packet(), "xi_B": xib.packet(), "u_A": ua.packet(), "u_B": ub.packet(),
                    "source_phase": ["1", "0"], "allocation": name,
                    "root_midpoints_used_as_source": False, "complete_Gram_supplied_by_caller": False}
                branch["true_source_calibration_K"] = {k: v.packet() for k, v in true_k.items()}
                branch["reference_source_forward"] = []
                reference = generated["reference"]
                for a, b in ((0, 0), (45, 45)):
                    pulse, outcomes = native_forward(reference["tH"], reference["tV"], ta, tb, c,
                        name, a, b, ba, bb)
                    branch["reference_source_forward"].append({"reference_beta_degrees": "16",
                        "readout_angles_from_calibration_roles": [str(a), str(b)],
                        "pulse_no_click": {k: v.packet() for k, v in pulse.items()},
                        "complete_N1_outcomes": {k: v.packet() for k, v in outcomes.items()},
                        "published_optimization_angles_read": False})
                branch["status"] = "source_generated_with_complete_raw_fringe_certificates"
            except ValueError as error:
                branch["status"], branch["reason"] = "UNRESOLVED", str(error)
                if isinstance(error, MathUnresolved):
                    branch["unresolved_mathematical_certificate"] = error.details
        legal = root_receipt["legal_root_count"]
        completed = sum(b["status"] == "source_generated_with_complete_raw_fringe_certificates" for b in receipt["branches"])
        unresolved = any(b["status"] == "UNRESOLVED" for b in receipt["branches"])
        receipt["status"] = ("UNRESOLVED" if unresolved else "MODEL_INPUT_REJECTED" if not legal else
                              "source_generated" if completed == legal else "UNRESOLVED")
    except ValueError as error:
        receipt["status"], receipt["reason"] = "UNRESOLVED", str(error)
    return receipt


def run():
    start = time.monotonic()
    config, bindings, mapping, freeze = inputs()
    points = [produce_point(*point, config) for point in point_inventory(config)]
    all_generated = all(p["status"] == "source_generated" for p in points)
    return {"schema": SCHEMA, "version": VERSION,
        "status": "source_generated" if all_generated else "source_partial_or_unresolved",
        "freeze": freeze, "source_bindings": bindings, "efficiency_unit_mapping": mapping,
        "precision_digits": 40, "source_grid_digits": 15, "source_grid_tie_rule": "toward_positive_infinity",
        "hyperbolic_positive_series_terms": 20, "pi_interval": [str(x) for x in arithmetic.PI],
        "readout_tolerance": str(TOL), "points": points, "point_count": len(points),
        "default_point_count": sum(p["included_in_default_source_box"] for p in points),
        "all_nineteen_source_points_generated": all_generated,
        "all_branches_and_unresolved_points_retained": True,
        "calibration_measurement_pulses": 1, "background_model": "independent_local_per_pulse_OR",
        "nominal_role": config["nominal_role"],
        "independence": {"foreign_new_calibration_program_read": False,
            "foreign_new_calibration_output_read": False, "first_receipt_protected": True},
        **{key: False for key in FALSE_FLAGS}, "publication_configuration_identified": False,
        "event_files_read": 0, "retrospective": True, "runtime_seconds": time.monotonic() - start}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "calibration-primary.json")
    args = parser.parse_args()
    require(not args.output.exists(), "protected_existing_calibration_first_receipt")
    report = run()
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": report["status"], "points": len(report["points"]),
        "all_generated": report["all_nineteen_source_points_generated"], "output": str(args.output),
        "sha256": arithmetic.digest(args.output)}))


if __name__ == "__main__":
    main()
