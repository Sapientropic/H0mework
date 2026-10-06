#!/usr/bin/env python3
"""Cross the sealed six-port and occupation-Born receipts on identical sources."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
FIRST = {
    "counts-primary.json": ("23b911509e", "4c8983b9cb1205f99cf3b80f5f77882168a0ea9f2be22dbf1a5cb62426225efb"),
    "counts-independent.json": ("5983458a99", "71ea8101d667b82c8bbdc6d2997a2e878929f1c53682cf1d2f2db411d736dc3f"),
}


def require(value, reason):
    if not value:
        raise ValueError(reason)


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


def interval(packet):
    a, b = F(packet["exact_lower"]), F(packet["exact_upper"])
    require(a <= b, "reversed_receipt_interval")
    return a, b


def gap(a, b):
    a0, a1 = interval(a)
    b0, b1 = interval(b)
    return max(F(0), a0 - b1, b0 - a1)


def matrix_gap(a, b):
    require(len(a) == len(b) and all(len(x) == len(y) for x, y in zip(a, b)),
            "different_native_matrix_dimensions")
    return max((gap(x[p], y[q]) for ar, br in zip(a, b) for x, y in zip(ar, br)
                for p, q in (("real", "re"), ("imaginary", "im"))), default=F(0))


def load_first(directory, name, primary):
    path = directory / name
    commit, digest = FIRST[name]
    require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
            "different_sealed_first_receipt:" + name)
    if directory == HERE:
        primary.frozen(path, commit)
    return json.loads(path.read_text())


def independent_q_effect(ind, raw, q):
    site = ind.environment_effect(raw["TA"], raw["xiA"], 0)
    roots = [ind.I(F(x)).sqrt() for x in raw["TA"]]
    columns = [[row[p] * roots[p] for p in range(2)] for row in site["embedding"]]
    if q is None:
        v = [ind.I(1), ind.I(0)]
    else:
        norm = ind.I(1 + q * q).sqrt()
        v = [ind.I(q) / norm, 1 / norm]
    projection = [[ind.C(v[p] * v[r] if e == f else 0)
                   for r in range(2) for f in range(2)]
                  for p in range(2) for e in range(2)]
    clicked = ind.mm(ind.adjoint(columns), ind.mm(projection, columns))
    return ind.matrix_subtract(ind.identity(2), clicked)


def independent_q_joint(ind, raw, q):
    xa = independent_q_effect(ind, raw, q)
    xb = ind.environment_effect(raw["TB"], raw["xiB"], raw["angles"][1])["no_click"]
    totals = [ind.C(), ind.C(), ind.C()]
    for n in range(7):
        row = ind.sector_readout(raw, n, ind.occupation_polynomial(xa, n),
                                ind.occupation_polynomial(xb, n))
        for j, key in enumerate(("no_click_A", "no_click_B", "no_click_AB")):
            totals[j] += row[key]
    _, _, tail = ind.mass(raw, 6)
    full = [ind.real_enclosure(x, "cross_q_Born") + ind.I(0, tail) for x in totals]
    return ind.outcomes_from_no_click(full)["++"].packet()


def verify(directory=HERE, enabled=True):
    require(enabled, "environment_count_verification_disabled")
    primary = module("p23_env_count_cross_primary", "counts.py")
    ind = module("p23_env_count_cross_independent", "independent_counts.py")
    freeze = primary.frozen(Path(__file__))
    config, _, _ = primary.inputs()
    oldp = load_first(directory, "counts-primary.json", primary)
    oldi = load_first(directory, "counts-independent.json", primary)
    require(oldp["version"] == oldi["version"] == config["version"], "look_alike_version")
    require(all(oldp[k] is False and oldi[k] is False for k in primary.FALSE_FLAGS),
            "count_authority_scope_changed")
    require(oldp["independence"] == {"foreign_new_science_program_read": False,
            "foreign_new_science_output_read": False, "comparison_performed": False,
            "first_receipt_protected": True}, "primary_first_not_blind")
    require(oldi["outcome"] == "FINITE_BORN_AND_ENVIRONMENT_CONTROLS_VERIFIED" and
            all(oldi["controls"]["checks"].values()), "independent_controls_failed")
    freshp, freshi = primary.run(), ind.compute(progress=False)
    require(oldi == freshi, "independent_first_not_reproduced")
    for key in ("fixtures", "controls", "fringe_polynomials", "source_bindings", "freeze"):
        require(oldp[key] == freshp[key], "primary_first_not_reproduced:" + key)
    ids = [x["id"] for x in config["fixtures"]]
    require(oldp["fixture_order"] == ids and [x["fixture_id"] for x in oldi["rows"]] == ids,
            "fixture_inventory_or_order_changed")
    rows = []
    for raw, foreign in zip(config["fixtures"], oldi["rows"]):
        name = raw["id"]
        native = oldp["fixtures"][name]
        require(native["input"] == foreign["source_parameters"] == raw, "source_coordinates_changed")
        ports = max(matrix_gap(native["station_ports"][arm][kind], foreign[key][j])
                    for j, arm in enumerate(("A", "B"))
                    for kind, key in (("clicked_Gram", "click_effect"), ("no_click_Gram", "no_click_effect")))
        pulses = max(gap(native["pulse_no_click"][key], foreign["full_no_click"][j])
                     for j, key in enumerate(("A", "B", "AB")))
        outcomes = max(gap(native["windows"][str(win["pulses"])][key], win["observed"]["outcomes"][key])
                       for win in foreign["windows"] for key in ("++", "+0", "0+", "00"))
        tail = native["source"]["numberMass_tail"]
        require(interval(tail) == (F(foreign["tail"]), F(foreign["tail"])), "different_original_mass_tail")
        require(F(foreign["mass"]) + F(foreign["tail"]) == 1 and
                foreign["prefix_renormalized"] is False and foreign["total_pair_prefix"] == 6,
                "mass_prefix_identity_changed")
        fringe = oldp["fringe_polynomials"][name]
        qgaps = []
        for q in (F(0), F(1), F(-1), F(1, 3), None):
            if q is None:
                polynomial = fringe["q_infinity_joint"]
            else:
                numerator = [primary.C(primary.I(*interval(x))) for x in fringe["joint_numerator"]]
                denominator = [primary.C(primary.I(*interval(x))) for x in fringe["joint_denominator"]]
                polynomial = (primary.real_part(primary.peval(numerator, q), "cross_q_numerator") /
                              primary.real_part(primary.peval(denominator, q), "cross_q_denominator")).packet()
            qgaps.append(gap(polynomial, independent_q_joint(ind, raw, q)))
        degrees = fringe["degrees"]
        require(degrees["QA"] <= 4 and degrees["QAB"] <= 4 and
                degrees["joint_numerator"] <= 8 and degrees["joint_denominator"] <= 8 and
                degrees["derivative_numerator"] <= 14 and fringe["degree_15_cancelled_algebraically"] is True and
                fringe["full_fringe_extrema_certified"] is False, "fringe_degree_or_scope_changed")
        distance = max(ports, pulses, outcomes, *qgaps)
        require(distance == 0, "independent_native_Fock_or_fringe_enclosures_disjoint:" + name)
        rows.append({"fixture": name, "matrix_outer_distance": str(ports),
                     "pulse_outer_distance": str(pulses), "window_outcome_outer_distance": str(outcomes),
                     "five_q_Fock_outer_distances": [str(x) for x in qgaps],
                     "original_pair_mass_tail": foreign["tail"], "fringe_degrees": degrees})
    return {"schema": "p23-environment-count-verification/v1", "version": config["version"],
            "status": "NATIVE_EFFECT_FOCK_AND_GENERAL_FRINGE_CROSS_VERIFIED", "program_freeze": freeze,
            "first_receipts": {name: {"commit": value[0], "sha256": value[1]} for name, value in FIRST.items()},
            "primary_first_reproduced": True, "independent_first_reproduced": True,
            "science_first_receipts_completed_before_cross": True, "fixture_rows": rows,
            "foreign_source_or_probability_used_as_forward_input": False,
            "foreign_fringe_coefficients_used_only_for_comparison": True,
            "all_21_independent_controls_verified": True, "primary_focused_tests": 12,
            **{key: False for key in primary.FALSE_FLAGS}, "actual_source_or_hardware_identity_verified": False,
            "retrospective": True, "event_files_read": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-root", type=Path, default=HERE, help="JSON receipts only; programs stay in this repository")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), "verification_output_already_exists")
    result = verify(args.input_root.resolve())
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(result["status"])


if __name__ == "__main__":
    main()
