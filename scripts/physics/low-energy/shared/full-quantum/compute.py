#!/usr/bin/env python3
"""Exact full-carrier temporal generator of the original Dirac-dual action.

This retains independent complex dual coordinates.  The positive current
Hermitian part is never substituted for the primal temporal generator.
"""
from __future__ import annotations

import json
import itertools
from pathlib import Path
import sys

import sympy as s

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE / "matter-modes"))
from compute import decode, encode, clean, zero, source, source_matrices  # noqa: E402


def main():
    root = HERE.parents[3]
    source_matrices(root)
    _, _, _, hashes = source.parse_source(root)
    phase = json.loads((BASE / "full-phase/receipt.json").read_text())
    modes = json.loads((BASE / "matter-modes/source.json").read_text())
    vertices = json.loads((BASE / "matter-vertices/receipt.json").read_text())
    assert phase["source_sha256"] == modes["source_sha256"] == vertices["source_sha256"] == hashes
    lapse = s.sympify(phase["source_lapse"])
    spin = s.sqrt(2)
    principal = [decode(x) for x in phase["principal_coefficients"]]
    gamma0 = clean(lapse * principal[0] / s.I)
    inv_time = clean(s.I * lapse * gamma0)
    zero(inv_time * principal[0] - s.eye(252))
    zero(principal[0] * inv_time - s.eye(252))
    B, Y = [decode(phase[key]) for key in ["original_constant_B", "original_Y"]]
    hfree = clean(lapse * gamma0 * B)
    ny = clean(lapse * gamma0 * Y)
    hfull = hfree + ny
    zero(hfree.H - hfree)
    zero(ny * ny)
    assert ny.todok()
    zero(principal[0] * (-s.I * hfull) + B + Y)
    # Canonical momentum is p=chi*C0; it is an independent row, not psi†.
    dual_generator = clean((B + Y) * inv_time)
    zero(dual_generator * principal[0] - principal[0] * s.I * hfull)
    # This is the conserved original bilinear concomitant in doubled variables.
    zero(dual_generator * principal[0] + principal[0] * (-s.I * hfull))
    zero(hfree * ny + ny * hfree)
    charge = decode(phase["phase_generator"])
    zero(hfull * charge - charge * hfull)
    gamma5 = s.kronecker_product(s.diag(-1, -1, 1, 1), s.eye(63))
    kinetic = spin * gamma5
    graph_defect = clean(hfull.H * kinetic - kinetic * hfull)
    assert graph_defect.todok()
    basis2 = list(itertools.combinations(range(7), 2))
    prepared = s.zeros(252, 1)
    for spin_index, pair, coefficient in [(0, (1, 5), 1), (1, (0, 5), -1),
                                          (2, (1, 5), 1), (3, (0, 5), -1)]:
        prepared[63 * spin_index + 7 + basis2.index(pair)] = coefficient
    frequency = s.sympify(phase["source_frequency"])
    zero(hfull * prepared - frequency * charge * prepared)
    zero(graph_defect * prepared)
    noether = kinetic * charge
    noether_signature = {"positive": sum(bool(value > 0) for value in noether.diagonal()),
                         "negative": sum(bool(value < 0) for value in noether.diagonal())}
    coordinate = list(sorted(ny.todok().items()))[0]
    (out_row, in_column), coefficient = coordinate
    e = s.eye(252)[:, in_column]
    witness = clean(ny * e)
    norm2 = s.simplify((witness.H * witness)[0])
    assert norm2 > 0
    # Any fixed positive Gram would give ||Ny e||_G²=<e,Ny²e>_G=0
    # if Ny were G-self-adjoint; Lean carries this universal argument.
    free_projection = decode(modes["free_projection"])
    vertex_summary = {}
    scalar_times = []
    p = s.symbols("p0:4", real=True)
    for vertex in vertices["primitive_vertices"]:
        operator = decode(vertex["operator"], **{str(x): x for x in p})
        group = vertex["group"]
        entry = vertex_summary.setdefault(group, {"count": 0, "free_leakage": 0})
        entry["count"] += 1
        temporal = clean(lapse * gamma0 * operator)
        leakage = clean((s.eye(252) - free_projection) * temporal * free_projection)
        entry["free_leakage"] += bool(leakage.todok())
        if group == "scalar":
            zero(temporal * temporal)
            scalar_times.append(temporal)
    # The registered vertex group names, rather than guessed labels, drive scope.
    spatial = [clean(-lapse * gamma0 * principal[j + 1] / s.I) for j in range(3)]
    assert len(scalar_times) == 70
    for left in scalar_times:
        for right in scalar_times:
            zero(left * right)
    # Exact exceptional momentum: test the spin/color singlet crossing in original units.
    k = 3 * spin / 2
    hcross = clean(hfull + k * spatial[2])
    hcrossfree = clean(hfree + k * spatial[2])
    crossing_witness = None
    for col in range(252):
        basis = s.eye(252)[:, col]
        if not clean(hcrossfree * basis).todok():
            image = clean(hcross * basis)
            if image.todok() and not clean(hcross * image).todok():
                crossing_witness = {"momentum": ["0", "0", str(k)],
                    "input_basis": col, "image": encode(image),
                    "image_norm_squared": str(s.simplify((image.H * image)[0]))}
                break
    result = {
        "scope": "FULL_252_ORIGINAL_PRIMAL_AND_INDEPENDENT_DUAL_TEMPORAL_GENERATOR",
        "source_sha256": phase["source_sha256"],
        "time_principal_inverse": encode(inv_time),
        "original_H_free": encode(hfree),
        "original_H_yukawa": encode(ny),
        "original_H_full": encode(hfull),
        "original_dual_time_generator": encode(dual_generator),
        "original_primal_equation": "C0*(-i H)+B+Y=0",
        "original_dual_equation": "chi'=chi*(B+Y)*C0^-1",
        "conserved_pairing": "chi*C0*psi, with independent chi",
        "yukawa_nonzero_square_zero": True,
        "yukawa_nonzero_witness": {"input_basis": in_column, "output_basis": out_row,
             "coefficient": str(coefficient), "image_norm_squared": str(norm2)},
        "source_free_H_hermitian": True,
        "source_free_H_anticommutes_yukawa": True,
        "full_H_commutes_source_charge": True,
        "actual_prepared_phase_derivative_matches_original": True,
        "canonical_initial_graph_defect": encode(graph_defect),
        "canonical_initial_graph_defect_zero_on_actual_prepared": True,
        "full_Noether_pairing_signature": noether_signature,
        "all_158_vertices_free_leakage": vertex_summary,
        "actual_fixed_scalar_exceptional_momentum": crossing_witness,
        "positive_time_pairing_identified_with_action": False,
    }
    (HERE / "receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ["scope", "yukawa_nonzero_witness",
        "all_158_vertices_free_leakage", "actual_fixed_scalar_exceptional_momentum"]}, indent=2))


if __name__ == "__main__":
    main()
