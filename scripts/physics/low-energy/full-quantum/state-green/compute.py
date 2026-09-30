#!/usr/bin/env python3
"""Independent sparse-Fock evaluation of both original full-source two-time words."""
from __future__ import annotations

from functools import lru_cache
import importlib.util
import itertools
import json
from pathlib import Path
import time

import sympy as s

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SPEC = importlib.util.spec_from_file_location("source_time", HERE.parent / "triangular/compute.py")
source = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(source)
decode, clean, zero = source.decode, source.clean, source.zero


@lru_cache(None)
def canonical(value):
    return s.radsimp(s.simplify(value))


def add(result, key, value):
    result[key] = result.get(key, 0)+value


def create_field(column, state):
    result = {}
    for occupied, amplitude in state.items():
        for label, weight in column:
            if label not in occupied:
                sign = (-1)**sum(other<label for other in occupied)
                add(result, tuple(sorted((*occupied, label))), sign*weight*amplitude)
    return result


def annihilate_field(row, state):
    result = {}
    for occupied, amplitude in state.items():
        for label, weight in row:
            if label in occupied:
                rest = tuple(other for other in occupied if other != label)
                sign = (-1)**sum(other<label for other in rest)
                add(result, rest, sign*weight*amplitude)
    return result


def pairing(prepared, state):
    return sum(s.conjugate(amplitude)*state.get(occupied, 0)
               for occupied, amplitude in prepared.items())


def main():
    started = time.monotonic()
    source.source.source_matrices(ROOT)
    _, _, _, hashes = source.source.source.parse_source(ROOT)
    parent = json.loads((HERE.parent / "receipt.json").read_text())
    phase = json.loads((HERE.parents[1] / "full-phase/receipt.json").read_text())
    triangle = json.loads((HERE.parent / "triangular/receipt.json").read_text())
    assert parent["source_sha256"] == phase["source_sha256"] == triangle["source_sha256"] == hashes
    case = next(case for case in triangle["cases"] if case["momentum"] == ["0", "0", "0"])
    assert all(term["time_power"] == 0 for term in case["time"]["coefficients"])
    rates = [s.sympify(term["rate"]) for term in case["time"]["coefficients"]]
    scale = min(abs(rate) for rate in rates)
    t, u = s.pi/scale, s.pi/(2*scale)
    coefficients = [(s.sympify(term["rate"]), decode(term["matrix"])) for term in case["time"]["coefficients"]]

    def evolution(time):
        result = s.zeros(252)
        for rate, matrix in coefficients:
            weight = s.expand_complex(s.exp(-s.I*s.simplify(rate*time)))
            result += weight*matrix
        return s.SparseMatrix(result).applyfunc(canonical)

    Ut, UminusS, Us = evolution(t), evolution(-u), evolution(u)
    zero(clean(Us*UminusS-s.eye(252)).applyfunc(canonical))
    zero(clean(UminusS*Us-s.eye(252)).applyfunc(canonical))
    adjoint_defect = clean(UminusS-Us.H).applyfunc(canonical)
    assert adjoint_defect.todok()
    w = s.zeros(252, 1)
    basis2 = list(itertools.combinations(range(7), 2))
    for spin, pair, coefficient in [(0, (1,5), 1), (1, (0,5), -1), (2, (1,5), 1), (3, (0,5), -1)]:
        w[63*spin+7+basis2.index(pair)] = s.Rational(coefficient, 2)
    assert (w.H*w)[0] == 1
    prepared = {(i,):value for i, value in enumerate(w) if value}
    P = s.SparseMatrix(w*w.H)
    zero(P*P-P)
    H = decode(parent["original_H_full"])
    nonstationary = clean(H*P-P*H)
    assert nonstationary.todok()
    rows = {i:[] for i in range(252)}
    columns = {j:[] for j in range(252)}
    for (i, a), weight in Ut.todok().items(): rows[i].append((a, weight))
    for (b, j), weight in UminusS.todok().items(): columns[j].append((b, weight))
    # Full Fock words act before reading the source one-particle bra.
    created = {j:create_field(columns[j], prepared) for j in range(252)}
    annihilated = {i:annihilate_field(rows[i], prepared) for i in range(252)}
    greater, lesser = {}, {}
    for i in range(252):
        for j in range(252):
            first = canonical(pairing(prepared, annihilate_field(rows[i], created[j])))
            second = canonical(pairing(prepared, create_field(columns[j], annihilated[i])))
            if first: greater[i, j] = first
            if second: lesser[i, j] = second
    greater = s.SparseMatrix(252, 252, greater)
    lesser = s.SparseMatrix(252, 252, lesser)
    zero(clean(greater-Ut*(s.eye(252)-P)*UminusS).applyfunc(canonical))
    zero(clean(lesser-Ut*P*UminusS).applyfunc(canonical))
    zero(clean(greater+lesser-Ut*UminusS).applyfunc(canonical))
    # The same time difference cannot erase this original prepared occupation.
    shifted = clean(evolution(t+u)*(s.eye(252)-P)*evolution(-2*u)).applyfunc(canonical)
    shift_defect = clean(shifted-greater).applyfunc(canonical)
    assert shift_defect.todok()
    lapse = s.sympify(phase["source_lapse"])
    C0 = decode(phase["principal_coefficients"][0])
    gamma0 = clean(lapse*C0/s.I)
    C0inverse = clean(s.I*lapse*gamma0)
    right_limit = clean(Us*(s.eye(252)-P)*UminusS*C0inverse)
    left_limit = clean(-Us*P*UminusS*C0inverse)
    zero(clean(C0*(right_limit-left_limit)-s.eye(252)).applyfunc(canonical))
    density = s.I/lapse
    chi_greater = clean(density*greater*C0inverse)
    zero(clean((-s.I*lapse)*chi_greater-greater*C0inverse).applyfunc(canonical))
    receipt = {
        "scope": "ORIGINAL_PREPARED_FULL_CAR_TWO_TIME_GREEN",
        "source_sha256": hashes,
        "momentum": ["0", "0", "0"],
        "t": str(t), "s": str(u),
        "prepared": "actual.matter(0)/2, four original coefficients, norm one",
        "CAR_words_evaluated_before_read": True,
        "mode_pairs_checked": 252**2,
        "greater_nnz": len(greater.todok()), "lesser_nnz": len(lesser.todok()),
        "greater_equals_U_I_minus_P_Uinverse": True,
        "lesser_equals_U_P_Uinverse": True,
        "canonical_inverse_not_adjoint_defect_nnz": len(adjoint_defect.todok()),
        "actual_H_P_commutator_nnz": len(nonstationary.todok()),
        "same_time_difference_shift_defect_nnz": len(shift_defect.todok()),
        "Dirac_principal_jump_identity": True,
        "independent_dual_weight": "(i/Vol)*S*C0^-1",
        "original_density_normalization": "(-i Vol)*chiGreen=S*C0^-1",
        "elapsed_seconds": round(time.monotonic()-started, 3),
    }
    (HERE/"receipt.json").write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({key: receipt[key] for key in ["scope", "mode_pairs_checked", "greater_nnz", "lesser_nnz",
        "canonical_inverse_not_adjoint_defect_nnz", "actual_H_P_commutator_nnz",
        "same_time_difference_shift_defect_nnz", "elapsed_seconds"]}, indent=2))


if __name__ == "__main__":
    main()
