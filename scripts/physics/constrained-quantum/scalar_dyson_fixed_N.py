#!/usr/bin/env python3
"""All-61 source insertion and fixed-N CAR Dyson termination.

The canonical scalar ports are the actual ``W_a=-i E^{-1}V_a`` matrices from
the source action.  Every one has image in the original degree-6 carrier and
annihilates that carrier on the next insertion.  The source free drift
preserves the degree-6 carrier at every real momentum, so a one-line
interaction-picture word with two scalar insertions is exactly zero, including
arbitrary separated times.

On the N-particle exterior CAR sector, a product of m second-quantized
insertions expands by assigning each insertion to one of N particle lines.
Repeated assignments contain the one-line zero; only injective assignments
survive.  There are no injective assignments for m=N+1.  This proves the
finite-N Dyson truncation algebraically while retaining nonzero normal
products on distinct lines.  Bosonic scalar coefficients may remain
noncommuting in time ordering because they are scalar coefficients relative to
the even CAR line operators; no Hilbert completion or continuum spectral
claim is made.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import math
from pathlib import Path
import time

import sympy as s

from full_matter_ports import MatterPorts, K, clean, equal
from dynamic import BASE, HERE, ROOT, ROOT_ID, decode


def frame_for_degree(degree):
    inside = [(d, word) for d in (6, 2, 4) for word in itertools.combinations(range(7), d)]
    indices = [spin * 63 + i for spin in range(4)
               for i, (d, _) in enumerate(inside) if d == degree]
    return s.SparseMatrix(252, len(indices), {(i, j): 1 for j, i in enumerate(indices)})


def zeros(rows, columns):
    return s.SparseMatrix.zeros(rows, columns)


def annihilate_basis(mode, state):
    if mode not in state:
        return None, s.Integer(0)
    sign = (-1) ** sum(index < mode for index in state)
    return tuple(index for index in state if index != mode), s.Integer(sign)


def create_basis(mode, state):
    if mode in state:
        return None, s.Integer(0)
    sign = (-1) ** sum(index < mode for index in state)
    return tuple(sorted((*state, mode))), s.Integer(sign)


def car_word_on_basis(i, k, ell, j, state):
    """Apply c†_i c†_k c_ell c_j to the original ordered CAR basis."""
    state, coefficient = annihilate_basis(j, state)
    if coefficient == 0:
        return None, s.Integer(0)
    state, factor = annihilate_basis(ell, state)
    if factor == 0:
        return None, s.Integer(0)
    state, factor2 = create_basis(k, state)
    if factor2 == 0:
        return None, s.Integer(0)
    state, factor3 = create_basis(i, state)
    if factor3 == 0:
        return None, s.Integer(0)
    return state, s.simplify(coefficient * factor * factor2 * factor3)


def normal_product_matrix_element(A, B, input_state, output_state):
    value = s.Integer(0)
    for i, j in A.todok():
        for k, ell in B.todok():
            state, sign = car_word_on_basis(i, k, ell, j, input_state)
            if state == output_state:
                value += A[i, j] * B[k, ell] * sign
    return s.simplify(value)


def main():
    started = time.monotonic()
    phase_path = HERE / "scalar_canonical_phase.json"
    phase = json.loads(phase_path.read_text())
    matter_path = HERE / "full-matter-ports.json"
    matter = MatterPorts()
    assert phase["root"] == ROOT_ID
    assert phase["source_sha256"] == matter.vertices["source_sha256"]
    for name, digest in phase["source_sha256"].items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
    for name, digest in matter.vertices["source_sha256"].items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name

    T6 = frame_for_degree(6)
    T2 = frame_for_degree(2)
    T4 = frame_for_degree(4)
    identity = s.eye(252)
    equal(T6 * T6.T + T2 * T2.T + T4 * T4.T, identity)
    equal(T6.T * T6, s.eye(28))
    equal(T2.T * T2, s.eye(84))
    equal(T4.T * T4, s.eye(140))

    # The full original free drift and its grade restrictions are checked at
    # symbolic momentum, rather than at a frozen static point.
    momentum = s.Matrix(K)
    drift = clean(-s.I * matter.H)
    drift6 = clean(T6.T * drift * T6)
    drift2 = clean(T2.T * drift * T2)
    drift4 = clean(T4.T * drift * T4)
    equal(drift * T6, T6 * drift6)
    equal(T2.T * drift, drift2 * T2.T)
    equal(drift * T4, T4 * drift4)
    # This is deliberately not upgraded to a commuting full grade projector:
    # the original background Yukawa is the actual 2 -> 6 one-way block.
    background_26 = clean(T6.T * drift * T2)
    assert background_26.todok()
    equal(drift * T2, T2 * drift2 + T6 * background_26)

    W_rows = phase["projected_CAR_couplings"]
    assert len(W_rows) == 61
    W = [decode(row["canonical_matter_vertex"]) for row in W_rows]
    ranks = []
    nonzero = []
    factorization = []
    for a, Wa in enumerate(W):
        # These are the canonical Hamiltonian vertices, not density V_a.
        assert int(W_rows[a]["coordinate"]) == a
        image6 = clean(T6.T * Wa * T2)
        equal(Wa, T6 * image6 * T2.T)
        equal(Wa * T6, zeros(252, 28))
        equal(T2.T * Wa, zeros(84, 252))
        equal(Wa.T * T2, zeros(252, 84))
        equal(Wa * Wa, zeros(252, 252))
        ranks.append(Wa.rank())
        nonzero.append(len(Wa.todok()))
        factorization.append({
            "coordinate": a,
            "rank": int(Wa.rank()),
            "nonzero_entries": len(Wa.todok()),
            "image_Lambda6": True,
            "annihilates_Lambda6": True,
            "annihilates_from_Lambda2_dual": True,
            "square_zero": True,
        })

    # Middle free propagation is handled by the exact grade intertwining.  We
    # record the matrix identity which proves all 61^2 time-separated words;
    # constructing exp(A t) symbolically would obscure, rather than strengthen,
    # the source identity.
    for Wa in W:
        equal(Wa * T6 * drift6, zeros(252, 28))
        equal(Wa * drift * T6, zeros(252, 28))
        # The factorization is the exact algebraic source of
        # Wa exp(t drift) Wb = 0 for every real momentum and t.
        assert clean(Wa * T6).todok() == {}
    pair_count = len(W) * len(W)

    # Fixed-N Dyson combinatorics.  An m-insertion term is indexed by a map
    # from insertion order to particle line.  A repeated line vanishes by the
    # one-line identity; only injections survive.
    surviving = {}
    for N in range(0, 7):
        values = {}
        for m in range(0, N + 3):
            values[str(m)] = math.factorial(N) // math.factorial(N - m) if m <= N else 0
        surviving[str(N)] = values
        assert values[str(N + 1)] == 0
    # Distinct lines do survive already at m=2: this is exactly the
    # source-normal-product mechanism and prevents a false carrier no-go.
    assert surviving["2"]["2"] == 2
    assert surviving["2"]["3"] == 0

    # A genuine distinct-particle normal product survives.  Evaluate the
    # complete original CAR word on occupation basis states; a repeated
    # creation/annihilation label would be a false witness because that word
    # vanishes before its coefficient is read.
    witness_input = (145, 152)
    witness_output = (0, 1)
    witness_value = normal_product_matrix_element(W[0], W[0], witness_input, witness_output)
    assert witness_value == s.Rational(27, 125)

    formal_paths = [
        ROOT / "Verification/physics/low-energy-phenomenology/external-composite-decay/FockRaising.lean",
        ROOT / "Verification/physics/low-energy-phenomenology/external-composite-decay/FockRaisingTensor.lean",
        ROOT / "Verification/physics/low-energy-phenomenology/external-composite-decay/FockRaisingAudit.lean",
        ROOT / "Verification/physics/low-energy-phenomenology/external-composite-decay/fock_raising_audit.json",
    ]
    formal_hashes = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                     for path in formal_paths}
    formal_audit = json.loads(formal_paths[-1].read_text())
    assert formal_audit["verdict"] == "CERTIFIED_FINITE_CAR_RAISING_WORDS_ON_ARBITRARY_NUMBER_SECTORS"
    assert all(check["exit_code"] == 0 for check in formal_audit["strict_checks"])
    for name, digest in formal_audit["input_sha256"].items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
    formal_input_hashes = {**formal_audit["input_sha256"], **formal_hashes}
    target_modes = {row for row in range(252) if T6[row, :].todok()}
    source_modes = {row for row in range(252) if T2[row, :].todok()}
    grade_entries = sum(len(Wa.todok()) for Wa in W)
    assert all(row in target_modes and column in source_modes
               for Wa in W for (row, column) in Wa.todok())

    output = {
        "root": ROOT_ID,
        "source_sha256": phase["source_sha256"],
        "input_sha256": {
            "Verification/physics/low-energy-phenomenology/external-composite-decay/scalar_canonical_phase.json": hashlib.sha256(phase_path.read_bytes()).hexdigest(),
            "Verification/physics/low-energy-phenomenology/external-composite-decay/full-matter-ports.json": hashlib.sha256(matter_path.read_bytes()).hexdigest(),
            "Verification/physics/low-energy-phenomenology/external-composite-decay/scalar_dyson_fixed_N.py": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            **formal_input_hashes,
        },
        "scope": "SOURCE_NATIVE_ALL61_SCALAR_INSERTION_FIXED_N_DYSON_TERMINATION",
        "canonical_vertex_definition": "W_a=-i*E^{-1}V_a from scalar_canonical_phase projected_CAR_couplings; density V_a is not substituted",
        "scalar_coordinate_count": 61,
        "canonical_vertex_ranks": sorted(set(ranks)),
        "canonical_vertex_nonzero_entry_range": [min(nonzero), max(nonzero)],
        "all61_factorization": factorization,
        "source_grade_scalar_condition": {
            "target_mode_count": len(target_modes),
            "source_mode_count": len(source_modes),
            "all_nonzero_W_entries_have_indicator_difference_one": True,
            "checked_nonzero_entries": grade_entries,
            "condition": "(1_Target(i)-1_Target(j)-1)*W_a[i,j]=0",
        },
        "all61_source_grade_law": "W_a=T6*(T6^T W_a T2)*T2^T; W_a*T6=0; T2^T*W_a=0",
        "all_momentum_middle_generator": "drift(k)*T6=T6*drift6(k), T2^T*drift(k)=drift2(k)*T2^T; therefore W_a exp(t drift(k)) W_b=0 for all a,b,k,t",
        "background_grade_boundary": "drift*T2=T2*drift2+T6*background_26; the original 2->6 Yukawa block is retained and no false full projector commutation is assumed",
        "all61_pair_count": pair_count,
        "all61_ordered_one_line_products_zero": True,
        "fixed_N_Dyson_surviving_assignment_counts_readout": surviving,
        "fixed_N_count_status": "finite N=0..6 combinatorial readout only; arbitrary-N termination is consumed by the strict Lean theorem bindings below",
        "fixed_N_termination": "every interaction-picture Dyson coefficient of order N+1 vanishes on the N-particle CAR sector by pigeonhole plus the one-line middle-insertion zero",
        "boson_time_ordering": "q_a(t) coefficients remain in their original ordered scalar product; they do not alter the CAR line pigeonhole",
        "two_particle_distinct_line_survives": True,
        "normal_product_source_witness": {
            "coordinates": [0, 0],
            "input_occupation": list(witness_input),
            "output_occupation": list(witness_output),
            "matrix_element": str(witness_value),
            "CAR_word": "sum_{i,j,k,l} W0[i,j] W0[k,l] c†_i c†_k c_l c_j",
        },
        "formal_fixed_N_consumer": {
            "matrix_theorem": "SourceFockRaising.matrix_word_vanishes_on_number_sector",
            "ordered_boson_tensor_theorem": "SourceFockRaising.tensor_word_vanishes_on_number_sector",
            "arbitrary_particle_number": True,
            "noncommuting_boson_order_preserved": True,
            "analytic_Dyson_convergence_claimed": False,
        },
        "finite_particle_scope": "exact algebraic fixed-N CAR Dyson termination for the source scalar61 insertion family; no positive Hilbert completion, continuum spectral measure, full four-block Hamiltonian, proton pole, Gamma or lifetime claim",
        "continuous_measure_status": "SOURCE_NATIVE_CONTINUOUS_MEASURE_REQUIRED",
        "lifetime_status": "SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED",
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    out = HERE / "scalar_dyson_fixed_N.json"
    out.write_text(json.dumps(output, separators=(",", ":")) + "\n")
    print("PASS all61 canonical source insertions, all-momentum Lambda6 middle propagation, and fixed-N Dyson termination", output["elapsed_seconds"], "seconds", flush=True)
    print("all61 ranks", sorted(set(ranks)), "nonzero range", min(nonzero), max(nonzero),
          "distinct-line normal-product witness", witness_value, flush=True)
    print("N+1 termination counts", {N: surviving[str(N)][str(N + 1)] for N in range(7)}, flush=True)


if __name__ == "__main__":
    main()
