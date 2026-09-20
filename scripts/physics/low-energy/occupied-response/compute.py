#!/usr/bin/env python3
"""Original occupied matter, gauge-pulse response, and the actual Euler Schur block.

Internal complex coordinates are realified before external Fourier substitution.
The full symbolic inverse is kept as two source-generated twelve-mode resolvents.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
import sys
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE))
sys.path.insert(0, str(BASE / "nonlinear-contact"))
import exact_readout as source
from slice_checks import GAMMA


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def zero(matrix):
    remaining = clean(matrix).todok()
    assert not remaining, list(remaining.items())[:6]


def decode(record, **symbols):
    return s.SparseMatrix(*record["shape"], {
        (i, j): s.sympify(value, locals=symbols)
        for i, j, value in record["entries"]})


def encode(matrix):
    return {"shape": list(matrix.shape), "entries": [
        [int(i), int(j), str(value)]
        for (i, j), value in sorted(clean(matrix).todok().items())]}


def realify(matrix):
    real = matrix.applyfunc(lambda value: s.expand(s.re(value)))
    imag = matrix.applyfunc(lambda value: s.expand(s.im(value)))
    return clean(real.row_join(-imag).col_join(imag.row_join(real)))


def real_column(matrix):
    return clean(matrix.applyfunc(s.re).col_join(matrix.applyfunc(s.im)))


def field_matrix(active, p):
    result = s.MutableSparseMatrix(289, 289, {})
    for i, j, powers, coefficient in active["Fourier_Jacobi_entries"]:
        result[i, j] += s.sympify(coefficient) * s.prod(
            p[mu] ** degree for mu, degree in enumerate(powers))
    return clean(result)


def solve_actual(matrix, rhs):
    domain = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)
    a = DomainMatrix.from_Matrix(matrix).convert_to(domain)
    b = DomainMatrix.from_Matrix(rhs).convert_to(domain)
    numerator, denominator = a.solve_den(b, method="rref")
    assert a * numerator == b * denominator
    assert denominator != domain.zero
    value = (numerator.to_Matrix() / domain.to_sympy(denominator)).applyfunc(s.simplify)
    zero(matrix * value - rhs)
    return clean(value)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    _, _, degrees, hashes = source.parse_source(args.root)
    phase = json.loads((BASE / "full-phase/receipt.json").read_text())
    modes = json.loads((BASE / "matter-modes/source.json").read_text())
    vertices = json.loads((BASE / "matter-vertices/receipt.json").read_text())
    active = json.loads((BASE / "active-gauge/receipt.json").read_text())
    assert phase["source_sha256"] == modes["source_sha256"] == vertices["source_sha256"] == hashes
    n = s.sympify(phase["source_lapse"])
    omega = s.sympify(phase["source_frequency"])
    spin = s.sympify(active["actual_background"]["dual_multiple"])
    assert spin == s.sqrt(2)
    p = s.symbols("p0:4", real=True)
    symbols = {str(value): value for value in p}
    zero_p = dict.fromkeys(p, 0)
    minus_p = dict(zip(p, [-value for value in p]))
    energy, k1, k2, k3 = s.symbols("E k1 k2 k3", real=True)
    momentum = [k1, k2, k3]
    fourier = dict(zip(p, [-s.I * energy, *[s.I * k for k in momentum]]))

    internal = [(degree, word) for degree in degrees
                for word in itertools.combinations(range(7), degree)]
    occupied = [63 * spin_index + internal.index((2, (color, 5)))
                for spin_index in range(4) for color in range(3)]
    frame = s.SparseMatrix(252, 12, {(row, col): 1 for col, row in enumerate(occupied)})
    projection = clean(frame * frame.T)
    zero(frame.T * frame - s.eye(12))
    gamma0 = clean(s.kronecker_product(GAMMA[0], s.eye(63)))
    gamma5 = clean(s.kronecker_product(s.diag(-1, -1, 1, 1), s.eye(63)))
    full_s = clean(gamma0 * gamma5)
    full_q = decode(phase["phase_generator"])
    small_s, small_q = [clean(frame.T * a * frame) for a in [full_s, full_q]]
    zero(full_s * frame - frame * small_s)
    zero(gamma5 * frame - frame * small_q)
    zero(full_q * frame - frame * small_q)
    zero(small_s * small_s - s.eye(12))
    zero(small_q * small_q - s.eye(12))

    full_d = decode(vertices["full_stationary_Dirac_operator"], **symbols)
    d = clean(frame.T * full_d * frame)
    zero(full_d * frame - frame * d)
    c0 = clean(d.diff(p[0]))
    c0_inverse = clean(s.I * n * frame.T * gamma0 * frame)
    zero(c0_inverse * c0 - s.eye(12))
    h0 = clean(-s.I * c0_inverse * d.subs(zero_p))
    hspace = [clean(c0_inverse * d.diff(p[j + 1])) for j in range(3)]
    h = clean(h0 + sum((momentum[j] * hspace[j] for j in range(3)), s.zeros(12)))
    drift = clean(p[0] * s.eye(12) + s.I * h0 +
                  sum((p[j + 1] * hspace[j] for j in range(3)), s.zeros(12)))
    zero(d - c0 * drift)
    original_h0 = clean(n * s.sqrt(2) * decode(modes["original_H_constant"]))
    original_hspace = [clean(n * decode(item)) for item in modes["original_H_spatial"]]
    zero(original_h0 * frame - frame * (h0 + omega * small_q))
    for actual, small in zip(original_hspace, hspace):
        zero(actual * frame - frame * small)
    for coefficient in [h0] + hspace:
        zero(coefficient.H - coefficient)
        zero(coefficient * small_q - small_q * coefficient)

    seed = s.Matrix(active["actual_background"]["primal_H"]).applyfunc(s.sympify)
    prepared = seed / 2
    zero(prepared.H * prepared - s.ones(1))
    zero(h0 * prepared)
    zero((h0 + omega * small_q) * prepared - omega * small_q * prepared)
    prepared_phases = [clean((s.eye(12) + sign * small_q) * prepared / 2) for sign in [-1, 1]]
    for sign, branch in zip([-1, 1], prepared_phases):
        zero((h0 + omega * small_q) * branch - sign * omega * branch)
        zero(branch.H * branch - s.ones(1) / 2)
    zero(sum(prepared_phases, s.zeros(12, 1)) - prepared)
    zero(d.subs(zero_p) * seed)
    source_dual = clean(spin * seed.T * small_s)
    zero(source_dual * d.subs(zero_p))

    gauge_vertices = [row for row in vertices["primitive_vertices"] if row["group"] == "gauge_A"]
    assert [row["coordinate"] for row in gauge_vertices] == [list(index)
        for index in itertools.product(range(4), range(12))]
    generator, reader, forcing, reader_seed = [], [], [], []
    for row in gauge_vertices:
        value = decode(row["operator"], **symbols)
        assert not value.free_symbols
        full_t = clean(gamma0 * value)
        full_b = clean(spin * (full_s * value + value.H * full_s) / 2)
        t = clean(frame.T * full_t * frame)
        b = clean(frame.T * full_b * frame)
        zero(full_t * frame - frame * t)
        zero(full_b * frame - frame * b)
        zero(t.H - t)
        zero(b.H - b)
        zero(small_q * t - t * small_q)
        zero(b + spin * small_q * t)
        zero(c0_inverse * (frame.T * value * frame) / n - s.I * t)
        generator.append(t)
        reader.append(b)
        forcing.append(clean(-s.I * t * seed))
        reader_seed.append(clean(b * seed))
    force = clean(s.SparseMatrix.hstack(*forcing))
    t_seed = clean(s.SparseMatrix.hstack(*[t * seed for t in generator]))
    b_seed = clean(s.SparseMatrix.hstack(*reader_seed))
    force_real = real_column(force)
    print("PASS original H12, unit prepared, actual clock on its trajectory, and all48 Hermitian gauge forces", flush=True)

    fields = active["fields"]
    primal = [i for i, row in enumerate(fields) if row["group"] == "primal_H"]
    dual = [i for i, row in enumerate(fields) if row["group"] == "dual_H"]
    matter = primal + dual
    gauge = [i for i, row in enumerate(fields) if row["group"] == "gauge_A"]
    expected_coordinates = [list(index) for index in itertools.product(range(2), range(4), range(3))]
    assert [fields[i]["coordinate"] for i in primal] == expected_coordinates
    assert [fields[i]["coordinate"] for i in dual] == expected_coordinates
    assert [fields[i]["coordinate"] for i in gauge] == [row["coordinate"] for row in gauge_vertices]
    full_hessian = field_matrix(active, p)
    matter_block = clean(full_hessian.extract(matter, matter))
    matter_gauge = clean(full_hessian.extract(matter, gauge))
    gauge_matter = clean(full_hessian.extract(gauge, matter))
    conjugation = s.diag(s.eye(12), -s.eye(12))
    graph = clean(s.eye(24).col_join(spin * realify(small_s) * conjugation))
    real_drift = realify(drift)
    equation_embedding = clean(matter_block.diff(p[0]) * graph)
    zero(matter_block * graph - equation_embedding * real_drift)
    zero(matter_gauge + equation_embedding * force_real)
    # This is the original independent-dual graph, not a replacement of its Euler rows.
    c = conjugation
    source_matter_block = clean(s.zeros(24).row_join(n * realify(d.subs(minus_p)).T * c)
        .col_join((n * c * realify(d)).row_join(s.zeros(24))))
    zero(matter_block - source_matter_block)

    split = clean(s.eye(12).row_join(s.I * s.eye(12))
                  .col_join(s.eye(12).row_join(-s.I * s.eye(12))))
    unsplit = clean(s.eye(12).row_join(s.eye(12))
                    .col_join((-s.I * s.eye(12)).row_join(s.I * s.eye(12))) / 2)
    zero(split * unsplit - s.eye(24))
    zero(unsplit * split - s.eye(24))
    h_minus = clean(h.subs(dict(zip(momentum, [-k for k in momentum])), simultaneous=True))
    plus_denominator = clean(energy * s.eye(12) - h)
    minus_denominator = clean(energy * s.eye(12) + h_minus)
    split_drift = s.diag(-s.I * plus_denominator, -s.I * minus_denominator.T)
    zero(split * real_drift.subs(fourier) * unsplit - split_drift)
    zero(split * real_drift.subs(minus_p).subs(fourier) * unsplit -
         s.diag(s.I * minus_denominator, s.I * plus_denominator.T))
    zero(realify(c0_inverse) * realify(c0) - s.eye(24))
    zero(realify(c0) * realify(c0_inverse) - s.eye(24))
    zero(split * force_real - force.col_join(force.conjugate()))
    current_split_reader = clean(b_seed.H.row_join(b_seed.T))
    zero(gauge_matter * graph - current_split_reader * split)
    print("PASS all-symbol original48 primal/dual Euler rows, all48 current readers, and ordered p/-p resolvent factorization", flush=True)

    # The inverse interface retains the source twelve-dimensional factors.
    # Pi = Bseed^dagger Rplus Tseed - Bseed^T Rminus^T conjugate(Tseed).
    samples = []
    sample_values = [("time", 3 * omega, [0, 0, 0]),
                     ("spatial_plus", 3 * omega, [0, 0, omega / (2 * n)]),
                     ("spatial_opposite", -3 * omega, [0, 0, -omega / (2 * n)])]
    for label, e_value, k_value in sample_values:
        values = dict(zip([energy] + momentum, [e_value] + k_value))
        p_values = {p[0]: -s.I * e_value, **{p[j + 1]: s.I * k_value[j] for j in range(3)}}
        full_value = clean(full_hessian.subs(p_values))
        mm = clean(matter_block.subs(p_values))
        mg = clean(matter_gauge.subs(p_values))
        actual_response = solve_actual(mm, -mg)
        rp = solve_actual(plus_denominator.subs(values), s.eye(12))
        rm = solve_actual(minus_denominator.subs(values), s.eye(12))
        complex_response = clean((rp * t_seed).col_join(-rm.T * t_seed.conjugate()))
        generated_response = clean(graph * unsplit * complex_response)
        zero(actual_response - generated_response)
        pi = clean(b_seed.H * rp * t_seed - b_seed.T * rm.T * t_seed.conjugate())
        zero(full_value.extract(gauge, matter) * actual_response - pi)
        all_rows = clean(full_value[:, matter] * actual_response + full_value[:, gauge])
        zero(all_rows[matter, :])
        zero(all_rows[gauge, :] - full_value.extract(gauge, gauge) - pi)
        samples.append({"label": label, "energy": str(e_value), "momentum": list(map(str, k_value)),
            "original_matter_response": encode(actual_response), "induced_current_response": encode(pi),
            "twelve_mode_positive_resolvent": encode(rp), "twelve_mode_negative_resolvent": encode(rm),
            "all_289_rows_after_gauge_injection_and_generated_matter": encode(all_rows),
            "all_48_original_primal_and_independent_dual_rows_zero": True,
            "all_48_by_48_original_current_Schur_entries_match": True,
            "nonmatter_rows_retained_not_declared_a_full_boson_solution": True})
        print("PASS", label, "nonempty inverse domain; all48x48 source Schur entries and all48 original matter rows", flush=True)
    zero(decode(samples[1]["induced_current_response"]).T - decode(samples[2]["induced_current_response"]))

    excluded_point = {energy: 3 * omega, k1: 0, k2: 0, k3: omega / n}
    excluded_plus = clean(plus_denominator.subs(excluded_point) / omega)
    assert excluded_plus.rank() == 11 and excluded_plus.det() == 0

    z = s.symbols("z", real=True)
    scaled_h0 = clean(h0 / omega)
    zero(scaled_h0 * prepared)
    char = s.factor(scaled_h0.charpoly().as_expr())
    symbolic_plus = (z * s.eye(12) - scaled_h0).inv(method="DM")
    symbolic_minus = (z * s.eye(12) + scaled_h0).inv(method="DM")
    diagonal = s.factor((b_seed[:, 0].H * symbolic_plus * t_seed[:, 0] -
        b_seed[:, 0].T * symbolic_minus.T * t_seed[:, 0].conjugate())[0] / omega)
    expected = -200 * s.sqrt(30) / (27 * (z * z - 4))
    assert s.simplify(diagonal - expected) == 0
    zero(decode(samples[0]["induced_current_response"])[0:1, 0:1] -
         s.Matrix([[expected.subs(z, 3)]]))

    result = {"scope": "ORIGINAL_OCCUPIED_GAUGE_RESPONSE_AND_COMPLETE_CURRENT_SCHUR_BLOCK",
        "source_sha256": hashes, "source_lapse": str(n), "source_frequency": str(omega),
        "source_dual_multiple": str(spin), "occupied_full_indices_zero_based": occupied,
        "occupied_frame": encode(frame), "source_prepared": encode(prepared),
        "source_prepared_norm_squared": 1, "original_background_matter_amplitude": 2,
        "source_prepared_phase_branches": list(map(encode, prepared_phases)),
        "prepared_phase_branch_norms_squared": ["1/2", "1/2"],
        "source_independent_dual_row": encode(source_dual),
        "occupied_phase_charge": encode(small_q), "occupied_adjoint_swap": encode(small_s),
        "stationary_H_constant": encode(h0), "H_spatial_coefficients": list(map(encode, hspace)),
        "original_H_constant": encode(h0 + omega * small_q),
        "prepared_original_clock_identity": "Horiginal(0)w=omega Qw; Hstationary(0)w=0",
        "old_phase_clock_operator_identified_on_arbitrary_states": False,
        "all_source_H_coefficients_preserve_H12_and_are_Hermitian": True,
        "gauge_coordinates": [row["coordinate"] for row in gauge_vertices],
        "gauge_Hamiltonian_forces": list(map(encode, generator)),
        "original_current_readers": list(map(encode, reader)),
        "current_generator_identity": "B_c=-s Q T_c; T_c=gamma0 V_c; original current B is retained",
        "all_48_raw_gauge_forces_preserve_H12_and_are_Hermitian": True,
        "all_48_gauge_forces_commute_with_original_phase_charge": True,
        "canonical_dual_graph_real": encode(graph), "real_time_equation_embedding": encode(equation_embedding),
        "actual_real_matter_operator": encode(matter_block), "original_real_drift": encode(real_drift),
        "original_real_forcing": encode(force_real), "real_to_double_complex": encode(split),
        "double_complex_to_real": encode(unsplit), "T_times_original_background": encode(t_seed),
        "B_times_original_background": encode(b_seed),
        "positive_resolvent_denominator": encode(plus_denominator),
        "negative_resolvent_denominator": encode(minus_denominator),
        "symbolic_original_matter_rows": "M48(p)L=C Realify[p0 I+i h0+sum_j Hj pj]; H_mA=-C f",
        "symbolic_original_current_rows": "H_Am(p)L=[Bseed^dagger,Bseed^T] Split",
        "all_symbolic_primal_dual_forcing_and_current_identities": True,
        "Fourier_order": "realify with real formal derivatives first; then p0=-iE,pj=ikj",
        "ordered_resolvent_formula": "Pi=Bseed^dagger (E-h(k))^-1 Tseed-Bseed^T (E+h(-k))^-T conjugate(Tseed)",
        "inverse_domain": "det(E-h(k)) != 0 and det(E+h(-k)) != 0; samples establish nonemptiness",
        "opposite_symbol_factorization": "Split K_R(-p_F) Split^-1=diag(i(E+h(-k)),i(E-h(k))^T)",
        "retained_pole_example": {"energy": str(3 * omega), "momentum": ["0", "0", str(omega / n)],
            "positive_resolvent_denominator_rank": 11, "positive_resolvent_denominator_determinant": 0},
        "original_matter_amplitude_squared_preserved": 4,
        "zero_momentum_scaled_stationary_characteristic_polynomial": str(char),
        "source_diagonal_response_E_equals_z_omega": str(diagonal),
        "samples": samples, "opposite_transfer_current_reciprocity": True,
        "quantum_input_scope": "source matrices and original field response; CAR time-response theorem is a separate consumer",
        "selfconsistent_bosonic_solution_or_vacuum_loop_measure_claimed": False,
        "elapsed_seconds": round(time.monotonic() - started, 3)}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print("PASS original nonzero response", diagonal, "; no full boson solution or vacuum loop measure substituted", flush=True)


if __name__ == "__main__":
    main()
