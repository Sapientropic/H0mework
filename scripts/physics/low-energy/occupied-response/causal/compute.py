#!/usr/bin/env python3
"""Source-prepared retarded gauge response and its positive-regulator transform."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import sys
import time

import sympy as s

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
spec = importlib.util.spec_from_file_location("occupied_source_response", PARENT / "compute.py")
parent = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = parent
spec.loader.exec_module(parent)
clean, zero, decode, encode = parent.clean, parent.zero, parent.decode, parent.encode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    occupied = json.loads((PARENT / "receipt.json").read_text())
    active = json.loads((PARENT.parent / "active-gauge/receipt.json").read_text())
    assert occupied["source_sha256"] == parent.source.parse_source(args.root)[3]
    n = s.sympify(occupied["source_lapse"])
    omega = s.sympify(occupied["source_frequency"])
    spin = s.sympify(occupied["source_dual_multiple"])
    assert omega.is_positive and spin == s.sqrt(2)
    h = decode(occupied["stationary_H_constant"])
    scaled_h = clean(h / omega)
    prepared = decode(occupied["source_prepared"])
    seed = 2 * prepared
    small_s = decode(occupied["occupied_adjoint_swap"])
    small_q = decode(occupied["occupied_phase_charge"])
    zero(h.H - h)
    zero(h * prepared)
    zero(prepared.H * prepared - s.ones(1))
    ts = decode(occupied["T_times_original_background"])
    bs = decode(occupied["B_times_original_background"])
    generators = list(map(decode, occupied["gauge_Hamiltonian_forces"]))
    readers = list(map(decode, occupied["original_current_readers"]))
    zero(ts - s.SparseMatrix.hstack(*[matrix * seed for matrix in generators]))
    zero(bs - s.SparseMatrix.hstack(*[matrix * seed for matrix in readers]))
    for t_matrix, b_matrix in zip(generators, readers):
        zero(t_matrix.H - t_matrix)
        zero(b_matrix.H - b_matrix)
        zero(b_matrix + spin * small_q * t_matrix)

    # Spectrum and polynomial projectors are generated from the actual source matrix.
    eigenvalues = scaled_h.eigenvals()
    assert sum(eigenvalues.values()) == 12
    rates = sorted(eigenvalues)
    assert all(rate.is_real and rate.is_rational for rate in rates)
    projectors = {}
    for rate in rates:
        projector = s.eye(12)
        for other in rates:
            if rate != other:
                projector = clean(projector * (scaled_h - other * s.eye(12)) / (rate - other))
        zero(projector.H - projector)
        zero(projector * projector - projector)
        zero(scaled_h * projector - rate * projector)
        assert s.trace(projector) == eigenvalues[rate]
        projectors[rate] = projector
    zero(sum(projectors.values(), s.zeros(12)) - s.eye(12))
    for first in rates:
        for second in rates:
            if first != second:
                zero(projectors[first] * projectors[second])

    # A Laurent variable encodes exp(-i omega t/2) without transcendental simplification.
    phase = s.symbols("phase", nonzero=True)
    exponents = {rate: int(2 * rate) for rate in rates}
    assert all(exponents[rate] == 2 * rate for rate in rates)
    flow = clean(sum((projectors[rate] * phase ** exponents[rate] for rate in rates), s.zeros(12)))
    inverse_flow = clean(flow.subs(phase, 1 / phase))
    adjoint_flow = clean(flow.conjugate().T.subs(s.conjugate(phase), 1 / phase))
    zero(inverse_flow - adjoint_flow)
    zero(flow * inverse_flow - s.eye(12))
    zero(inverse_flow * flow - s.eye(12))
    zero(flow.subs(phase, 1) - s.eye(12))

    def time_derivative(matrix):
        return clean(-s.I * omega * phase * matrix.diff(phase) / 2)

    zero(time_derivative(flow) + s.I * h * flow)
    zero(flow * prepared - prepared)
    original_h = decode(occupied["original_H_constant"])
    original_branches = list(map(decode, occupied["source_prepared_phase_branches"]))
    for sign, branch in zip([-1, 1], original_branches):
        zero(original_h * branch - sign * omega * branch)
    print("PASS actual five-rate spectral resolution; source unitary flow and original prepared clock branches", flush=True)

    forward_weights = {rate: clean(bs.H * projectors[rate] * ts) for rate in rates}
    backward_weights = {rate: clean((ts.H * projectors[rate] * bs).T) for rate in rates}
    for rate in rates:
        zero(backward_weights[rate] - forward_weights[rate].conjugate())
    residues = {rate: clean(forward_weights[rate] - backward_weights.get(-rate, s.zeros(48)))
                for rate in rates}
    response = clean(s.I * sum((backward_weights[rate] * phase ** (-exponents[rate]) -
                               forward_weights[rate] * phase ** exponents[rate]
                               for rate in rates), s.zeros(48)))
    zero(response + s.I * sum((residues[rate] * phase ** exponents[rate]
                              for rate in rates), s.zeros(48)))
    zero(response.conjugate().subs(s.conjugate(phase), 1 / phase) - response)
    jump = clean(response.subs(phase, 1))
    explicit_jump = s.MutableSparseMatrix(48, 48, {})
    for b, reader in enumerate(readers):
        for c, generator in enumerate(generators):
            explicit_jump[b, c] = s.expand(4 * s.I *
                (prepared.H * (generator * reader - reader * generator) * prepared)[0])
    zero(jump - explicit_jump)

    fields = active["fields"]
    primal = [i for i, row in enumerate(fields) if row["group"] == "primal_H"]
    dual = [i for i, row in enumerate(fields) if row["group"] == "dual_H"]
    matter = primal + dual
    gauge = [i for i, row in enumerate(fields) if row["group"] == "gauge_A"]
    p = s.symbols("p0:4", real=True)
    full = parent.field_matrix(active, p)
    zero_p = dict.fromkeys(p, 0)
    mm = clean(full.extract(matter, matter))
    mg = clean(full.extract(matter, gauge))
    gm = clean(full.extract(gauge, matter))
    zero(mg - mg.subs(zero_p))
    zero(gm - gm.subs(zero_p))
    derivative_matrix = clean(mm.diff(p[0]))
    constant_matrix = clean(mm.subs(zero_p))
    zero(mm.subs(dict.fromkeys(p[1:], 0)) - constant_matrix - p[0] * derivative_matrix)
    graph = decode(occupied["canonical_dual_graph_real"])
    unsplit = decode(occupied["double_complex_to_real"])
    complex_pulse = clean(-s.I * flow * ts)
    conjugate_pulse = clean(complex_pulse.conjugate().subs(s.conjugate(phase), 1 / phase))
    matter_pulse = clean(graph * unsplit * complex_pulse.col_join(conjugate_pulse))
    zero(matter_pulse.conjugate().subs(s.conjugate(phase), 1 / phase) - matter_pulse)
    zero(derivative_matrix * time_derivative(matter_pulse) + constant_matrix * matter_pulse)
    zero(derivative_matrix * matter_pulse.subs(phase, 1) + mg)
    zero(gm * matter_pulse - response)
    print("PASS all48 pulse sources: original primal/independent-dual equations for t>0, delta-source jumps, all2304 current readouts", flush=True)

    # The scalar transform fixes the retarded half-plane, then finite source weights commute with it.
    time_variable = s.symbols("t", real=True, nonnegative=True)
    energy = s.symbols("E", real=True)
    eta = s.symbols("eta", real=True, positive=True)
    z = energy + s.I * eta
    transforms = []
    laplace = s.zeros(48)
    for rate in rates:
        frequency = omega * rate
        exponent = s.I * (energy - frequency) - eta
        primitive = s.exp(exponent * time_variable) / exponent
        assert s.simplify(s.diff(primitive, time_variable) - s.exp(exponent * time_variable)) == 0
        norm_squared = s.simplify(s.exp(exponent * time_variable) *
                                 s.conjugate(s.exp(exponent * time_variable)))
        assert s.simplify(norm_squared - s.exp(-2 * eta * time_variable)) == 0
        assert s.limit(s.exp(-eta * time_variable), time_variable, s.oo) == 0
        integral = -1 / exponent
        assert s.simplify(integral - s.I / (z - frequency)) == 0
        laplace += -s.I * residues[rate] * integral
        transforms.append({"scaled_rate": str(rate), "frequency": str(frequency),
            "damped_exponent": str(exponent), "integral": str(s.I / (z - frequency)),
            "modulus": "exp(-eta*t)", "infinite_endpoint": 0})
    # Equalities are compared over the small common denominator before substitution.
    z_formal = s.symbols("z")
    plus_inverse = sum((projectors[rate] / (z_formal - omega * rate)
                        for rate in rates), s.zeros(12))
    minus_inverse = sum((projectors[rate] / (z_formal + omega * rate)
                         for rate in rates), s.zeros(12))

    def rational_zero(matrix):
        for value in clean(matrix).todok().values():
            assert s.cancel(value) == 0, value

    rational_zero((z_formal * s.eye(12) - h) * plus_inverse - s.eye(12))
    rational_zero(plus_inverse * (z_formal * s.eye(12) - h) - s.eye(12))
    rational_zero((z_formal * s.eye(12) + h) * minus_inverse - s.eye(12))
    rational_zero(minus_inverse * (z_formal * s.eye(12) + h) - s.eye(12))
    meromorphic = sum((residues[rate] / (z_formal - omega * rate)
                      for rate in rates), s.zeros(48))
    original_resolvent_reader = bs.H * plus_inverse * ts - bs.T * minus_inverse.T * ts.conjugate()
    rational_zero(meromorphic - original_resolvent_reader)
    rational_zero(laplace - meromorphic.subs(z_formal, z))
    # Im z>0 excludes every generated real spectral pole; the same statement covers the opposite factor.
    for rate in rates:
        assert s.im(z - omega * rate) == eta
        assert s.im(z + omega * rate) == eta
    print("PASS positive-regulator Fourier-Laplace transform of all48x48 source retarded weights equals the original ordered resolvent", flush=True)

    regulated_energy = omega * (3 + s.I)
    values = {p[0]: -s.I * regulated_energy, p[1]: 0, p[2]: 0, p[3]: 0}
    actual_matter = parent.solve_actual(mm.subs(values), -mg)
    actual_current = clean(gm * actual_matter)
    transformed_current = meromorphic.subs(z_formal, regulated_energy).applyfunc(s.simplify)
    zero(actual_current - transformed_current)
    zero(mm.subs(values) * actual_matter + mg)
    zero(meromorphic.subs(z_formal, 3 * omega).applyfunc(s.simplify) -
         decode(occupied["samples"][0]["induced_current_response"]))
    diagonal = s.factor(meromorphic[0, 0])
    time_diagonal = s.simplify(response[0, 0].subs(phase, s.exp(-s.I * omega * time_variable / 2)))
    assert s.simplify(s.expand_complex(time_diagonal) - 8 * s.sqrt(2) * s.sin(2 * omega * time_variable)) == 0
    assert s.simplify(diagonal + 16 * s.sqrt(2) * omega / (z_formal ** 2 - 4 * omega ** 2)) == 0
    zero(residues[0])
    print("PASS original complex-energy matter Schur consumer at z=(3+i)omega; real-energy parent consumer; nonzero causal sine response", flush=True)

    result = {"scope": "SOURCE_PREPARED_ZERO_SPATIAL_MOMENTUM_RETARDED_GAUGE_RESPONSE",
        "source_sha256": occupied["source_sha256"], "source_frequency": str(omega),
        "source_lapse": str(n), "source_dual_multiple": str(spin),
        "source_prepared": encode(prepared), "source_prepared_norm_squared": 1,
        "original_matter_amplitude_squared": 4,
        "generated_spectrum": [{"scaled_rate": str(rate), "frequency": str(omega * rate),
            "multiplicity": int(eigenvalues[rate]), "projector": encode(projectors[rate]),
            "forward_current_weight": encode(forward_weights[rate]),
            "backward_current_weight": encode(backward_weights[rate]),
            "merged_retarded_residue": encode(residues[rate]),
            "merged_residue_rank": int(residues[rate].rank())} for rate in rates],
        "phase_coordinate": "phase=exp(-i omega t/2)", "source_unitary_flow": encode(flow),
        "source_retarded_current_positive_time": encode(response),
        "source_retarded_matter_positive_time": encode(matter_pulse),
        "retarded_support": "zero for t<0; positive-time formula for t>0; right limit at0 recorded separately",
        "current_right_jump": encode(jump), "current_jump_nonzero_entries": len(jump.todok()),
        "original_matter_right_jump": encode(matter_pulse.subs(phase, 1)),
        "original_matter_equations_for_positive_time": True,
        "original_primal_and_independent_dual_delta_jumps": True,
        "current_commutator_jump_identity": "chi_bc(0+)=4i w^dagger(T_c B_b-B_b T_c)w",
        "source_response_formula": "chi_bc(t)=4i[w^dagger T_c exp(i h t)B_b w-w^dagger B_b exp(-i h t)T_c w] for t>=0",
        "spectral_time_formula": "chi(t)=-i sum_r R_r exp(-i omega*r*t), with source-generated R_r",
        "scalar_transform_checks": transforms,
        "transform_domain": "E real, eta>0, z=E+i eta",
        "transform_convention": "Pi_R(E+i eta,0)=integral_0^infinity exp(iEt-eta*t) chi(t) dt",
        "all_48_by_48_transform_equals_original_resolvent": True,
        "zero_rate_current_pole_cancels": True,
        "regulated_consumer": {"energy": str(regulated_energy), "eta": str(omega),
            "original_matter_response": encode(actual_matter), "original_current_response": encode(actual_current),
            "all_original_matter_rows_zero": True, "all_2304_Schur_entries_match_causal_transform": True},
        "real_boundary_away_from_generated_poles": "finite rational sum converges to original Pi(E,0) as eta->0+ when E is not a generated pole",
        "source_diagonal_time_kernel": "8*sqrt(2)*sin(2*omega*t)",
        "source_diagonal_transform": str(diagonal),
        "retarded_prescription_selected_from_original_time_equation_and_zero_past": True,
        "spatial_scope": "k=0; no all-space continuum integral claimed",
        "new_vacuum_or_Feynman_prescription_or_loop_measure_added": False,
        "elapsed_seconds": round(time.monotonic() - started, 3)}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
