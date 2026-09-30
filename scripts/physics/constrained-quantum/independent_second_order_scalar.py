#!/usr/bin/env python3
"""Original-density full70 verification of the actual second-order scalar field."""
from __future__ import annotations

import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import time

import sympy as s

from dynamic import SourceExchange, ROOT_ID, decode, P

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
L = s.Symbol("lam")


def clean(value): return s.SparseMatrix(value).applyfunc(s.expand)


def equal(left, right):
    residual = clean(left-right)
    if residual.todok(): residual = residual.applyfunc(s.simplify)
    assert not residual.todok(), list(residual.todok())[:3]


def raw_action_data():
    path = BASE/"active-gauge/compute.py"
    spec = importlib.util.spec_from_file_location("independent_scalar_original_density", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module, module.build(ROOT)


def realify(value):
    real, imaginary = value.applyfunc(s.re), value.applyfunc(s.im)
    return clean(real.row_join(-imaginary).col_join(imaginary.row_join(real)))


def main():
    started = time.monotonic()
    candidate_path = HERE/"second_order_scalar.json"
    candidate = json.loads(candidate_path.read_text())
    assert candidate["root"] == ROOT_ID
    for name, digest in candidate["input_sha256"].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    source = SourceExchange()
    assert candidate["source_sha256"] == source.vertices["source_sha256"]
    original, (coordinates, _, _, data, provenance) = raw_action_data()
    assert coordinates.fields == source.active["fields"]
    assert provenance["source_sha256"] == source.active["source_sha256"]
    N, c = data["n"], source.clock
    assert s.simplify(N-source.N) == 0 and s.simplify(c*c-2*N*N) == 0 and c > 0
    assert s.simplify(s.sympify(candidate["original_lapse"])-N) == 0
    assert s.simplify(s.sympify(candidate["original_clock"])-c) == 0
    # This is the Hessian of N*(1/2*g^{mu nu}D_mu phi.D_nu phi-|eta|²),
    # differentiated before specializing its first-jet symbol.
    connections = [clean(sum((data["a0"][mu, a]*data["rho4"][a] for a in range(12)), s.zeros(70)))
                   for mu in range(4)]
    assert all(not clean(value+value.T).todok() for value in connections)
    equal(connections[0], s.zeros(70))
    metric = data["e0"].inv()*original.ETA*data["e0"].inv().T
    raw_hessian = -2*N*s.eye(70)
    for mu, nu in itertools.product(range(4), repeat=2):
        raw_hessian -= N*metric[mu, nu]*(P[mu]*s.eye(70)+connections[mu])*(P[nu]*s.eye(70)+connections[nu])
    raw_hessian = clean(raw_hessian)
    scalar = source.scalar
    J = data["inclusion"]
    PJ = clean(J*(J.T*J).inv()*J.T)
    P61 = clean(s.eye(70)-PJ)
    rotations = [clean(value/data["alpha"]) for value in connections[1:]]
    casimir = clean(sum((value*value for value in rotations), s.zeros(70)))
    doublet = clean(-s.Rational(4, 3)*casimir*P61)
    singlet = clean(P61-doublet)
    for key, value in [("peripheral_projector", P61), ("singlet_projector", singlet), ("doublet_projector", doublet)]:
        equal(value, decode(scalar[key])); equal(value*value, value)
    assert [s.trace(singlet), s.trace(doublet)] == [25, 36]
    for rotation in rotations: equal(rotation*singlet, s.zeros(70))
    u, r1, r2, r3 = s.symbols("u r1 r2 r3")
    normalized = decode(scalar["normalized_full_scalar_operator"])
    equal(raw_hessian, N*normalized.subs(dict(zip([u, r1, r2, r3], [P[0]/c, *[p/s.sqrt(2) for p in P[1:]]]))))

    dynamic_path, feedback_path = HERE/"dynamic.json", HERE/"external-leg-feedback.json"
    dynamic, feedback = [json.loads(path.read_text()) for path in [dynamic_path, feedback_path]]
    for record in [dynamic, feedback]: assert record["root"] == ROOT_ID and record["source_sha256"] == source.vertices["source_sha256"]
    sample = next(row for row in dynamic["samples"] if row["name"] == "energy_transfer")
    rate = decode(sample["transfer"])
    inside = [(degree, word) for degree in (6, 2, 4) for word in itertools.combinations(range(7), degree)]
    degree4 = [63*spin+i for spin in range(4) for i, (degree, _) in enumerate(inside) if degree == 4]
    projector4 = s.SparseMatrix(252, 252, {(i, i): 1 for i in degree4})
    equal(projector4*source.D, source.D*projector4)
    assert len(source.Y) == 70
    for vertex in source.Y:
        equal(vertex*projector4, s.zeros(252)); equal(projector4*vertex, s.zeros(252))
    legs = [source.leg(4, list(map(s.sympify, q))) for q in sample["scaled_momenta"][:2]]
    for leg in legs:
        equal(projector4*leg.vector, leg.vector)
        equal(leg.vector.H*source.S*projector4, leg.vector.H*source.S)
    pair_updates = [row for row in feedback["source_updates"] if row["source_pair"] == 0]
    assert len(pair_updates) == 8
    outputs_checked = 0
    for row in pair_updates:
        amplitude = decode(row["field_fourier_amplitude"])
        vertex = clean(sum((value*V for value, V in zip(amplitude, source.V)), s.zeros(252)))
        equal(vertex*projector4, projector4*vertex)
        for side in ["primal", "independent_dual_transposed"]:
            output = decode(row[side]["augmented_output"])
            equal(projector4*output, output)
            for scalar_vertex in source.Y:
                if side == "primal": equal(scalar_vertex*output, s.zeros(252, output.cols))
                else: equal(output.T*scalar_vertex, s.zeros(output.cols, 252))
            outputs_checked += 1
    assert outputs_checked == 16

    occupied_path = BASE/"occupied-response/receipt.json"
    occupied = json.loads(occupied_path.read_text())
    psi = clean(2*decode(occupied["occupied_frame"])*decode(occupied["source_prepared"]))
    chi = clean(s.sqrt(2)*psi.H*source.S)
    Mfull = clean(s.SparseMatrix.hstack(*[clean(vertex*psi/N) for vertex in source.Y]))
    degree6 = [63*spin+i for spin in range(4) for i, (degree, _) in enumerate(inside) if degree == 6]
    Mcomplex = Mfull[:, :35]
    equal(Mfull[:, 35:], s.I*Mcomplex)
    equal(Mcomplex, decode(json.loads((BASE/"full-phase/receipt.json").read_text())["stationary_scalar_mixing"]))
    Mreal = realify(Mcomplex.extract(degree6, list(range(35))))
    equal(Mreal, decode(scalar["source_phase_mixing_real"]))
    for vertex in source.Y: equal(chi*vertex, s.zeros(1, 252))
    print("PASS raw full70 density Hessian, actual singlet/doublet projectors, Lambda4 current and original M readback", flush=True)

    native_path = HERE/"native_boson_residual.json"
    native = json.loads(native_path.read_text())
    assert native["root"] == ROOT_ID and native["source_sha256"] == source.vertices["source_sha256"]
    equal(rate, decode(native["transfer"]))
    numerator = decode(scalar["peripheral_scalar_green_numerator"])
    denominator = s.sympify(scalar["peripheral_scalar_green_denominator"])
    reports = []
    source_terms = {row["harmonic"]: row for row in native["full70_scalar_quadratic_Euler"]}
    saved = {row["harmonic"]: row for row in candidate["harmonics"]}
    assert set(saved) == {-2, 0, 2}
    forces, denominators = {}, {}
    growing_residue = None
    for h in [-2, 0, 2]:
        row = saved[h]
        f = clean(-P61*decode(source_terms[h]["value"]))
        assert len(f.todok()) == 4
        equal(f, decode(row["physical_force"]))
        equal(P61*f, f); equal(singlet*f, f); equal(doublet*f, s.zeros(70, 1))
        equal(J.T*f, s.zeros(9, 1)); equal(Mreal*f, s.zeros(56, 1)); equal(Mfull*f, s.zeros(252, 1))
        k = clean(h*rate[1:, 0]/s.I)
        frequency = s.simplify(h*rate[0])
        omega2 = s.simplify(N*N*((k.T*k)[0]-2))
        equal(k, decode(row["spatial_momentum"]))
        assert s.simplify(frequency-s.sympify(row["source_frequency"])) == 0
        assert s.simplify(omega2-s.sympify(row["source_singlet_omega_squared"])) == 0
        substitution = dict(zip(P, [L, *[h*p for p in rate[1:, 0]]]))
        operator = clean(raw_hessian.subs(substitution))
        normalized_at = {u: L/c, r1: h*rate[1]/s.sqrt(2), r2: h*rate[2]/s.sqrt(2), r3: h*rate[3]/s.sqrt(2)}
        Gnum, Gden = clean(numerator.subs(normalized_at)), s.expand(denominator.subs(normalized_at))
        equal(operator*Gnum, Gden*P61); equal(Gnum*operator, Gden*P61)
        forced_num = clean(Gnum*f)
        equal(forced_num, decode(row["unreduced_original_Green_numerator_times_force"]))
        assert s.expand(Gden-s.sympify(row["unreduced_original_Green_denominator"])) == 0
        spatial_square = sum(normalized_at[r]**2 for r in [r1, r2, r3])
        singlet_factor = s.expand(2*(L/c)**2-2*spatial_square-2)
        doublet_factor = s.expand((singlet_factor+s.Rational(27, 50))**2+2*data["alpha"]**2*spatial_square)
        assert s.degree(doublet_factor, L) == 4
        assert s.expand(Gden-N*singlet_factor*doublet_factor) == 0
        equal(forced_num, doublet_factor*f)
        minimal_den = s.expand((L-frequency)*(L*L+omega2))
        minimal_num = clean(N*f)
        assert s.expand(minimal_den-s.sympify(row["actual_response_denominator"])) == 0
        equal(minimal_num, decode(row["actual_response_numerator"]))
        equal(forced_num*minimal_den, minimal_num*Gden*(L-frequency))
        assert all(not value.has(L) for value in minimal_num.todok().values())
        assert s.simplify(frequency*frequency+omega2) != 0

        # Independent physical state: [scalar amplitude, its time derivative,
        # forcing phase].  No source-clock rescaling enters this generator.
        B = s.Matrix([[0, 1, 0], [-omega2, 0, N], [0, 0, frequency]])
        O = s.SparseMatrix.hstack(f, s.zeros(70, 2))
        initial = s.Matrix([0, 0, 1])
        H2, H1, H0 = clean(operator.diff(L, 2)/2), clean(operator.diff(L).subs(L, 0)), clean(operator.subs(L, 0))
        equal(H2, s.eye(70)/N); equal(H1, s.zeros(70))
        equal(H2*O*B**2+H1*O*B+H0*O, f*s.Matrix([[0, 0, 1]]))
        equal(O*initial, s.zeros(70, 1)); equal(O*B*initial, s.zeros(70, 1))
        equal(O*B**2*initial, N*f)
        C, saved_O, saved_initial = map(decode, [row["companion_generator"], row["companion_output"], row["companion_initial"]])
        transport = s.Matrix([[N, 0, 0], [0, N, 0], [omega2, 0, 1]])
        assert transport.det() == N*N
        equal(B*transport, transport*C)
        equal(transport*saved_initial, initial); equal(O*transport, saved_O)
        equal(transport[-1:, :], decode(row["forcing_readout"]))
        for key, actual in [("initial_value", O*initial), ("initial_velocity", O*B*initial),
            ("initial_acceleration", O*B**2*initial), ("initial_distribution_delta_prime", H2*O*initial),
            ("initial_distribution_delta", H2*O*B*initial+H1*O*initial)]: equal(actual, decode(row[key]))
        # Constant numerator over a monic cubic is strictly proper: no hidden
        # polynomial delta contact survives the original Green cancellation.
        assert s.degree(minimal_den, L) == 3
        equal(Mreal*O, s.zeros(56, 3)); equal(Mfull*O, s.zeros(252, 3))
        equal(decode(row["original_M_phi_state_output"]), Mfull*saved_O)
        equal(decode(row["original_scalar_induced_primal252"]), s.zeros(252, 1))
        equal(decode(row["original_scalar_induced_independent_dual252"]), s.zeros(1, 252))
        poles = [s.sympify(value["pole"]) for value in row["actual_poles_and_nonzero_residues"]]
        assert len(poles) == 3 and len(set(poles)) == 3
        reconstructed = s.zeros(70, 1)
        for record in row["actual_poles_and_nonzero_residues"]:
            pole = s.sympify(record["pole"])
            assert s.simplify(minimal_den.subs(L, pole)) == 0
            derivative = s.simplify(s.diff(minimal_den, L).subs(L, pole))
            assert derivative != 0
            residue = decode(record["residue"])
            assert residue.todok()
            equal(derivative*residue, minimal_num)
            reconstructed += residue
            if h == 0 and s.simplify(pole-c) == 0:
                growing_residue = residue
                equal(residue, f/(4*N))
        equal(reconstructed, s.zeros(70, 1))
        original_doublet_omega2 = [s.simplify(N*N*((k.T*k)[0]-s.Rational(73, 50)
            +sign*data["alpha"]*s.sqrt((k.T*k)[0]))) for sign in [-1, 1]]
        assert all(s.simplify(a-s.sympify(b)) == 0 for a, b in zip(original_doublet_omega2, row["source_doublet_omega_squared"]))
        for value in [omega2, *original_doublet_omega2]: assert s.simplify(c*c+value).is_nonnegative
        if h == 0:
            assert frequency == 0 and s.simplify(omega2+c*c) == 0
            assert any(s.simplify(pole-c) == 0 for pole in poles)
            assert any(s.simplify(pole+c) == 0 for pole in poles)
        else:
            assert omega2 == s.Rational(783, 500)
            assert s.simplify(frequency*frequency+omega2) == s.Rational(27, 25)
        forces[h], denominators[h] = f, minimal_den
        reports.append({"harmonic": h, "force_nonzero_entries": len(f.todok()), "source_singlet_omega_squared": str(omega2),
            "original_two_sided_full70_Green_checked": True, "actual_doublet_factor_degree_cancelled": 4,
            "constant_nonzero_numerator_over_coprime_cubic": True,
            "independent_physical_ODE_and_state_transport_checked": True,
            "initial_value_velocity_and_all_distribution_contacts_zero": True,
            "all_three_actual_poles_have_nonzero_residues": True,
            "original_M_readback_zero_all_times": True})
        print("PASS independent scalar harmonic", h, "raw full70 ODE, strict cancellation, zero initial data and actual residues", flush=True)
    equal(forces[-2], forces[2].conjugate()); equal(forces[0], forces[0].conjugate())
    conjugate_den = s.expand(sum(s.conjugate(a)*L**p[0] for p, a in s.Poly(denominators[2], L).terms()))
    assert s.expand(denominators[-2]-conjugate_den) == 0
    assert growing_residue is not None and len(growing_residue.todok()) == 4
    equal(growing_residue, decode(candidate["zero_harmonic_growing_residue"]))
    assert s.simplify(s.sympify(candidate["zero_harmonic_growing_pole"])-c) == 0
    assert candidate["lifetime_status"] == "SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED"
    paths = [candidate_path, native_path, dynamic_path, feedback_path, occupied_path,
             BASE/"active-gauge/compute.py", BASE/"scalar-exchange/receipt.json",
             BASE/"full-phase/receipt.json", BASE/"matter-vertices/receipt.json"]
    output = {"verdict": "CERTIFIED_ACTUAL_SECOND_ORDER_SCALAR70_ZERO_PAST_RESPONSE",
        "root": ROOT_ID, "source_sha256": source.vertices["source_sha256"],
        "input_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        "original_mother_action_source_sha256": provenance["source_sha256"],
        "algorithm": "raw scalar density Hessian from actual metric/connection; original Yukawa M columns; original full70 two-sided Green; direct physical amplitude/velocity/forcing ODE and state transport; exact factor cancellation and pole residues",
        "candidate_module_imported": False,
        "actual_external_scalar_current_zero_scope": "pair0 Lambda4, all70 original scalar vertices on both sides, all16 actual feedback outputs and determinant vertex variation",
        "harmonics": reports, "source_clock": str(c), "safe_Laplace_half_plane": "Re(lam)>"+str(c),
        "zero_harmonic_positive_real_pole": str(c), "positive_pole_residue_nonzero_entries": len(growing_residue.todok()),
        "positive_pole_residue": "f0/(4*N), checked from the uncancelled original Green through exact polynomial identities",
        "zero_harmonic_time_response": "theta(t)*f0/(2*N)*(cosh(c*t)-1)",
        "growth_scope": "actual generated second-order homogeneous scalar background response; no composite pole, nonlinear long-time or decay-width identification",
        "lifetime_status": "SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED",
        "elapsed_seconds": round(time.monotonic()-started, 3)}
    (HERE/"independent_second_order_scalar.json").write_text(json.dumps(output, indent=2)+"\n")
    print("PASS independent actual second-order scalar certification", output["elapsed_seconds"], "seconds", flush=True)


if __name__ == "__main__":
    main()
