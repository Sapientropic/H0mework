#!/usr/bin/env python3
"""Independent raw-source finite-field reaction and canonical-current audit."""
from __future__ import annotations

from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import re
import sys
import time

import sympy as s

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(BASE))
import exact_readout as source

P = s.symbols("p0:4")
PAIRS = [(0, 1), (0, 2), (0, 3), (2, 3), (3, 1), (1, 2)]
ROOT_ID = ("positiveSmoothUnifiedSource; repaired Dirac-dual; SpinPair.actual; "
           "visit10/tick16/materialEntry -> tick17 unchanged")


def matrix(record):
    return s.SparseMatrix(*record["shape"], {(i, j): s.sympify(value)
        for i, j, value in record["entries"]})


def clean(value):
    return s.SparseMatrix(value).applyfunc(s.expand)


def scalar(value):
    return s.expand(s.radsimp(s.expand(value)))


def equal(left, right):
    residual = clean(left-right)
    if residual.todok():
        residual = residual.applyfunc(scalar)
    assert not residual.todok(), list(residual.todok())[:2]


def permutation_determinant(value):
    size = value.rows
    return scalar(sum((-1)**sum(order[i] > order[j] for i in range(size) for j in range(i+1, size))
        *s.prod(value[i, order[i]] for i in range(size)) for order in itertools.permutations(range(size))))


def cofactor_geometry(e):
    volume = permutation_determinant(e)
    adj = s.SparseMatrix(4, 4, {(mu, a): (-1)**(mu+a)*permutation_determinant(
        e.extract([i for i in range(4) if i != a], [j for j in range(4) if j != mu]))
        for mu in range(4) for a in range(4)})
    equal(e*adj, volume*s.eye(4))
    equal(adj*e, volume*s.eye(4))
    return volume, adj


class OriginalAction:
    def __init__(self, active, phase, vertices, vacuum, degrees, gamma):
        self.active, self.vertices = active, vertices
        self.N, self.omega = s.sympify(active["source_lapse"]), s.sympify(active["source_frequency"])
        self.gamma = gamma
        self.Gamma = [clean(s.kronecker_product(g, s.eye(63))) for g in gamma]
        eta = s.diag(-1, 1, 1, 1)
        for a, b in itertools.product(range(4), repeat=2):
            equal(gamma[a]*gamma[b]+gamma[b]*gamma[a], 2*eta[a, b]*s.eye(4))
        inside = [(degree, word) for degree in degrees for word in itertools.combinations(range(7), degree)]
        self.Q = s.diag(*[(1 if spin >= 2 else -1)+2*int(degree == 6)
            for spin in range(4) for degree, _ in inside])
        equal(self.Q, matrix(phase["phase_generator"]))
        self.S = clean(s.kronecker_product(gamma[0]*s.diag(-1, -1, 1, 1), s.eye(63)))
        generators = source.generators([(0, 1, 2), (3, 4)])
        assert [name for name, _, _ in generators] == active["native_P286_labels"]
        self.rho, rho4 = [], []
        for _, imaginary, original in generators:
            factor = s.I if imaginary else 1
            internal = s.diag(*[s.SparseMatrix(source.exterior_action(original, degree))*factor for degree in degrees])
            self.rho.append(clean(s.kronecker_product(s.eye(4), internal)))
            rho4.append(s.SparseMatrix(source.exterior_action(original, 4))*factor)
        self.spin = [clean(s.kronecker_product(gamma[a]*gamma[b]/2, s.eye(63))) for a, b in PAIRS]
        four_words = list(itertools.combinations(range(7), 4))
        def yukawa(values):
            _, _, original, _ = source.yukawa(values)
            internal = s.MutableSparseMatrix(63, 63, {})
            internal[:7, 7:28] = s.SparseMatrix(original)
            return clean(s.kronecker_product(s.diag(0, 0, 1, 1), internal))
        self.Y0 = yukawa(vacuum)
        equal(self.Y0, matrix(phase["original_Y"]))
        vacuum_column = s.Matrix([vacuum.get(word, 0) for word in four_words])
        elementary_yukawa = [yukawa(Counter({word: 1})) for word in four_words]
        self.scalar = {}
        for j, index in enumerate(active["J_independent_columns"]):
            orbit = rho4[index]*vacuum_column
            self.scalar[j] = clean(sum((orbit[i]*elementary_yukawa[i] for i in range(35)
                                       if orbit[i]), s.zeros(252)))
        self.raw_vertices = {entry["field"]: matrix(entry["operator"])
                             for entry in vertices["active_289_bosonic_source_operators"]}
        self.order = list(self.raw_vertices)

    def configuration(self, field):
        background = self.active["actual_background"]
        e = s.Matrix(background["coframe"]).applyfunc(s.sympify)
        A = s.Matrix(background["gauge_connection"]).applyfunc(s.sympify)
        O = s.Matrix(background["lowered_Lorentz_connection"]).applyfunc(s.sympify)
        Y = self.Y0.copy()
        for index in self.order:
            value = field[index]
            row = self.active["fields"][index]
            group, coord = row["group"], row["coordinate"]
            if group == "coframe": e[tuple(coord)] += value
            elif group == "gauge_A": A[tuple(coord)] += value
            elif group == "Lorentz": O[tuple(coord)] += value
            elif group == "scalar_J": Y += value*self.scalar[coord[0]]
            else: raise AssertionError(group)
        volume, adj = cofactor_geometry(e)
        assert volume != 0
        connections = [clean(sum((A[mu, a]*self.rho[a] for a in range(12)), s.zeros(252))
            +sum((O[mu, a]*self.spin[a] for a in range(6)), s.zeros(252))) for mu in range(4)]
        return {"e": e, "A": A, "O": O, "Y": clean(Y), "volume": volume, "adj": adj,
                "connections": connections, "inverse_e": (adj/volume).applyfunc(scalar)}

    def holonomic(self, data, momentum):
        contracted = [clean(s.I*sum((data["adj"][mu, a]*self.Gamma[a] for a in range(4)), s.zeros(252)))
                      for mu in range(4)]
        E = contracted[0]
        K = clean(sum((contracted[mu]*data["connections"][mu] for mu in range(4)), s.zeros(252))
            +sum((s.I*momentum[j]*contracted[j+1] for j in range(3)), s.zeros(252))
            +self.omega*sum((data["adj"][0, a]*self.Gamma[a]*self.Q for a in range(4)), s.zeros(252))
            +data["volume"]*data["Y"])
        E4 = clean(s.I*sum((data["adj"][0, a]*self.gamma[a] for a in range(4)), s.zeros(4)))
        norm = scalar(data["adj"][0, 0]**2-sum(data["adj"][0, j]**2 for j in range(1, 4)))
        assert norm != 0
        equal(E4*E4, norm*s.eye(4))
        inverse4 = E4.inv(method="DM").applyfunc(scalar)
        equal(E4*inverse4, s.eye(4)); equal(inverse4*E4, s.eye(4))
        equal(inverse4, (E4/norm).applyfunc(scalar))
        inverse = clean(s.kronecker_product(inverse4, s.eye(63)))
        equal(E, s.kronecker_product(E4, s.eye(63)))
        H = clean(-s.I*inverse*K)
        equal(-s.I*E*H+K, s.zeros(252))
        return {**data, "contracted": contracted, "E": E, "E4": E4, "inverse_E": inverse,
                "K": K, "H": H, "norm": norm, "momentum": momentum}

    def variation(self, data, index):
        row = self.active["fields"][index]
        group, coordinate = row["group"], row["coordinate"]
        dE = s.zeros(252)
        principal = [s.zeros(252) for _ in range(4)]
        if group == "gauge_A": dK = clean(data["contracted"][coordinate[0]]*self.rho[coordinate[1]])
        elif group == "Lorentz": dK = clean(data["contracted"][coordinate[0]]*self.spin[coordinate[1]])
        elif group == "scalar_J": dK = clean(data["volume"]*self.scalar[coordinate[0]])
        elif group == "coframe":
            elementary = s.zeros(4); elementary[tuple(coordinate)] = 1
            # Jacobi/inverse variation is independent of the candidate's
            # derivative of adjugate(e+tE) and determinant(e+tE).
            dvolume = scalar(data["volume"]*s.trace(data["inverse_e"]*elementary))
            dadj = clean(dvolume*data["inverse_e"]
                         -data["volume"]*data["inverse_e"]*elementary*data["inverse_e"])
            dcontracted = [clean(s.I*sum((dadj[mu, a]*self.Gamma[a] for a in range(4)), s.zeros(252)))
                           for mu in range(4)]
            dE = dcontracted[0]
            principal = dcontracted
            dK = clean(sum((dcontracted[mu]*data["connections"][mu] for mu in range(4)), s.zeros(252))
                +sum((s.I*data["momentum"][j]*dcontracted[j+1] for j in range(3)), s.zeros(252))
                +self.omega*sum((dadj[0, a]*self.Gamma[a]*self.Q for a in range(4)), s.zeros(252))
                +dvolume*data["Y"])
        else: raise AssertionError(group)
        dinverse = clean(-data["inverse_E"]*dE*data["inverse_E"])
        W = clean(-s.I*(dinverse*data["K"]+data["inverse_E"]*dK))
        equal(-s.I*data["E"]*W-s.I*dE*data["H"]+dK, s.zeros(252))
        return clean(dE), dK, W, principal


def main():
    started = time.monotonic()
    candidate_path = HERE/"spectral_splice.json"
    candidate = json.loads(candidate_path.read_text())
    assert candidate["root"] == ROOT_ID
    for name, digest in candidate["input_sha256"].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    paths = [BASE/name for name in ["active-gauge/receipt.json", "full-phase/receipt.json",
             "matter-vertices/receipt.json", "occupied-response/receipt.json"]]
    active, phase, vertices, occupied = [json.loads(path.read_text()) for path in paths]
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    assert candidate["source_sha256"] == phase["source_sha256"] == vertices["source_sha256"] == occupied["source_sha256"] == hashes
    gamma_path = ROOT/"Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean"
    text = gamma_path.read_text()
    gamma = []
    for name in ["Zero", "One", "Two", "Three"]:
        literal = re.search(r"def diracGamma"+name+r"\s*:.*?:=\s*!!\[(.*?)\]", text, re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(a.strip().replace("Complex.I", "I")) for a in row.split(",")]
                                    for row in literal.split(";")]))
    original = OriginalAction(active, phase, vertices, vacuum, degrees, gamma)
    dynamic_path = HERE/"dynamic.json"
    dynamic = json.loads(dynamic_path.read_text())
    assert dynamic["root"] == ROOT_ID and dynamic["source_sha256"] == hashes
    sample = next(row for row in dynamic["samples"] if row["name"] == "energy_transfer")
    field = clean(-matrix(sample["response"]["field289"]).applyfunc(s.re))
    equal(field, matrix(candidate["source_field"]))
    assert field.todok() and all(s.im(value) == 0 for value in field.todok().values())
    momentum = s.sqrt(2)*s.Matrix(list(map(s.sympify, sample["scaled_momenta"][0])))
    equal(momentum, matrix(candidate["physical_momentum"]))
    zero_config = original.configuration(s.zeros(289, 1))
    live_config = original.configuration(field)
    zero = original.holonomic(zero_config, momentum)
    live = original.holonomic(live_config, momentum)
    zero_background = original.holonomic(zero_config, s.zeros(3, 1))
    live_background = original.holonomic(live_config, s.zeros(3, 1))
    phase_p = dict(zip(P, [0, *[s.I*v for v in momentum]]))
    equal(zero["E"], original.N*matrix(phase["principal_coefficients"][0]))
    equal(zero["K"], original.N*matrix(vertices["full_stationary_Dirac_operator"]).subs(phase_p))
    equal(live["e"], matrix(candidate["coframe"]))
    assert scalar(live["volume"]-s.sympify(candidate["volume"])) == 0
    equal(live["E4"], matrix(candidate["temporal_principal4"]))
    assert scalar(live["E4"].det()-s.sympify(candidate["temporal_principal4_determinant"])) == 0
    equal(live["H"], matrix(candidate["finite_hamiltonian"]))
    delta = clean(live["H"]-zero["H"])
    equal(delta, matrix(candidate["finite_reaction"]))
    assert delta.todok()
    print("PASS independent Lean Clifford/exterior/Yukawa, cofactor geometry, direct double inverse and full252 finite Hamiltonian", flush=True)

    prepared = clean(matrix(occupied["occupied_frame"])*matrix(occupied["source_prepared"]))
    equal(prepared.H*prepared, s.ones(1))
    psi = 2*prepared
    chi = clean(s.sqrt(2)*psi.H*original.S)
    actual = candidate["actual_prepared_consumer"]
    equal(prepared, matrix(actual["prepared_unit"])); equal(psi, matrix(actual["psi"])); equal(chi, matrix(actual["chi"]))
    assert actual["physical_momentum"] == [0, 0, 0]
    equal(zero_background["H"]*psi, s.zeros(252, 1))
    assert scalar((chi*original.S*psi)[0]-4*s.sqrt(2)) == 0
    delta_background = clean(live_background["H"]-zero_background["H"])
    reaction = clean(delta_background*psi)
    equal(reaction, matrix(actual["reaction_on_actual_psi"]))
    assert len(reaction.todok()) == actual["nonzero_reaction_entries"] > 0
    p0, p1 = [clean(-s.I*chi*data["E"]) for data in [zero_background, live_background]]
    expected_feedback = {row["field"]: row for row in candidate["canonical_current_feedback"]}
    expected_actual = {row["field"]: row for row in actual["current_feedback"]}
    feedback, actual_feedback = [], []
    tangent = s.zeros(252)
    for index in original.order:
        dE, dK, W0, principal = original.variation(zero, index)
        vertex = original.raw_vertices[index]
        equal(dE, vertex.diff(P[0])); equal(dK, vertex.subs(phase_p))
        for mu in range(4):
            equal(principal[mu], vertex.diff(P[mu]))
        tangent += field[index]*W0
        _, _, W1, _ = original.variation(live, index)
        dE0, dK0, W0b, _ = original.variation(zero_background, index)
        dE1, dK1, W1b, _ = original.variation(live_background, index)
        equal(dK0, vertex.subs(dict(zip(P, [0]*4))))
        current0 = scalar((chi*(dE0*(-s.I*zero_background["H"])+dK0)*psi)[0])
        current1 = scalar((chi*(dE1*(-s.I*live_background["H"])+dK1)*psi)[0])
        assert scalar(current0-(-p0*W0b*psi)[0]) == 0
        assert scalar(current1-(-p1*W1b*psi)[0]) == 0
        # Differentiate -p W xi by the actual independent primal/dual flows.
        dp = clean(s.I*p1*delta_background)
        dpsi = clean(-s.I*delta_background*psi)
        current_derivative = scalar((-dp*W1b*psi-p1*W1b*dpsi)[0])
        current_change = scalar(current1-current0)
        real_change, real_derivative = scalar(s.re(current_change)), scalar(s.re(current_derivative))
        if real_change != 0 or real_derivative != 0:
            row = expected_actual[index]
            for key, value in [("original_action_current", current0), ("finite_action_current", current1),
                               ("real_current_change", real_change), ("real_matter_flow_derivative_change", real_derivative)]:
                assert scalar(value-s.sympify(row[key])) == 0, (index, key)
            actual_feedback.append(index)
        if active["fields"][index]["group"] == "gauge_A":
            derivative = clean(s.I*delta*W1-W1*s.I*delta)
            if derivative.todok():
                row = expected_feedback[index]
                first_index, first_value = next(iter(sorted(derivative.todok().items())))
                assert len(derivative.todok()) == row["nonzero_entries"]
                assert list(first_index) == row["first_entry"][:2]
                assert scalar(first_value-s.sympify(row["first_entry"][2])) == 0
                feedback.append(index)
    assert len(original.order) == 97
    assert set(feedback) == set(expected_feedback)
    assert set(actual_feedback) == set(expected_actual)
    assert len(feedback) == candidate["canonical_current_feedback_nonzero_fields"] > 0
    assert len(actual_feedback) == actual["nonzero_real_current_feedback_fields"] > 0
    beyond_linear = clean(delta-tangent)
    assert len(beyond_linear.todok()) == candidate["nonlinear_beyond_linear_tangent_nonzero_entries"] > 0
    assert candidate["full_interacting_generator"] == "SOURCE_NATIVE_SELFCONSISTENT_CURRENT_FIELD_EVOLUTION_REQUIRED"
    assert candidate["lifetime_status"] == "SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED"
    print("PASS independent all97 Jacobi holonomic tangents, canonical currents and actual prepared source feedback", flush=True)
    paths += [candidate_path, dynamic_path, gamma_path, BASE/"exact_readout.py"]
    output = {"verdict": "CERTIFIED_SOURCE_GENERATED_FINITE_FIELD_FULL252_REACTION",
        "root": ROOT_ID, "source_sha256": hashes,
        "input_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        "candidate_module_imported": False,
        "algorithm": "Lean Gamma literals; original exterior generators and Yukawa; permutation cofactors/determinant; Clifford E squared and direct4d matrix inverse; Jacobi adjugate differential; original holonomic coefficients; primal/dual product-rule current derivative",
        "source_field": "phase0 physical b=-Re(dynamic energy_transfer full289 response); its matter-coupled97 coordinate restriction supplies e,A,Omega,Y",
        "finite_temporal_two_sided_inverse_checked": True, "full252_finite_hamiltonian_checked": True,
        "original_action_tangents_checked": 97, "finite_canonical_current_identities_checked": 97,
        "original_holonomic_coefficient_slots_per_vertex": 5,
        "nonlinear_beyond_linear_tangent_entries": len(beyond_linear.todok()),
        "nonzero_matrix_feedback_fields": len(feedback),
        "prepared_zero_momentum_original_stationary_equation_checked": True,
        "prepared_source_amplitude": "4*sqrt(2)", "prepared_reaction_nonzero_entries": len(reaction.todok()),
        "prepared_real_current_feedback_fields": actual_feedback,
        "canonical_convention": "p_CAR=-i*zeta*E; j=-p_CAR*(dH/db)*xi; fixed-field derivative uses both independent primal and dual flows",
        "claim_scope": "source-generated local finite-field matter reaction; simultaneous constrained spacetime evolution and quantum spectral realization are separate producers",
        "full_interacting_generator": "SOURCE_NATIVE_SELFCONSISTENT_CURRENT_FIELD_EVOLUTION_REQUIRED",
        "lifetime_status": "SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED",
        "elapsed_seconds": round(time.monotonic()-started, 3)}
    (HERE/"independent_spectral_splice.json").write_text(json.dumps(output, indent=2)+"\n")
    print("PASS independent finite-field spectral splice certification", output["elapsed_seconds"], "seconds", flush=True)


if __name__ == "__main__":
    main()
