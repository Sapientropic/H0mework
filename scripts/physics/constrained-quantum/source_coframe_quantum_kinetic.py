#!/usr/bin/env python3
"""Original source coframe kinetic operator after its six primary rows.

Only the source coefficient matrices are fixed. All six free coframe momenta
are genuine CCR derivatives, and the complete independent-dual real currents
are the original504-branch CAR operators. The Lorentz contribution is consumed
inside the common Legendre formula once, before normal ordering.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_homogeneous_canonical_flow import SourceHomogeneousCanonicalFlow, SPATIAL, TIME
from source_lorentz_contact import clean, equal, encode
from source_common_hamiltonian import real
from real_scalar_car_source import realify, real_bilinear
from source_gauss_quantum_current import apply_current, normal_pair


def normalized(values):
    return {key: s.expand(value) for key, value in values.items() if s.expand(value) != 0}


def weighted(terms):
    result = defaultdict(lambda: s.S.Zero)
    for coefficient, vector in terms:
        if not coefficient:
            continue
        for target, value in vector.items():
            result[target] += coefficient*value
    return normalized(result)


def momentum(direction, vector):
    result = defaultdict(lambda: s.S.Zero)
    for (powers, fermions), value in vector.items():
        if powers[direction]:
            output = list(powers); output[direction] -= 1
            result[(tuple(output), fermions)] += -s.I*powers[direction]*value
    return normalized(result)


def position(direction, vector):
    result = defaultdict(lambda: s.S.Zero)
    for (powers, fermions), value in vector.items():
        output = list(powers); output[direction] += 1
        result[(tuple(output), fermions)] += value
    return normalized(result)


def current(matrix, vector):
    result = defaultdict(lambda: s.S.Zero)
    for (powers, fermions), value in vector.items():
        for target, coefficient in apply_current(matrix, fermions).items():
            result[(powers, target)] += value*coefficient
    return normalized(result)


def quartic(left, right, vector):
    result = defaultdict(lambda: s.S.Zero)
    for (powers, fermions), value in vector.items():
        for target, coefficient in normal_pair(left, right, fermions).items():
            result[(powers, target)] += value*coefficient
    return normalized(result)


def state_encode(vector):
    return [[list(powers), list(fermions), str(value)] for (powers, fermions), value in sorted(vector.items())]


class SourceCoframeQuantumKinetic:
    def __init__(self):
        self.flow = SourceHomogeneousCanonicalFlow()
        self.model = self.flow.coframe
        background = self.flow.common.scalar.exchange.active['actual_background']
        self.e = s.Matrix(background['coframe']).applyfunc(s.sympify)
        self.N = self.e[0, 0]
        self.geometry = self.model.geometry(self.e)
        self.Hinv = self.geometry['Lorentz_inverse']
        self.Q = self.geometry['velocity_inverse']
        self.Gt = self.geometry['G'][:, :16]
        spatial = self.e.copy(); spatial[:, 0] = s.zeros(4, 1)
        self.Z = s.Matrix.hstack(*[(T*spatial).reshape(16, 1) for T in self.model.lorentz.basis])
        matrix = self.Z.T[:, SPATIAL]
        minor = matrix[:, self.flow.primary_pivots]
        self.A, self.S = s.zeros(16, 6), s.zeros(16, 6)
        for a, j in enumerate(self.flow.primary_free):
            self.A[SPATIAL[j], a] = 1
        free_response = -minor.inv()*matrix[:, self.flow.primary_free]
        spin_response = -minor.inv()
        for a, j in enumerate(self.flow.primary_pivots):
            self.A[SPATIAL[j], :] = free_response[a, :]
            self.S[SPATIAL[j], :] = spin_response[a, :]
        self.time_reader = s.eye(24)[:6, :]
        self.L = clean(self.S*self.time_reader+self.Gt.T*self.Hinv)
        self.kinetic = clean(self.A.T*self.Q*self.A/2)
        self.mixed = clean(self.A.T*self.Q*self.L)
        self.weight = clean((self.L.T*self.Q*self.L+self.Hinv)/2)
        self.constant = 3*self.e.det()
        ports = self.model.lorentz.raw_matter_ports(self.e)
        self.E = clean(ports['E'])
        self.native4 = [clean(self.E.inv()*V) for V in ports['V']]
        self.quantum8 = [clean(s.diag(s.I*M, s.I*M.conjugate())) for M in self.native4]
        self.quantum = [clean(s.kronecker_product(M, s.eye(63))) for M in self.quantum8]
        self.mixed8 = [clean(sum((self.mixed[r, a]*self.quantum8[a] for a in range(24)), s.zeros(8))) for r in range(6)]
        self.mixed_quantum = [clean(s.kronecker_product(M, s.eye(63))) for M in self.mixed8]
        self.one_body8 = clean(sum((coefficient*self.quantum8[a]*self.quantum8[b]
                                   for (a, b), coefficient in self.weight.todok().items()), s.zeros(8)))
        self.one_body = clean(s.kronecker_product(self.one_body8, s.eye(63)))

    def shifted_momentum(self, index, state):
        return weighted([(self.A[index, r], momentum(r, state)) for r in range(6)]+
                        [(self.L[index, a], current(self.quantum[a], state)) for a in range(24)])

    def direct_action(self, state):
        terms = [(self.constant, state)]
        terms += [(coefficient/2, self.shifted_momentum(i, self.shifted_momentum(j, state)))
                  for (i, j), coefficient in self.Q.todok().items()]
        terms += [(coefficient/2, current(self.quantum[a], current(self.quantum[b], state)))
                  for (a, b), coefficient in self.Hinv.todok().items()]
        return weighted(terms)

    def ordered_terms(self, state):
        kinetic = weighted((coefficient, momentum(r, momentum(t, state)))
                           for (r, t), coefficient in self.kinetic.todok().items())
        mixed = weighted((1, momentum(r, current(self.mixed_quantum[r], state))) for r in range(6))
        normal = weighted((coefficient, quartic(self.quantum[a], self.quantum[b], state))
                          for (a, b), coefficient in self.weight.todok().items())
        one_body = current(self.one_body, state)
        return {'kinetic': kinetic, 'mixed': mixed, 'normal_quartic': normal,
                'one_body': one_body, 'constant': weighted([(self.constant, state)])}


def verify_source_graph(model):
    equal(model.Z.T*model.A, s.zeros(6))
    equal(model.Z.T*model.S, -s.eye(6))
    equal(model.A.extract(TIME, range(6)), s.zeros(4, 6))
    equal(model.S.extract(TIME, range(6)), s.zeros(4, 6))
    for a in range(6):
        equal(model.native4[a], model.model.lorentz.spin[a])
    kappas = s.Matrix(s.symbols('kappa0:6', real=True))
    formal_j = s.Matrix(s.symbols('source_current0:24', real=True))
    formal_Pi = model.A*kappas+model.S*formal_j[:6, :]
    free_coordinates = [SPATIAL[j] for j in model.flow.primary_free]
    dependent_coordinates = [SPATIAL[j] for j in model.flow.primary_pivots]
    coordinate_lift = s.eye(16)[:, free_coordinates]
    dependent_reader = s.eye(16)[dependent_coordinates, :]
    transverse = clean(dependent_reader*model.Z)
    assert transverse.det() != 0
    equal(model.A.T*coordinate_lift, s.eye(6))
    equal(model.S.T*coordinate_lift, s.zeros(6))
    dq = s.Matrix(s.symbols('d_free_coframe0:6', real=True))
    assert s.expand((formal_Pi.T*coordinate_lift*dq)[0]-(kappas.T*dq)[0]) == 0
    # The source-frozen canonical slice fixes the six dependent coordinates.
    # Its velocity equals the original quotient velocity after the uniquely
    # determined Lorentz correction that holds those coordinates fixed.
    slice_velocity_reader = clean(coordinate_lift.T-coordinate_lift.T*model.Z*
                                   transverse.inv()*dependent_reader)
    equal(slice_velocity_reader, model.A.T)
    shift = -model.Gt.T*model.Hinv*formal_j
    original = ((formal_Pi-shift).T*model.Q*(formal_Pi-shift))[0]/2+model.constant+(formal_j.T*model.Hinv*formal_j)[0]/2
    expanded = (kappas.T*model.kinetic*kappas)[0]+(kappas.T*model.mixed*formal_j)[0]+(formal_j.T*model.weight*formal_j)[0]+model.constant
    assert s.expand(original-expanded) == 0
    # Actual independent p and psi populate all252 entries. No adjoint graph
    # or occupied-mode restriction is used in the momentum-section consumer.
    psi = s.Matrix([s.Rational((3*j+2) % 11-5, 31)+s.I*s.Rational((5*j+1) % 13-6, 37) for j in range(252)])
    p = s.Matrix([[s.Rational((7*j+3) % 17-8, 41)+s.I*s.Rational((2*j+5) % 11-5, 43) for j in range(252)]])
    full_E = s.kronecker_product(model.E, s.eye(63))
    chi = clean(s.I*p*full_E.inv())
    ports = model.model.lorentz.raw_matter_ports(model.e)
    j = s.Matrix([real((chi*s.kronecker_product(V, s.eye(63))*psi)[0]) for V in ports['V']])
    native = s.Matrix([real((s.I*p*s.kronecker_product(M, s.eye(63))*psi)[0]) for M in model.native4])
    equal(j, native)
    Pi = model.flow.momentum_section(model.e, psi, p, kappas)['momentum']
    equal(Pi, model.A*kappas+model.S*j[:6, :])
    equal(model.model.constraints(model.e, Pi, s.zeros(48, 1), psi, chi), s.zeros(10, 1))
    raw_H = model.model.hamiltonian(model.e, Pi, s.zeros(48, 1), psi, chi, s.zeros(10, 1))
    actual = (kappas.T*model.kinetic*kappas)[0]+(kappas.T*model.mixed*j)[0]+(j.T*model.weight*j)[0]+model.constant
    assert s.simplify(raw_H-actual) == 0
    I = s.eye(4); C = s.Matrix.hstack(I, s.I*I)
    U = s.Matrix.vstack(C, C.conjugate())/s.sqrt(2)
    Pmap = s.Matrix.vstack(s.Matrix.hstack(s.zeros(4), -I), s.Matrix.hstack(-I, s.zeros(4)))
    for M, Q in zip(model.native4, model.quantum8):
        equal(Pmap*realify(M), real_bilinear(s.I*M))
        equal(U*(s.I*realify(M))*U.H, Q)
    normalized_primal = s.Matrix.vstack(psi, psi.conjugate())/s.sqrt(2)
    normalized_momentum = s.Matrix.hstack(p, -p.conjugate())/s.sqrt(2)
    for a in range(24):
        assert s.simplify((normalized_momentum*model.quantum[a]*normalized_primal)[0]-j[a]) == 0
    return {'six_free_momenta_symbolic': True, 'all24_original_real_currents_kept': True,
            'all252_primal_and_independent_p_entries_used': True,
            'original_Re_half_and_two_branch_signs': True,
            'all10_primary_rows_and_actual_momentum_section': True,
            'canonical_slice': {'fixed_dependent_coframe_coordinates': dependent_coordinates,
                'free_coframe_coordinates': free_coordinates,
                'original_Lorentz_transverse_minor': encode(transverse),
                'coordinate_lift': encode(coordinate_lift),
                'one_form_pullback': 'Pi_e^T de+Re(i p dpsi) pulls back to kappa^T dq_free+Re(i p dpsi), with the six dependent coframe coordinates fixed at their source values.',
                'spin_graph_one_form_term_zero': True,
                'Lorentz_corrected_velocity_reader_equals_A_transpose': True,
                'old_zero_Lorentz_representative_component_equality_claimed': False},
            'whole_original_coframe_Legendre_energy_matches_expansion': True,
            'actual_full24_current': encode(j), 'actual_independent_primal': encode(psi),
            'actual_independent_p': encode(p)}


def verify_quantum_consumer(model):
    equal(model.one_body8, -9*model.N*s.eye(8)/8)
    assert model.kinetic.det() != 0 and all(M.todok() for M in model.mixed8)
    assert any(clean(model.quantum8[a]*model.quantum8[b]-model.quantum8[b]*model.quantum8[a]).todok()
               for a in range(24) for b in range(24))
    inputs = [
        {((2, 1, 2, 1, 2, 1), (0, 315)): s.S.One},
        {((1, 2, 0, 1, 1, 0), (63, 126, 252)): s.S.One},
        {((0, 0, 0, 0, 0, 0), (0,)): s.S.One},
    ]
    records = []
    for state in inputs:
        direct = model.direct_action(state)
        terms = model.ordered_terms(state)
        ordered = weighted((1, value) for value in terms.values())
        assert weighted([(1, direct), (-1, ordered)]) == {}
        records.append({'input': state_encode(state), 'direct_original_square': state_encode(direct),
                        'ordered_terms': {key: state_encode(value) for key, value in terms.items()}})
    assert records[0]['ordered_terms']['kinetic'] and records[0]['ordered_terms']['mixed']
    assert records[0]['ordered_terms']['normal_quartic'] and records[0]['ordered_terms']['one_body']
    assert not records[2]['ordered_terms']['normal_quartic'] and records[2]['ordered_terms']['one_body']
    state = inputs[0]
    for r in range(6):
        for t in range(6):
            residual = weighted([(1, position(r, momentum(t, state))), (-1, momentum(t, position(r, state))),
                                 (-s.I if r == t else 0, state)])
            assert residual == {}
    # The original source momentum operator commutators give the generated
    # coframe velocity, including the nonzero matter-current cross term.
    velocities = []
    for r in range(6):
        actual = weighted([(s.I, model.direct_action(position(r, state))),
                           (-s.I, position(r, model.direct_action(state)))])
        expected = weighted([(2*model.kinetic[r, t], momentum(t, state)) for t in range(6)]+
                            [(1, current(model.mixed_quantum[r], state))])
        assert weighted([(1, actual), (-1, expected)]) == {}
        velocities.append(state_encode(actual))
    return {'actual_polynomial_CCR_tensor_CAR_readouts': records,
            'all36_position_momentum_CCR_checks': True,
            'six_generated_Heisenberg_coordinate_velocities': velocities,
            'bosonic_momenta_not_frozen': True,
            'free_momenta_mutually_commute_as_original_CCR_requires': True,
            'Lorentz_CAR_currents_noncommuting': True,
            'pure_quartic_single_particle_omission_control_nonzero': True}


def main():
    started = time.monotonic(); model = SourceCoframeQuantumKinetic()
    graph = verify_source_graph(model)
    print('PASS original full252 independent current, six primary graph and common coframe Legendre energy', flush=True)
    quantum = verify_quantum_consumer(model)
    print('PASS actual sixCCR tensor real504 CAR kinetic/cross/quartic/onebody and all coordinate velocities', flush=True)
    inputs = [HERE/name for name in ('source_coframe_quantum_kinetic.py', 'source_homogeneous_canonical_flow.py',
        'source_homogeneous_canonical_flow.json', 'independent_source_homogeneous_canonical_flow.json',
        'source_coframe_legendre.py', 'source_coframe_legendre.json', 'independent_source_coframe_legendre.json',
        'source_lorentz_contact.py', 'source_lorentz_contact.json', 'real_scalar_car_source.py',
        'real_scalar_car_source.json', 'source_gauss_quantum_current.py', 'source_gauss_quantum_current.json',
        'fock_raising_audit.json')]
    inputs += [ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/Fermion/NormalOrder.lean']
    body = {'root': ROOT_ID, 'source_sha256': model.flow.common.scalar.exchange.vertices['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs},
        'scope': 'ORIGINAL_SOURCE_COFRAME_COEFFICIENTS_WITH_SIX_CCR_MOMENTA_AND_FULL_REAL504_CAR',
        'source_coframe': encode(model.e), 'source_constant': str(model.constant),
        'six_free_momentum_coordinates': [SPATIAL[j] for j in model.flow.primary_free],
        'primary_graph': {'free_momentum_embedding': encode(model.A), 'spin_current_embedding': encode(model.S),
            'formula': 'Pi_e=A*kappa+S*j_time6, j_l=Re(i p E^-1 V_l psi)',
            'shifted_current_embedding': encode(model.L),
            'original_momentum_shift': 'b=-Gt^T H_Omega^-1 j; Pi_e-b=A*kappa+L*j'},
        'source_quantum_current_spin8_tensor_identity63': [encode(Q) for Q in model.quantum8],
        'ordered_Hamiltonian': {'formula': 'kappa^T K kappa + sum_r kappa_r tensor dGamma(C_r) + sum_lm W_lm normalProduct(Q_l,Q_m) + dGamma(M_one) +3 det(e_source)',
            'CCR_kinetic_weight': encode(model.kinetic), 'CCR_CAR_mixed_current_weight': encode(model.mixed),
            'mixed_spin8_matrices': [encode(C) for C in model.mixed8],
            'whole_current_square_weight': encode(model.weight), 'one_body_spin8_matrix': encode(model.one_body8),
            'one_body_full504': '-9*N/8 times identity504 = -27*sqrt(30)/200 times identity504',
            'universal_CAR_identity': 'SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize_normal_order'},
        'original_graph_consumer': graph, 'actual_operator_consumer': quantum,
        'common_component_domain': 'Polynomials in the six free coframe coordinates of the source Lorentz-transverse canonical slice tensor algebraic CAR(Fin504). Momentum is -i partial; source coefficient matrices are constant. Every finite operator composition stays in this domain and preserves CAR particle number.',
        'same_Lorentz_elimination_consumed_once': True,
        'additional_72_or_571_Contact_added': False,
        'general_live_coframe_coefficient_derivative_ordering_claimed': False,
        'full_joint_Hilbert_adjoint_evolution_or_spectrum_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_coframe_quantum_kinetic.json').write_text(json.dumps(body, separators=(',', ':'))+'\n')
    print('PASS source coframe quantum kinetic', body['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
