#!/usr/bin/env python3
"""One local ordered Hamiltonian on the source coframe/scalar/gauge/CAR domain.

All coefficients act on the same 103 configuration coordinates. This is the
homogeneous bulk operator with the original time coframe fixed as a parameter,
after the six Spin-primary and nine scalar Gauss momentum substitutions.
The remaining temporal and stabilizer constraints are not replaced by a
Hilbert-space completion or by an assumed physical state.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_coframe_live_ordering import SourceCoframeLiveOrdering, FREE, full, verify_jet_action
from source_scalar_shift_quantum import SourceScalarShiftQuantum
from source_gauge_quantum_energy import SourceGaugeQuantumEnergy
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_lorentz_contact import clean, equal, encode, GAMMA
from source_common_hamiltonian import real
from source_scalar_legendre import dot


class SourceJointLocalQuantum:
    def __init__(self):
        self.coframe = SourceCoframeLiveOrdering()
        self.scalar = SourceScalarShiftQuantum()
        self.gauge = SourceGaugeQuantumEnergy()
        self.common = self.scalar.graph.common

    def coefficients(self, q, x, spatial_A):
        e = self.coframe.e.subs(dict(zip(self.coframe.q, q)))
        cf = self.coframe.coefficients(q)
        scalar = self.scalar.coefficients(e, x, spatial_A)
        gauge = self.gauge.coefficients(e)
        substitutions = dict(zip(self.gauge.coordinates, spatial_A.reshape(36, 1)))
        gauge = {key: clean(value.subs(substitutions)) if isinstance(value, s.MatrixBase)
                 else s.expand(value.subs(substitutions)) for key, value in gauge.items()}
        A = s.zeros(4, 12); A[1:, :] = spatial_A
        matter = self.common.matter_data(e, scalar['phi'], A)
        H = clean(-s.I*matter['inverse_E']*matter['lower_without_Lorentz'])
        Q = clean(s.diag(H, -H.conjugate()))
        return {'e': e, 'coframe': cf, 'scalar': scalar, 'gauge': gauge,
                'matter': matter, 'matter_H': H, 'matter_CAR': Q, 'connection': A}

    def scalar_action(self, data, state, gradient, Hessian):
        m, d = self.scalar, data['scalar']
        unit = {tuple(state): s.S.One}
        terms = []
        for j in range(70):
            a, n = d['momentum_vectors'][j, :].T, -d['normal_embedding'][j, :]
            b = d['shift'][j]
            derivative = m.directional_momentum(d, a)
            da, dn = derivative['momentum_vectors'][j, :].T, -derivative['normal_embedding'][j, :]
            db = (d['shift_derivative'][j, :]*a)[0]
            inner = weighted_sum([(-s.I*(a.T*gradient)[0]-b, unit), (1, m.current(n, unit))])
            dinner = weighted_sum([(-s.I*((da.T*gradient)[0]+(a.T*Hessian*a)[0])-db-b*(a.T*gradient)[0], unit),
                                    (1, m.current(dn, unit)), ((a.T*gradient)[0], m.current(n, unit))])
            terms.extend([(-s.I/(2*d['h00']), dinner), (1/(2*d['h00']), m.current(n, inner)),
                          (-b/(2*d['h00']), inner)])
        terms.append((d['spatial_potential'], unit))
        return weighted_sum(terms)

    def action(self, data, state, gradient, Hessian):
        """Value on a unit-valued smooth germ; all 103 first/second jets supplied."""
        assert gradient.shape == (103, 1) and Hessian.shape == (103, 103)
        coframe = verify_jet_action(data['coframe'], state, 1, gradient[:6, :], Hessian[:6, :6])
        cf_action = {tuple(word): s.sympify(value) for word, value in coframe['raw_nested_square']}
        scalar = self.scalar_action(data, state, gradient[6:, :], Hessian[6:, 6:])
        d = data['gauge']; g, h = gradient[67:, :], Hessian[67:, 67:]
        W, C, dC = d['weight'], d['momentum_shift'], d['shift_derivative']
        gauge_value = s.S.Zero
        for (i, j), weight in W.todok().items():
            inner = -s.I*g[j]-C[j]
            dinner = -s.I*h[j, i]-dC[j, i]-C[j]*g[i]
            gauge_value += weight*(-s.I*dinner-C[i]*inner)/2
        gauge = {tuple(state): s.expand(gauge_value+d['magnetic_potential'])}
        matter = apply_superposition(data['matter_CAR'], {tuple(state): s.S.One})
        components = {'coframe': cf_action, 'scalar': scalar, 'gauge': gauge, 'matter_without_Lorentz': matter}
        return components, weighted_sum((1, value) for value in components.values())


def classical_readback(model, data):
    graph = model.scalar.graph
    e, A = data['e'], data['connection']
    psi = s.Matrix([s.Rational((3*j+2) % 11-5, 31)+s.I*s.Rational((5*j+1) % 13-6, 37) for j in range(252)])
    p = s.Matrix([[s.Rational((7*j+3) % 17-8, 41)+s.I*s.Rational((2*j+5) % 11-5, 43) for j in range(252)]])
    kappa = s.Matrix([s.Rational(j-2, 23) for j in range(6)])
    pi = s.Matrix([s.Rational((j % 5)-2, 31) for j in range(61)])
    PiA = s.Matrix(3, 12, lambda i, a: s.Rational((i+3*a) % 11-5, 31))
    x = graph.dual_R.T*(data['scalar']['phi']-graph.constraints.vacuum)
    scalar = graph.embed(x, pi, A, PiA, [s.zeros(3, 12)]*3, psi, p)
    ports = model.coframe.model.lorentz.raw_matter_ports(e)
    chi = clean(s.I*p*data['matter']['inverse_E'])
    j = s.Matrix([real((chi*full(s.diag(V, s.zeros(4)))[:252, :252]*psi)[0]) for V in ports['V']])
    cf = data['coframe']
    Pi_e = cf['A']*kappa+cf['S']*j[:6, :]
    original = model.common.hamiltonian(e, Pi_e, s.zeros(48, 1), scalar['phi'], scalar['Pi_phi'],
        [s.zeros(70, 1)]*3, A, PiA, s.zeros(3, 48), psi, p, [s.zeros(252, 1)]*3, s.zeros(10, 1))
    cf_energy = (kappa.T*cf['K']*kappa)[0]+(kappa.T*(cf['A'].T*cf['Q']*cf['L'])*j)[0]+(j.T*cf['W']*j)[0]+cf['constant']
    sc = data['scalar']
    sc_energy = dot(scalar['Pi_phi']-sc['shift'], scalar['Pi_phi']-sc['shift'])/(2*sc['h00'])+sc['spatial_potential']
    g = data['gauge']; shift = PiA.reshape(36, 1)-g['momentum_shift']
    g_energy = (shift.T*g['weight']*shift)[0]/2+g['magnetic_potential']
    m_energy = real((p*data['matter_H']*psi)[0])
    expected = {'coframe_Lorentz_matter': cf_energy, 'scalar': sc_energy, 'gauge': g_energy, 'matter_without_Lorentz': m_energy}
    for key, value in expected.items():
        assert s.simplify(original['components'][key]-value) == 0
    equal(original['coframe_primary'], s.zeros(10, 1))
    equal(graph.select.T*scalar['Gauss'], s.zeros(9, 1))
    a = s.Matrix.vstack(psi, psi.conjugate())/s.sqrt(2)
    b = s.Matrix.hstack(p, -p.conjugate())/s.sqrt(2)
    assert s.simplify((b*data['matter_CAR']*a)[0]-m_energy) == 0
    return {'all4_original_component_values_match': True, 'all10_coframe_primary_and9_broken_Gauss_rows_zero': True,
            'original_independent_real_matter_normalization_checked': True,
            'full252_primal_and_independent_momentum_used': True,
            'unreduced_stabilizer_Gauss': encode(graph.stabilizer.T*scalar['Gauss'])}


def main():
    started = time.monotonic(); model = SourceJointLocalQuantum()
    q = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8), s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    x = s.Matrix([s.Rational((3*j+1) % 7-3, 100) for j in range(61)])
    active = model.scalar.graph.common.scalar.exchange.active['actual_background']
    A = s.Matrix(active['gauge_connection']).applyfunc(s.sympify)[1:, :]
    A[0, 2] += s.Rational(1, 17); A[1, 7] += s.Rational(1, 19)
    data = model.coefficients(q, x, A)
    original = classical_readback(model, data)
    print('PASS common original bulk Hamiltonian, primary/Gauss graph and full504 matter normalization', flush=True)
    ell = s.Matrix([s.Rational(j % 11+1, 67) for j in range(103)])
    m = s.Matrix([s.Rational(j % 7-3, 53) for j in range(103)])
    gradient, Hessian = s.I*ell, m*m.T-s.eye(103)
    components, total = model.action(data, (5, 258), gradient, Hessian)
    assert all(components.values())
    assert total
    # The Gauss-square has real scalar/gauge mixed derivatives on this common
    # domain. Removing those Hessian entries changes the actual total action.
    separate = Hessian.copy(); separate[6:67, 67:] = s.zeros(61, 36); separate[67:, 6:67] = s.zeros(36, 61)
    separated_scalar = model.scalar_action(data, (5, 258), gradient[6:, :], separate[6:, 6:])
    mixed_defect = weighted_sum([(1, components['scalar']), (-1, separated_scalar)])
    assert mixed_defect
    # Scalar position changes the original non-Lorentz matter generator.
    # Every direction uses the original 70 Yukawa matrices and source R61.
    Yukawa = model.common.yukawa_basis
    dH = []
    for r in range(61):
        dY = clean(sum(((model.scalar.graph.R[j, r]+s.I*model.scalar.graph.R[j+35, r])*Yukawa[j]
                        for j in range(35)), s.zeros(252)))
        M = clean(-s.I*data['e'].det()*data['matter']['inverse_E']*dY)
        dH.append(clean(s.diag(M, -M.conjugate())))
    force_pairs = [(r, column) for r, M in enumerate(dH) for column in range(504) if M[:, column].todok()]
    assert force_pairs
    r, column = force_pairs[0]
    force = apply_superposition(-dH[r], {(column,): s.S.One})
    assert force
    print('PASS one103-coordinate Hamiltonian action, mixed scalar/gauge jet and original Yukawa force', flush=True)
    inputs = [HERE/name for name in ('source_joint_local_quantum.py', 'source_coframe_live_ordering.py',
        'source_coframe_live_ordering.json', 'source_scalar_shift_quantum.py', 'source_scalar_shift_quantum.json',
        'source_gauge_quantum_energy.py', 'source_gauge_quantum_energy.json', 'source_common_hamiltonian.py',
        'source_common_hamiltonian.json', 'source_scalar_gauss_reduction.py', 'source_gauss_live_ordering.py')]
    result = {'root': ROOT_ID, 'source_sha256': model.coframe.source['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
        'scope': 'COMMON_ORDERED_HOMOGENEOUS_LOCAL_HAMILTONIAN_ON_ONE103_COORDINATE_CCR_CAR_DOMAIN',
        'coordinates': {'coframe': 6, 'scalar': 61, 'gauge': 36, 'original_real_CAR': 504},
        'domain': 'Cc_infinity(U_q times U_x times R36) tensor algebraic CAR(Fin504); U_q has positive q0,q2,q5; U_x is the original det D9!=0 source chart',
        'domain_invariance': 'Each original ordered component is a differential operator of order at most2 with smooth rational coefficients on this same open chart and finite degree number-preserving CAR words. Finite sums and compositions preserve compact support and each finite particle sector.',
        'Hamiltonian': 'H_coframe_live+H_scalar_Gauss+H_native_gauge+dGamma(diag(Hm,-conjugate(Hm))); Hm=-i E^-1 K_without_Lorentz, with homogeneous spatial derivatives and A0=0 in the common Gauss bulk',
        'original_classical_readback': original,
        'configuration': {'coframe': encode(data['e']), 'scalar': encode(x), 'gauge': encode(A)},
        'actual_nonseparable_103_wavepacket': {'state': [5, 258], 'gradient': 'i*((j mod11)+1)/67',
            'Hessian': 'm*m^T-I103, m_j=((j mod7)-3)/53; realized by a compact smooth cutoff equal1 near the base configuration',
            'components': {key: encode_state(value) for key, value in components.items()}, 'joint_action': encode_state(total),
            'dropping_scalar_gauge_cross_jets_defect': encode_state(mixed_defect)},
        'matter_Yukawa_force': {'all61_derivatives_from_original70_vertices': True, 'direction': r, 'input': [column],
            'i_H_commutator_scalar_momentum': encode_state(force)},
        'remaining_quantum_constraints': 'four temporal coframe equations and three stabilizer Gauss rows; no physical-state solution has been assumed',
        'coframe_time_column_fixed_at_original_source_value': True,
        'spatial_QFT_or_Hilbert_evolution_spectral_measure_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_joint_local_quantum.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS common ordered local quantum Hamiltonian', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
