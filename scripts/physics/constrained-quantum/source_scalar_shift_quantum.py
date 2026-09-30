#!/usr/bin/env python3
"""Complete homogeneous scalar energy on the live source Gauss operator graph.

The original momentum is Rdual*pi+O*zeta, zeta=-D(phi)^(-T)*G. A live
coframe shift and the actual gauge/scalar CCR fields enter the same squared
momentum. The calculation retains both coefficient commutators and the
original spatial/potential multiplication term.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_gauss_live_ordering import SourceGaussLiveOrdering
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_lorentz_contact import clean, equal, encode
from source_scalar_legendre import dot


class SourceScalarShiftQuantum:
    def __init__(self):
        self.live = SourceGaussLiveOrdering()
        self.graph, self.c = self.live.graph, self.live.c
        self.gauge = self.graph.common.gauge
        saved = json.loads((HERE/'source_gauss_quantum_current.json').read_text())
        all_Q = [decode(item) for item in saved['real_CAR_current']['all12_matrices_in_complex_branch_basis']]
        self.Q = [all_Q[a] for a in self.c.broken_columns]
        self.T = [s.diag(self.live.compressed[j], *[self.gauge.ad(s.eye(12)[:, a])]*3)
                  for j, a in enumerate(self.c.broken_columns)]
        self.embedding = self.graph.dual_R.row_join(s.zeros(70, 36))
        self.peripheral_inverse_gram = clean((self.graph.R.T*self.graph.R).inv())

    def coefficients(self, e, x, spatial_A):
        data = self.live.coefficients(e, x)
        phi, F = data['phi'], data['F']
        h, volume = self.c.metric_density(e)
        RA = [clean(sum((spatial_A[i, a]*self.c.rho[a] for a in range(12)), s.zeros(70))) for i in range(3)]
        U = [clean(R*phi) for R in RA]
        shift = clean(sum((h[0, i+1]*U[i] for i in range(3)), s.zeros(70, 1)))
        shift_derivative = s.zeros(70, 97)
        shift_derivative[:, :61] = sum((h[0, i+1]*RA[i]*self.graph.R for i in range(3)), s.zeros(70, 61))
        for i in range(3):
            for a in range(12):
                shift_derivative[:, 61+12*i+a] = h[0, i+1]*self.c.rho[a]*phi
        y = x.col_join(spatial_A.reshape(36, 1))
        vectors = clean(s.Matrix.vstack(*[(T*y).T for T in self.T]))
        t = clean(self.graph.dual_R.T*shift)
        n = clean(self.graph.O.T*shift)
        n_derivative = clean(self.graph.O.T*shift_derivative)
        w = clean(F.T*n)
        div_t = s.trace(self.graph.dual_R.T*shift_derivative[:, :61])
        assert div_t == 0
        commutator = s.expand(-s.I*sum(F[a, b]*(n_derivative[a, :]*vectors[b, :].T)[0]
                                       for a in range(9) for b in range(9))/(2*h[0, 0]))
        spatial_potential = s.expand(-sum(h[i+1, j+1]*dot(U[i], U[j])/2
                                         for i in range(3) for j in range(3))+
                                    volume*dot(phi-self.c.vacuum, phi-self.c.vacuum))
        OF = clean(self.graph.O*F)
        return {**data, 'metric': h, 'spatial_A': spatial_A, 'vectors': vectors,
                'shift': shift, 'shift_derivative': clean(shift_derivative),
                'peripheral_shift': t, 'normal_shift': n, 'current_shift': w,
                'shift_commutator': s.factor(commutator), 'spatial_potential': s.factor(spatial_potential),
                'normal_embedding': OF, 'momentum_vectors': clean(self.embedding-OF*vectors)}

    def directional_momentum(self, data, direction):
        dD = clean(self.c.select.T*self.c.consistency_matrix(self.graph.R*direction[:61, :])*self.c.select)
        dF = clean(-data['F']*dD.T*data['F'])
        dOF = clean(self.graph.O*dF)
        dV = clean(s.Matrix.vstack(*[(T*direction).T for T in self.T]))
        return {'normal_embedding': dOF,
                'momentum_vectors': clean(-dOF*data['vectors']-data['normal_embedding']*dV)}

    def current(self, coefficients, state):
        return weighted_sum((coefficient, apply_superposition(self.Q[a], state))
                            for a, coefficient in enumerate(coefficients) if coefficient)

    def wavepacket_consumer(self, data, state, gradient, Hessian):
        original = {tuple(state): s.S.One}
        V, OF = data['vectors'], data['normal_embedding']
        J = [apply_superposition(Q, original) for Q in self.Q]
        G = [weighted_sum([(-s.I*(V[a, :]*gradient)[0], original), (1, J[a])]) for a in range(9)]
        GG = {}
        for a in range(9):
            for b in range(9):
                scalar_second = -((self.T[b]*V[a, :].T).T*gradient)[0]-(V[b, :]*Hessian*V[a, :].T)[0]
                GG[a, b] = weighted_sum([(scalar_second, original),
                    (-s.I*(V[a, :]*gradient)[0], J[b]),
                    (-s.I*(V[b, :]*gradient)[0], J[a]),
                    (1, apply_superposition(self.Q[a], J[b]))])
        raw = []
        for j in range(70):
            a = data['momentum_vectors'][j, :].T
            m = -OF[j, :]
            b = data['shift'][j]
            derivative = self.directional_momentum(data, a)
            da = derivative['momentum_vectors'][j, :].T
            dm = -derivative['normal_embedding'][j, :]
            db = (data['shift_derivative'][j, :]*a)[0]
            inner = weighted_sum([(-s.I*(a.T*gradient)[0]-b, original), (1, self.current(m, original))])
            dinner = weighted_sum([
                (-s.I*((da.T*gradient)[0]+(a.T*Hessian*a)[0])-db-b*(a.T*gradient)[0], original),
                (1, self.current(dm, original)), ((a.T*gradient)[0], self.current(m, original))])
            raw.append(weighted_sum([(-s.I, dinner), (1, self.current(m, inner)), (-b, inner)]))
        h00 = data['h00']
        kinetic = weighted_sum((1/(2*h00), value) for value in raw)
        free = weighted_sum([(-s.trace(self.peripheral_inverse_gram*Hessian[:61, :61])/(2*h00), original)])
        normal = weighted_sum([(value, GG[a, b]) for (a, b), value in data['quadratic'].todok().items()]+
                              [(data['linear'][a], G[a]) for a in range(9)])
        peripheral_shift = weighted_sum([(s.I*(data['peripheral_shift'].T*gradient[:61, :])[0]/h00, original)])
        normal_shift = weighted_sum([(data['shift_commutator'], original)]+
            [(data['current_shift'][a]/h00, G[a]) for a in range(9)])
        shift_square = weighted_sum([(dot(data['shift'], data['shift'])/(2*h00), original)])
        shift = weighted_sum([(1, peripheral_shift), (1, normal_shift), (1, shift_square)])
        expanded = weighted_sum([(1, free), (1, normal), (1, shift)])
        assert weighted_sum([(1, kinetic), (-1, expanded)]) == {}
        assert shift and normal_shift
        potential = weighted_sum([(data['spatial_potential'], original)])
        return {'original_squared_momentum': kinetic, 'peripheral_kinetic': free,
                'normal_kinetic': normal, 'shift': shift, 'spatial_potential': potential,
                'peripheral_shift': peripheral_shift, 'normal_shift': normal_shift,
                'full_scalar_bulk': weighted_sum([(1, kinetic), (1, potential)])}


def main():
    started = time.monotonic()
    model = SourceScalarShiftQuantum()
    active = model.graph.common.scalar.exchange.active['actual_background']
    e = s.Matrix(active['coframe']).applyfunc(s.sympify)
    e[1, 0] = e[0, 0]/5
    A = s.Matrix(active['gauge_connection']).applyfunc(s.sympify)
    A[1, model.c.broken_columns[0]] += s.Rational(1, 17)
    x = s.Matrix([s.Rational((3*j+1) % 7-3, 100) for j in range(61)])
    data = model.coefficients(e, x, A[1:, :])
    assert data['metric'][0, 1] != 0 and data['shift'].todok() and data['current_shift'].todok()
    ell = s.Matrix([s.Rational((j % 11)+1, 67) for j in range(97)])
    m = s.Matrix([s.Rational((j % 7)-3, 53) for j in range(97)])
    wave = model.wavepacket_consumer(data, (5, 258), s.I*ell, m*m.T-s.eye(97))
    print('PASS complete original70 shifted momentum square on actual97-variable CCR tensor real-CAR wavepacket', flush=True)
    # Read the identical classical scalar density with independent canonical
    # tangent and normal momenta; no proposed energy is an input.
    pi = s.Matrix([s.Rational((j % 5)-2, 31) for j in range(61)])
    zeta = s.Matrix([s.Rational(j-4, 29) for j in range(9)])
    Pi = model.graph.dual_R*pi+model.graph.O*zeta
    A[0, :] = s.zeros(1, 12)
    original = model.graph.common.scalar.hamiltonian(e, data['phi'], Pi, [s.zeros(70, 1)]*3, A)
    reconstructed = dot(Pi-data['shift'], Pi-data['shift'])/(2*data['h00'])+data['spatial_potential']
    assert s.simplify(original-reconstructed) == 0
    coordinates = model.c.select.row_join(model.c.stabilizer).inv()[:9, :]
    expected_w = sum((data['metric'][0, i+1]*coordinates*A[i+1, :].T for i in range(3)), s.zeros(9, 1))
    equal(data['current_shift'], expected_w)
    print('PASS original scalar Legendre readback, source normal shift cancellation and retained live ordering', flush=True)
    inputs = [HERE/name for name in ('source_scalar_shift_quantum.py', 'source_gauss_live_ordering.py',
        'source_gauss_live_ordering.json', 'independent_source_gauss_live_ordering.json',
        'source_gauss_quantum_current.py', 'source_gauss_quantum_current.json',
        'source_scalar_gauss_reduction.py', 'source_scalar_legendre.py', 'source_gauge_legendre.py')]
    result = {'root': ROOT_ID, 'source_sha256': model.graph.common.scalar.exchange.vertices['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
        'scope': 'COMPLETE_HOMOGENEOUS_SCALAR_SHIFTED_MOMENTUM_ENERGY_ON_LIVE_GAUSS_OPERATOR_GRAPH',
        'original_scalar_energy': '(Rdual*pi+O*zeta-b)^T(Rdual*pi+O*zeta-b)/(2h00)-sum_ij h_ij U_i.U_j/2+abs(det e)*V(phi)',
        'normal_equation': 'zeta=-D(phi)^(-T) G; broken A0 multiplies the original common Gauss constraint and is eliminated only in that common bulk Hamiltonian',
        'actual_coframe': encode(e), 'actual_scalar_coordinates': encode(x),
        'actual_spatial_gauge': encode(A[1:, :]), 'metric_density': encode(data['metric']),
        'original_shift': encode(data['shift']), 'normal_current_shift': encode(data['current_shift']),
        'normal_current_shift_scalar_dependence_cancels': True,
        'peripheral_shift_divergence_zero': True, 'normal_shift_commutator': str(data['shift_commutator']),
        'expanded_shift': 'i*t.partial_x/h00 + w.G/h00 -i*sum_ab F_ab*(V_b.partial n_a)/(2h00)+b.b/(2h00)',
        'wavepacket': {'dimensions': 97, 'scalar_dimensions': 61, 'gauge_dimensions': 36,
            'function': 'eta(y)*exp(-|y|^2/2)*(1+i ell.y+(m.y)^2/2)|5,258>, y=(x,A_i)-(x0,A_i0); eta smooth compactly supported inside det D!=0 and equal1 near0',
            'ell_j': '((j mod 11)+1)/67', 'm_j': '((j mod 7)-3)/53',
            'components': {key: encode_state(value) for key, value in wave.items()},
            'nested70_square_equals_complete_expansion': True, 'omit_shift_defect_nonzero': True,
            'omit_normal_shift_defect_nonzero': True},
        'common_component_domain': 'C_c^infinity(U_scalar times R^36_gauge) tensor finite CAR(Fin504), fixed source-admissible coframe e; every finite differential action preserves the same compact support and particle number',
        'original_scalar_density_readback': True,
        'public_API': 'SourceScalarShiftQuantum.{coefficients,directional_momentum,wavepacket_consumer}',
        'coframe_quantum_field_or_full_joint_evolution_installed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_scalar_shift_quantum.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')


if __name__ == '__main__':
    main()
