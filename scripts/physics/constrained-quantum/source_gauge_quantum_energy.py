#!/usr/bin/env python3
"""Original native12 homogeneous gauge Hamiltonian on its36 canonical fields.

The original Hodge, native pairing, magnetic curvature and live coframe
shift generate the complete ordered momentum square. The full A0 term and
its spatial boundary remain a common-Gauss responsibility.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_gauge_legendre import SourceGaugeLegendre, contraction
from source_lorentz_contact import clean, equal, encode


class SourceGaugeQuantumEnergy:
    def __init__(self):
        self.source = SourceGaugeLegendre()
        self.coordinates = s.Matrix(s.symbols('A0:36', real=True))
        self.spatial_A = self.coordinates.reshape(3, 12)
        self.magnetic = s.Matrix.vstack(*[self.source.bracket(self.spatial_A[i, :], self.spatial_A[j, :]).T
                                          for i, j in ((1, 2), (2, 0), (0, 1))])
        self.magnetic_derivative = self.magnetic.reshape(36, 1).jacobian(self.coordinates)
        for i in range(3):
            for j in range(3):
                assert s.expand(sum(self.magnetic_derivative[12*j+a, 12*i+a] for a in range(12))) == 0

    def coefficients(self, e):
        raw = self.source.constitutive(e)
        W = clean(s.kronecker_product(raw['electric_inverse'], self.source.gram_inverse))
        C = clean(raw['mixed']*self.magnetic*self.source.gram).reshape(36, 1)
        dC = C.jacobian(self.coordinates)
        zero_order_commutator = s.expand(s.I*s.trace(W*dC)/2)
        assert zero_order_commutator == 0
        potential = s.expand(-contraction(self.magnetic, raw['magnetic']*self.magnetic*self.source.gram)/2)
        return {'weight': W, 'momentum_shift': C, 'shift_derivative': dC,
                'magnetic_potential': potential, 'shifted_momentum_commutator': clean(s.I*(dC.T-dC)),
                'derivative_ordering_constant': zero_order_commutator}

    def apply_at(self, e, A, gradient, Hessian):
        data = self.coefficients(e)
        substitutions = dict(zip(self.coordinates, A.reshape(36, 1)))
        W = data['weight']
        C = clean(data['momentum_shift'].subs(substitutions))
        dC = clean(data['shift_derivative'].subs(substitutions))
        potential = s.expand(data['magnetic_potential'].subs(substitutions))
        # Direct nested action of (p_i-C_i)(p_j-C_j) on the actual jet.
        nested = s.S.Zero
        for (i, j), coefficient in W.todok().items():
            inner = -s.I*gradient[j]-C[j]
            derivative_inner = -s.I*Hessian[j, i]-dC[j, i]-C[j]*gradient[i]
            nested += coefficient*(-s.I*derivative_inner-C[i]*inner)/2
        expanded = (-s.trace(W*Hessian)/2+s.I*(C.T*W*gradient)[0]+
                    (C.T*W*C)[0]/2+data['derivative_ordering_constant'])
        assert s.expand(nested-expanded) == 0
        omitted = s.expand(s.I*(C.T*W*gradient)[0]+(C.T*W*C)[0]/2)
        assert omitted != 0
        return {'kinetic': s.expand(nested), 'magnetic': potential,
                'whole': s.expand(nested+potential), 'omit_shift_defect': omitted,
                'shift': C, 'commutator': clean(data['shifted_momentum_commutator'].subs(substitutions))}


def main():
    started = time.monotonic()
    model = SourceGaugeQuantumEnergy()
    active = json.loads((BASE/'active-gauge/receipt.json').read_text())['actual_background']
    e0 = s.Matrix(active['coframe']).applyfunc(s.sympify)
    e = e0.copy(); e[1, 0] = e0[0, 0]/5
    A = s.Matrix(active['gauge_connection']).applyfunc(s.sympify)[1:, :]
    A[0, 2] += s.Rational(1, 17); A[1, 7] += s.Rational(1, 19)
    ell = s.Matrix([s.Rational(j+1, 41) for j in range(36)])
    m = s.Matrix([s.Rational((j % 7)-3, 43) for j in range(36)])
    actual = model.apply_at(e, A, s.I*ell, m*m.T-s.eye(36))
    assert actual['shift'].todok() and actual['commutator'].todok()
    print('PASS original36 gauge CCR momentum square, magnetic potential and noncommuting shifted momenta', flush=True)
    Pi = s.Matrix(3, 12, lambda i, a: s.Rational((i+3*a) % 11-5, 31))
    connection = s.zeros(4, 12); connection[1:, :] = A
    data = model.coefficients(e)
    substitutions = dict(zip(model.coordinates, A.reshape(36, 1)))
    C = data['momentum_shift'].subs(substitutions)
    classical = ((Pi.reshape(36, 1)-C).T*data['weight']*(Pi.reshape(36, 1)-C))[0]/2+actual['magnetic']
    original = model.source.hamiltonian(e, connection, s.zeros(3, 48), Pi)
    assert s.simplify(classical-original) == 0
    # Source values and all nine generic divergence cancellations use the
    # actual native Gram, including Y norm1 rather than the mother trace2.
    N, sigma = e0[0, 0], model.source.sigma
    source_data = model.coefficients(e0)
    equal(source_data['weight'], sigma/N*s.kronecker_product(s.eye(3), model.source.gram_inverse))
    equal(source_data['momentum_shift'], s.zeros(36, 1))
    expected = contraction(model.magnetic, model.magnetic*model.source.gram)/(2*sigma*N)
    assert s.expand(source_data['magnetic_potential']-expected) == 0
    # Keep the complete original time-connection term for the common graph.
    connection[0, :] = s.Matrix([[s.Rational(a-5, 37) for a in range(12)]])
    spatial_A = s.zeros(3, 48)
    spatial_A[:, :12] = s.Matrix(3, 12, lambda i, a: s.Rational((i+a) % 5-2, 47))
    spatial_Pi = [s.Matrix(3, 12, lambda j, a: s.Rational((i+2*j+a) % 7-3, 53)) for i in range(3)]
    whole_original = model.source.hamiltonian(e, connection, spatial_A, Pi)
    G = model.source.gauss(connection, Pi, spatial_Pi)
    divergence = sum(contraction(spatial_Pi[i][i, :], connection[0, :])+
                     contraction(Pi[i, :], spatial_A[i, :12]) for i in range(3))
    assert s.simplify(whole_original-original+(connection[0, :]*G)[0]-divergence) == 0
    print('PASS exact native source coefficients and full A0 Gauss/spatial-boundary Legendre identity', flush=True)
    inputs = [HERE/name for name in ('source_gauge_quantum_energy.py', 'source_gauge_legendre.py',
        'source_gauge_legendre.json', 'independent_source_gauge_legendre.json', 'source_common_hamiltonian.json')]
    inputs.append(BASE/'active-gauge/receipt.json')
    result = {'root': ROOT_ID, 'source_sha256': model.source.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
        'scope': 'COMPLETE_HOMOGENEOUS_NATIVE12_GAUGE_QUANTUM_ENERGY_WITH_ORIGINAL_LIVE_COFRAME_PARAMETERS',
        'coordinate_dimension': 36, 'native_pairing': encode(model.source.gram),
        'operator': '1/2*(p-C)^T W*(p-C)+V_B, p=-i partial_A, W=K_E^-1 tensor Gram^-1, C=vec(K_mix B Gram)',
        'magnetic_potential': '-trace(B^T K_magnetic B Gram)/2 with B=([A2,A3],[A3,A1],[A1,A2])',
        'expanded_operator': '-1/2 W:partial^2+i*(W C).partial+1/2 C^T W C+V_B',
        'all9_generic_native_divergence_coefficients_zero': True,
        'derivative_ordering_constant_zero_for_every_admissible_coframe': True,
        'shifted_momentum_commutator': 'i*(partial_i C_j-partial_j C_i)',
        'actual_coframe': encode(e), 'actual_spatial_connection': encode(A),
        'actual_shift': encode(actual['shift']), 'actual_nonzero_momentum_commutator': encode(actual['commutator']),
        'wavepacket': {'dimension': 36, 'function': 'eta(y) exp(-|y|^2/2) (1+i ell.y+(m.y)^2/2), y=A-A0; eta smooth compact and equal1 near0',
            'ell_j': '(j+1)/41', 'm_j': '((j mod 7)-3)/43',
            'kinetic': str(actual['kinetic']), 'magnetic': str(actual['magnetic']), 'whole': str(actual['whole']),
            'nested_minus_expanded': '0', 'omit_shift_defect': str(actual['omit_shift_defect'])},
        'source_specialization': 'W=(sigma/N) I3 tensor Gram^-1, C=0, V_B=trace(B^T B Gram)/(2 sigma N)',
        'original_scalar_pair_Y_norm': str(model.source.gram[11, 11]),
        'original_A0_term': '-A0.G_gauge+div(Pi_Ai A0); retained until the common full Gauss graph is consumed',
        'original_Legendre_H_and_A0_boundary_readback': True,
        'common_component_domain': 'C_c^infinity(R^36) tensor finite CAR, at fixed source-admissible e; polynomial coefficients and all finite derivatives preserve each compact support',
        'coframe_quantized_or_full_joint_spectral_measure_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_gauge_quantum_energy.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')


if __name__ == '__main__':
    main()
