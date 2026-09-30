#!/usr/bin/env python3
"""Uniform source spatial stabilizer slice at every real Fourier momentum.

The original Gauss divergence fixes the derivative sign. Its full36 native
gauge orbit has an everywhere invertible Gram, even where the old three
coordinate minor vanishes. No Hamiltonian kinetic form is replaced.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_constraint_preservation import SourceConstraintPreservation
from source_stabilizer_phase_reduction import block_diagonal
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode


def zero(A):
    equal(rational(A), s.zeros(*A.shape))


def cross(v):
    a, b, c = v
    return s.Matrix([[0, -c, b], [c, 0, -a], [-b, a, 0]])


class SourceSpatialStabilizerOrbit:
    def __init__(self):
        self.source = SourceConstraintPreservation()
        self.gauge, self.S = self.source.gauge, self.source.stabilizer
        active = json.loads((BASE/'active-gauge/receipt.json').read_text())['actual_background']
        self.A = s.Matrix(active['gauge_connection']).applyfunc(s.sympify)[1:, :]
        self.k = s.Matrix(s.symbols('k1:4', real=True))
        self.G = block_diagonal(*([self.gauge.gram]*3))
        equal(self.S.T*self.gauge.gram*self.S, 2*s.eye(3))
        lower, diagonal = self.gauge.gram.LDLdecomposition(hermitian=False)
        equal(lower*diagonal*lower.T, self.gauge.gram)
        assert all(diagonal[j, j].is_positive for j in range(12))
        self.native_LDL = (lower, diagonal)
        blocks = []
        for i in range(3):
            V0 = clean(s.Matrix.hstack(*[self.gauge.ad(self.S[:, a])*self.A[i, :].T for a in range(3)]))
            equal(V0, -self.gauge.ad(self.A[i, :])*self.S)
            blocks.append(V0-s.I*self.k[i]*self.S)
        self.V = clean(s.Matrix.vstack(*blocks))
        self.N = clean(self.V.H*self.G*self.V)
        self.a = s.Rational(3, 5)*s.sqrt(2)
        self.r2 = (self.k.T*self.k)[0]
        self.b = self.r2+2*self.a**2
        self.C = clean((self.N/2-self.b*s.eye(3))/(2*s.I*self.a))
        self.q = s.Matrix([-self.C[1, 2], self.C[0, 2], -self.C[0, 1]])
        self.rotation = self.q.jacobian(self.k)
        equal(self.C, cross(self.q)); equal(self.rotation*self.k, self.q)
        equal(self.rotation.T*self.rotation, s.eye(3))
        equal(self.C*self.C, self.q*self.q.T-self.r2*s.eye(3))
        equal(self.N, 2*(self.b*s.eye(3)+2*s.I*self.a*self.C))
        self.denominator = s.expand(self.r2**2+4*self.a**4)
        self.inverse = rational((self.b**2*s.eye(3)-2*s.I*self.a*self.b*self.C-
                                 4*self.a**2*self.q*self.q.T)/(2*self.b*self.denominator))
        zero(self.N*self.inverse-s.eye(3)); zero(self.inverse*self.N-s.eye(3))
        equal(self.inverse.H, self.inverse)
        self.reader = rational(self.inverse*self.V.H*self.G)
        zero(self.reader*self.V-s.eye(3))
        self.P = rational(s.eye(36)-self.V*self.reader)

    def at(self, matrix, momentum):
        return rational(matrix.subs(dict(zip(self.k, momentum))))

    def decompose(self, momentum, field):
        V = self.at(self.V, momentum); P = self.at(self.P, momentum)
        reader = self.at(self.reader, momentum)
        parameter = rational(reader*field)
        transverse = rational(P*field)
        longitudinal = rational(V*parameter)
        zero(transverse+longitudinal-field)
        zero(V.H*self.G*transverse)
        zero(transverse.H*self.G*longitudinal)
        norm = s.simplify((field.H*self.G*field)[0])
        nt = s.simplify((transverse.H*self.G*transverse)[0])
        nl = s.simplify((longitudinal.H*self.G*longitudinal)[0])
        assert s.simplify(norm-nt-nl) == 0
        return {'parameter': parameter, 'transverse': transverse, 'longitudinal': longitudinal,
                'norm': norm, 'transverse_norm': nt, 'longitudinal_norm': nl}


def main():
    started = time.monotonic(); m = SourceSpatialStabilizerOrbit()
    # This literal polynomial square identity pays the all-real-k gap; no
    # guessed dispersion relation or sampled minimum enters the inverse.
    H = m.a*s.eye(3)+s.I*m.C
    equal(H.H, H)
    equal(m.N-2*m.a**2*s.eye(3), 2*(H.H*H+m.q*m.q.T))
    lam = s.Symbol('lambda', real=True)
    expected = (2*m.b-lam)*((2*m.b-lam)**2-16*m.a**2*m.r2)
    assert s.expand((m.N-lam*s.eye(3)).det()-expected) == 0
    assert s.expand(m.N.det()-8*m.b*m.denominator) == 0
    # The uniform lower bound is attained at a real source momentum.
    sharp_momentum = m.rotation.T*s.Matrix([0, 0, m.a])
    polarization = s.Matrix([s.I, 1, 0])/s.sqrt(2)
    equal(polarization.H*polarization, s.ones(1, 1))
    zero((m.at(m.N, sharp_momentum)-2*m.a**2*s.eye(3))*polarization)
    assert 2*m.a**2 == s.Rational(36, 25)
    print('PASS original all-real3k native orbit Gram, explicit inverse and sharp uniform gap36/25 by polynomial squares', flush=True)

    # Generic low-rank identities are the full36 projector proof: the
    # explicit middle3x3 matrices vanish before multiplication by V or V^HG.
    B = m.V.H*m.G
    zero(m.inverse*m.N*m.inverse-m.inverse)
    zero(m.inverse.H-m.inverse)
    zero(m.P*m.V)
    zero(B*m.P)
    zero(m.P.H*m.G-m.G*m.P)
    # P^2-P = V*(N^-1*N*N^-1-N^-1)*V^H*G. This factorization
    # plus reader*V=I proves idempotence/rank33 without a symbolic rank oracle.
    zero(m.V*(rational(m.inverse*m.N*m.inverse-m.inverse))*B)
    reversal = dict(zip(m.k, -m.k))
    zero(m.V.xreplace(reversal)-m.V.conjugate())
    zero(m.N.xreplace(reversal)-m.N.conjugate())
    zero(m.P.xreplace(reversal)-m.P.conjugate())
    print('PASS complete36 native orthoprojector identities, transverse33 carrier and exact plus/minus momentum reality', flush=True)

    pivots = (0, 6, 18)
    minor = m.V[list(pivots), :]
    expected_minor = s.Matrix([[-s.I*m.k[0], 0, m.a], [m.a, 0, s.I*m.k[0]],
                               [0, -m.a, s.I*m.k[1]]])
    equal(minor, expected_minor)
    assert s.expand(minor.det()-m.a*(m.k[0]**2-m.a**2)) == 0
    singular_old = s.Matrix([m.a, s.Rational(1, 7), -s.Rational(2, 9)])
    assert m.at(minor, singular_old).det() == 0
    old_V, old_P = m.at(m.V, singular_old), m.at(m.P, singular_old)
    assert old_V.rank() == 3 and old_P.rank() == 33
    zero(old_P*old_P-old_P)

    momentum = s.Matrix([s.Rational(1, 3), s.Rational(2, 5), -s.Rational(3, 7)])
    field = s.Matrix([s.Rational((j % 7)-3, 11)+s.I*s.Rational((3*j % 5)-2, 13) for j in range(36)])
    data = m.decompose(momentum, field)
    assert data['transverse_norm'] > 0 and data['longitudinal_norm'] > 0
    P = m.at(m.P, momentum)
    equal(P*P, P)
    partner = m.decompose(-momentum, field.conjugate())
    zero(partner['transverse']-data['transverse'].conjugate())
    zero(partner['parameter']-data['parameter'].conjugate())
    print('PASS old-minor zero point retains rank3/33 and actual nonaxis complex field decomposes with positive orthogonal norms', flush=True)

    paths = [HERE/name for name in ('source_spatial_stabilizer_orbit.py', 'source_constraint_preservation.py',
        'source_constraint_preservation.json', 'independent_source_constraint_preservation.json',
        'source_gauge_legendre.py', 'source_gauge_legendre.json', 'independent_source_gauge_legendre.json',
        'source_stabilizer_phase_reduction.py', 'source_stabilizer_phase_reduction.json',
        'independent_source_stabilizer_phase_reduction.json')]
    paths.append(BASE/'active-gauge/receipt.json')
    result = {'root': ROOT_ID, 'source_sha256': m.gauge.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'UNIFORM_ALL_REAL_THREE_MOMENTUM_SOURCE_SPATIAL_STABILIZER_ORBIT_AND_NATIVE_TRANSVERSE_PROJECTOR',
        'original_source_connection': encode(m.A), 'original_stabilizer_embedding': encode(m.S),
        'native_Gram': encode(m.gauge.gram), 'native_Gram_LDL_positive_diagonal': encode(m.native_LDL[1]),
        'original_Gauss_sign': 'G=div Pi_A-ad(A_i)^T Pi_A+other original currents. Its smeared canonical action on A_i is -partial_i epsilon-ad(A_i)epsilon, hence V_i(k)=ad_s(A_i)-i k_i S.',
        'orbit': encode(m.V), 'Gram': encode(m.N), 'source_amplitude': str(m.a),
        'source_momentum_frame': encode(m.rotation),
        'Gram_formula': 'N=2*((|k|^2+2a^2) I+2 i a cross(q)), q=the displayed original orthogonal momentum frame times k, a=3sqrt2/5.',
        'Gram_characteristic_polynomial': '(2b-lambda)*((2b-lambda)^2-16*a^2*|k|^2), b=|k|^2+2a^2',
        'Gram_eigenvalues': '2*(r^2+2a^2), 2*(r^2+2a^2+2ar), 2*(r^2+2a^2-2ar), r=|k|',
        'uniform_positive_gap': '36/25',
        'gap_identity': 'N-(36/25)I=2*((aI+i cross(q))^H*(aI+i cross(q))+q*q^T)',
        'sharp_gap_momentum': encode(sharp_momentum), 'sharp_gap_unit_polarization': encode(polarization),
        'inverse': encode(m.inverse),
        'inverse_formula': '(b^2 I-2 i a b cross(q)-4a^2 q q^T)/(2b*(|k|^4+4a^4))',
        'all_real_domain': 'b>=2a^2>0 and |k|^4+4a^4>0 for every real k; there is no excluded momentum locus.',
        'projector': 'P(k)=I36-V(k) N(k)^-1 V(k)^H G36, G36=I3 tensor nativeGram.',
        'reader': 'R(k)=N(k)^-1 V(k)^H G36; R V=I3, R P=0; a=P a+V R a.',
        'all_momentum_identities': {'P_squared_P': True, 'metric_selfadjoint': True,
            'P_V_zero': True, 'V_H_G_P_zero': True, 'V_rank': 3, 'P_rank': 33,
            'minus_k_is_complex_conjugate': True, 'idempotence_proof': 'P^2-P=V*(N^-1*N*N^-1-N^-1)*V^H*G36; the middle exact polynomial-rational matrix is zero.'},
        'old_coordinate_slice': {'pivots': list(pivots), 'minor': encode(minor),
            'determinant': 'a*(k1^2-a^2)', 'actual_zero_momentum': encode(singular_old),
            'whole_orbit_rank_at_old_minor_zero': 3, 'whole_projector_rank_at_old_minor_zero': 33},
        'actual_nonaxis_consumer': {'momentum': encode(momentum), 'field': encode(field),
            'parameter': encode(data['parameter']), 'transverse': encode(data['transverse']),
            'longitudinal': encode(data['longitudinal']), 'original_native_norm': str(data['norm']),
            'transverse_norm': str(data['transverse_norm']), 'longitudinal_norm': str(data['longitudinal_norm']),
            'orthogonal_norm_additivity_and_real_partner_checked': True},
        'consumer': 'The source linear spatial gauge component has a uniform full-momentum slice. The remaining fields must use the same recovered gauge parameter when this is spliced into the complete original constrained field generator.',
        'Hamiltonian_kinetic_replaced': False, 'full126_generator_spliced': False,
        'global_nonlinear_gauge_or_Hilbert_or_decay_measure_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_spatial_stabilizer_orbit.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source spatial stabilizer orbit', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
