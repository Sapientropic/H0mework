#!/usr/bin/env python3
"""Original metric/Spin Euler rows generate the temporal-constraint PDE.

The spatial Euler rows are reconstructed from the four temporal rows rather
than assumed zero off the constraint surface. Substitution into the original
coordinate Noether identity produces a homogeneous first-order transport
equation with an invertible source time coefficient.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_coframe_legendre import SourceCoframeLegendre, symmetric
from source_lorentz_contact import clean, equal, encode, ETA

TIME = [0, 4, 8, 12]
SPATIAL = [a for a in range(16) if a not in TIME]


class SourceCoframeConstraintTransport:
    def __init__(self):
        self.source = SourceCoframeLegendre()

    def Euler_embedding(self, e):
        assert e.det() != 0 and (e[:, 1:].T*ETA*e[:, 1:]).det() != 0
        D = self.source.at(self.source.D, e)[:, SPATIAL]
        R = clean(self.source.metric_lift_numerator(e)[SPATIAL, :]/e.det())
        Z = self.source.universal_null_frame(e)[:, 4:]
        Zs, Zt = Z[SPATIAL, :], Z[TIME, :]
        equal(D*R, s.eye(6)); equal(D*Zs, s.zeros(6))
        Gram_inverse = clean((Zs.T*Zs).inv())
        projection = clean(s.eye(12)-D.T*R.T)
        K = clean(-projection*Zs*Gram_inverse*Zt.T)
        equal(R.T*K, s.zeros(6, 4)); equal(Zs.T*K, -Zt.T)
        whole = s.zeros(16, 4)
        for a in range(4): whole[4*a, a] = 1
        for a, row in enumerate(SPATIAL): whole[row, :] = K[a, :]
        return {'D': D, 'R': R, 'Zs': Zs, 'Zt': Zt, 'Gram_inverse': Gram_inverse,
                'projection': projection, 'spatial': K, 'whole': whole}

    def derivative(self, e, direction, data):
        dD = self.source.at(self.source.D, direction)[:, SPATIAL]
        inverse = e.inv(); dinverse = -inverse*direction*inverse
        columns = []
        for a in range(6):
            value = s.zeros(4); value[:, 1:] = ETA*dinverse[1:, :].T*symmetric(s.eye(6)[:, a])/2
            columns.append(value.reshape(16, 1)[SPATIAL, :])
        dR = clean(s.Matrix.hstack(*columns))
        dZ = self.source.universal_null_frame(direction)[:, 4:]
        dZs, dZt = dZ[SPATIAL, :], dZ[TIME, :]
        Zs, Zt, D, R, W, P = [data[key] for key in ('Zs', 'Zt', 'D', 'R', 'Gram_inverse', 'projection')]
        dW = clean(-W*(dZs.T*Zs+Zs.T*dZs)*W)
        dP = clean(-dD.T*R.T-D.T*dR.T)
        dK = clean(-dP*Zs*W*Zt.T-P*dZs*W*Zt.T-P*Zs*dW*Zt.T-P*Zs*W*dZt.T)
        equal(dR.T*data['spatial']+R.T*dK, s.zeros(6, 4))
        equal(dZs.T*data['spatial']+Zs.T*dK, -dZt.T)
        whole = s.zeros(16, 4)
        for a, row in enumerate(SPATIAL): whole[row, :] = dK[a, :]
        return whole

    def transport(self, e, de):
        assert len(de) == 4
        data = self.Euler_embedding(e)
        derivatives = [self.derivative(e, d, data) for d in de]
        K = data['whole']
        spatial = [clean(e.T*K[[4*a+i for a in range(4)], :]) for i in range(1, 4)]
        lower = de[0].T.copy()
        for i in range(1, 4):
            rows = [4*a+i for a in range(4)]
            lower += de[i].T*K[rows, :]+e.T*derivatives[i][rows, :]
        lower -= s.Matrix.vstack(*[d.reshape(1, 16)*K for d in de])
        return {**data, 'derivatives': derivatives, 'time': e.T,
                'spatial_coefficients': spatial, 'lower': clean(lower),
                'solved_spatial': [clean(-e.T.inv()*A) for A in spatial],
                'solved_lower': clean(-e.T.inv()*lower)}


def verify_original_Noether(model, e, de):
    data = model.transport(e, de)
    F = s.Matrix(s.symbols('F0:4', real=True))
    dF = [s.Matrix(s.symbols('F'+str(mu)+'_0:4', real=True)) for mu in range(4)]
    E = (data['whole']*F).reshape(4, 4)
    dE = [(data['derivatives'][mu]*F+data['whole']*dF[mu]).reshape(4, 4) for mu in range(4)]
    raw = s.zeros(4, 1)
    for nu in range(4):
        raw[nu] = sum(E[a, mu]*de[nu][a, mu] for a in range(4) for mu in range(4))
        raw[nu] -= sum(dE[mu][a, mu]*e[a, nu]+E[a, mu]*de[mu][a, nu]
                       for a in range(4) for mu in range(4))
    transport = data['time']*dF[0]+sum((A*dF[i+1] for i, A in enumerate(data['spatial_coefficients'])), s.zeros(4, 1))+data['lower']*F
    equal(clean(raw+transport), s.zeros(4, 1))
    assert data['time'].det() != 0
    return data


def main():
    started = time.monotonic()
    model = SourceCoframeConstraintTransport()
    active = json.loads((BASE/'active-gauge/receipt.json').read_text())['actual_background']
    e0 = s.Matrix(active['coframe']).applyfunc(s.sympify)
    source = verify_original_Noether(model, e0, [s.zeros(4)]*4)
    for i, A in enumerate(source['solved_spatial']):
        expected = s.zeros(4); expected[0, i+1] = e0[0, 0]
        equal(A, expected)
    equal(source['lower'], s.zeros(4))
    e = s.Matrix([[s.Rational(7, 5), s.Rational(1, 9), 0, 0],
                  [s.Rational(1, 7), 1, s.Rational(1, 11), 0],
                  [0, 0, s.Rational(6, 5), s.Rational(1, 13)], [0, 0, 0, s.Rational(9, 8)]])
    de = [s.Matrix(4, 4, lambda a, mu: s.Rational((3*a+2*mu+nu) % 7-3, 41+2*nu)) for nu in range(4)]
    actual = verify_original_Noether(model, e, de)
    assert actual['lower'].todok()
    assert actual['spatial'].todok()
    # The two source polynomial identities needed for the uniform block
    # argument use the actual generic16 coframe, before selecting a frame.
    generic = model.source.e
    D = model.source.D
    Rnum = model.source.metric_lift_numerator(generic)
    Z = model.source.universal_null_frame(generic)[:, 4:]
    equal(clean(D*Rnum), clean(generic.det()*s.eye(6)))
    equal(clean(D*Z), s.zeros(6))
    print('PASS source metric/Spin Euler reconstruction and exact homogeneous first-order F4 Noether transport', flush=True)
    inputs = [HERE/name for name in ('source_coframe_constraint_transport.py', 'source_coframe_legendre.py',
        'source_coframe_legendre.json', 'independent_source_coframe_legendre.json',
        'source_coframe_constraints.json', 'independent_source_coframe_constraints.json',
        'source_spatial_time_coframe.py', 'source_spatial_time_coframe.json', 'independent_source_spatial_time_coframe.json')]
    provenance = json.loads((HERE/'source_coframe_legendre.json').read_text())
    result = {'root': ROOT_ID, 'source_sha256': provenance['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
        'scope': 'ORIGINAL_METRIC_SPIN_EULER_RECONSTRUCTION_AND_TEMPORAL_CONSTRAINT_TRANSPORT',
        'spatial_Euler_formula': 'E_sp=K(e)F, K=-(I-D_h,sp^T R_sp^T) Z_sp (Z_sp^T Z_sp)^-1 Z_time^T',
        'uniform_reconstruction': ['D_h R=I and D_h Z=0 are the original generic16 polynomial identities.',
            'Z_sp is injective: a Lorentz-skew map killing the nondegenerate spatial3-plane also kills its nonnull normal line, hence vanishes. Thus its real Euclidean Gram is invertible.',
            'R_sp^T K=0 and Z_sp^T K=-Z_time^T solve precisely the metric6 and full Spin6 Euler rows; no spatial Euler row is set to zero off F=0.'],
        'transport': 'e^T partial_t F+sum_i e^T K_i partial_i F+B(e,de)F=0',
        'Noether_source': 'sum_a,mu E_a,mu partial_nu e_a,mu - partial_mu(sum_a E_a,mu e_a,nu) = -partial_mu Q^mu_nu after the other original Euler equations hold',
        'source_readback': 'partial_t F0=N sum_i partial_i Fi; partial_t Fi=0, i=1,2,3',
        'source_time_determinant': str(e0.det()),
        'actual_coframe': encode(e), 'actual_time_matrix': encode(actual['time']),
        'actual_spatial_matrices': [encode(A) for A in actual['spatial_coefficients']],
        'actual_lower_matrix': encode(actual['lower']),
        'all_symbolic_F_and_first_derivative_coefficients_in_raw_Noether_match': True,
        'nonzero_spatial_Euler_off_constraint_retained': True,
        'linear_zero_initial_uniqueness': 'On any analytic first-order source-field solution inside the noncharacteristic chart, these coefficients are analytic and e^T is invertible. The solved homogeneous first-order constraint PDE has the unique analytic zero solution for zero initial F.',
        'consumer_order': 'First generate preservation of torsion, scalar-gradient, gauge-curvature, C9 and Gauss constraints so that the other original Euler equations hold; then consume this F4 transport. This module does not assume those earlier producers are already assembled.',
        'public_API': 'SourceCoframeConstraintTransport.{Euler_embedding,derivative,transport}',
        'full_spatial_Cauchy_solution_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_coframe_constraint_transport.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')


if __name__ == '__main__':
    main()
