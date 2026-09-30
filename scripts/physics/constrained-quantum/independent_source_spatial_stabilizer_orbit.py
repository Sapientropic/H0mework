#!/usr/bin/env python3
"""Independent original Gauss audit of the all-momentum stabilizer slice.

No orbit producer is imported. Raw exterior and native bracket matrices give
its full36 derivative-bearing gauge action. The inverse is independently
built as a polynomial in its traceless Hermitian part, and actual native
least-squares systems regenerate the reported transverse fields.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from independent_source_joint_temporal_rates import (
    RawSource, HERE, BASE, ROOT, ROOT_ID, bindings, clean, rational,
    zero, eq, encode, decode, dot)


class RawSpatialOrbit:
    def __init__(self):
        self.raw = RawSource()
        self.S = s.Matrix.hstack(*self.raw.O.nullspace())
        self.k = s.Matrix(s.symbols('k1:4', real=True))
        self.G = s.kronecker_product(s.eye(3), self.raw.Gram)
        self.stabilizer_Gram = clean(self.S.T*self.raw.Gram*self.S)
        eq(self.stabilizer_Gram, 2*s.eye(3))
        blocks = []
        for i in range(3):
            # Smear the original div(Pi)-ad(A)^T Pi and integrate the one
            # derivative by parts: coefficient of Pi is -d(eps)-ad(A)eps.
            constant = -self.raw.ad(self.raw.A[i+1, :])*self.S
            by_bracket = s.Matrix.hstack(*(self.raw.ad(self.S[:, a])*self.raw.A[i+1, :].T for a in range(3)))
            eq(constant, by_bracket)
            blocks.append(clean(constant-s.I*self.k[i]*self.S))
        self.V = s.Matrix.vstack(*blocks)
        self.N = clean(self.V.H*self.G*self.V)
        eq(self.N.H, self.N)
        self.r2 = (self.k.T*self.k)[0]
        at_zero = self.N.subs(dict.fromkeys(self.k, 0))
        self.a = s.sqrt(s.trace(at_zero)/12)
        assert self.a > 0
        self.alpha = s.factor(s.trace(self.N)/3)
        eq(at_zero, 4*self.a*self.a*s.eye(3))
        zero(self.alpha-2*(self.r2+2*self.a*self.a))
        self.D = clean(self.N-self.alpha*s.eye(3))
        self.C = clean(self.D/(4*s.I*self.a))
        eq(self.C+self.C.T, s.zeros(3))
        self.q = s.Matrix([-self.C[1, 2], self.C[0, 2], -self.C[0, 1]])
        self.rotation = self.q.jacobian(self.k)
        eq(self.q, self.rotation*self.k)
        eq(self.rotation.T*self.rotation, s.eye(3))
        eq(self.C*self.q, s.zeros(3, 1))
        eq(self.C*self.C, self.q*self.q.T-self.r2*s.eye(3))
        eq(self.D*self.D*self.D, 16*self.a*self.a*self.r2*self.D)
        self.denominator = s.factor(self.alpha*self.alpha-16*self.a*self.a*self.r2)
        zero(self.denominator-4*(self.r2**2+4*self.a**4))
        # Independent inverse from the paid cubic minimal identity. It does
        # not copy the candidate's q q^T rational numerator.
        self.inverse = rational(s.eye(3)/self.alpha-self.D/self.denominator+
                                self.D*self.D/(self.alpha*self.denominator))
        eq(self.N*self.inverse, s.eye(3)); eq(self.inverse*self.N, s.eye(3))
        eq(self.inverse.H, self.inverse)
        self.reader = rational(self.inverse*self.V.H*self.G)
        self.P = s.eye(36)-self.V*self.reader

    def at(self, A, momentum):
        return rational(A.subs(dict(zip(self.k, momentum))))

    def least_squares(self, momentum, field):
        V = self.at(self.V, momentum)
        N = clean(V.H*self.G*V)
        parameter, free = N.gauss_jordan_solve(V.H*self.G*field)
        assert free.rows == 0
        parameter = rational(parameter)
        longitudinal = rational(V*parameter)
        transverse = rational(field-longitudinal)
        eq(V.H*self.G*transverse, s.zeros(3, 1))
        zero((transverse.H*self.G*longitudinal)[0])
        norms = [s.factor((value.H*self.G*value)[0]) for value in (field, transverse, longitudinal)]
        zero(norms[0]-norms[1]-norms[2])
        return parameter, transverse, longitudinal, norms


def native_positivity(model, candidate):
    # Sylvester's original leading determinants provide an independent
    # positive native pairing, compared with the producer's LDL diagonal.
    leading = [s.S.One]+[s.factor(model.raw.Gram[:j, :j].det()) for j in range(1, 13)]
    assert all(value > 0 for value in leading)
    diagonal = s.diag(*(s.cancel(leading[j+1]/leading[j]) for j in range(12)))
    eq(diagonal, decode(candidate['native_Gram_LDL_positive_diagonal']))
    H = clean(model.a*s.eye(3)+s.I*model.C)
    eq(H.H, H)
    gap = 2*model.a*model.a
    eq(model.N-gap*s.eye(3), 2*(H.H*H+model.q*model.q.T))
    zero(gap-s.sympify(candidate['uniform_positive_gap']))
    lam = s.Symbol('lambda', real=True)
    polynomial = (model.alpha-lam)*((model.alpha-lam)**2-16*model.a*model.a*model.r2)
    zero(s.expand((model.N-lam*s.eye(3)).det()-polynomial))
    zero(s.expand(model.N.det()-model.alpha*model.denominator))
    kstar = decode(candidate['sharp_gap_momentum'])
    unit = decode(candidate['sharp_gap_unit_polarization'])
    zero((unit.H*unit)[0]-1)
    eq((model.at(model.N, kstar)-gap*s.eye(3))*unit, s.zeros(3, 1))
    return {'native_Gram_all12_leading_minors_positive': list(map(str, leading[1:])),
            'source_stabilizer_Gram': encode(model.stabilizer_Gram),
            'all_real_k_polynomial_square_gap': str(gap),
            'native_Lie_metric_gap': str(s.cancel(gap/2)),
            'gap_convention': 'N >= (36/25) I3 = (18/25) Gram_stabilizer; the native metric is retained.',
            'actual_sharp_gap_witness_verified': True,
            'full_characteristic_polynomial_and_nonzero_all_real_denominator': True}


def universal_projector(model):
    N, inverse, V, G = model.N, model.inverse, model.V, model.G
    B = V.H*G
    eq(inverse*N*inverse, inverse)
    eq(inverse.H, inverse)
    # These matrices are the exact coefficients of P^2-P, PV, BP and
    # P^H G-GP before multiplying the unchanged outer36 native factors.
    eq(inverse*N-s.eye(3), s.zeros(3))
    eq(N*inverse-s.eye(3), s.zeros(3))
    eq(inverse*N*inverse-inverse, s.zeros(3))
    eq(inverse.H-inverse, s.zeros(3))
    reversal = dict(zip(model.k, -model.k))
    eq(V.xreplace(reversal), V.conjugate())
    eq(N.xreplace(reversal), N.conjugate())
    eq(inverse.xreplace(reversal), inverse.conjugate())
    # For any momentum, positive N implies injective V. RV=I and
    # P=I-VR give im(P)=ker(R), dim ker(R)=36-3. The equality is an
    # algebraic consequence for every vector, not a sampled rank inference.
    eq(model.reader*V, s.eye(3))
    return {'all_real_native_projection_and_left_inverse': True,
            'complete36_projector_proof': 'P^2-P=V*(Ninv*N*Ninv-Ninv)*B; PV=V*(I-Ninv*N); BP=(I-N*Ninv)*B; P^H G-GP=G V*(Ninv-Ninv^H)*V^H G. All middle coefficients vanish identically.',
            'all_real_ranks': {'V': 3, 'P': 33},
            'all_real_plus_minus_k_complex_reality': True,
            'positive_pairing_is_original_native_Gram': True}


def main():
    began = time.monotonic()
    path = HERE/'source_spatial_stabilizer_orbit.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    model = RawSpatialOrbit(); assert model.raw.hashes == candidate['source_sha256']
    symbols = {str(k): k for k in model.k}
    eq(model.raw.A[1:, :], decode(candidate['original_source_connection']))
    eq(model.S, decode(candidate['original_stabilizer_embedding']))
    eq(model.raw.Gram, decode(candidate['native_Gram']))
    eq(model.V, decode(candidate['orbit'], symbols))
    eq(model.N, decode(candidate['Gram'], symbols))
    eq(model.inverse, decode(candidate['inverse'], symbols))
    eq(model.rotation, decode(candidate['source_momentum_frame']))
    zero(model.a-s.sympify(candidate['source_amplitude']))
    positivity = native_positivity(model, candidate)
    print('PASS raw original Gauss divergence/brackets, native36 orbit, all-real Gram inverse and sharp polynomial-square gap', flush=True)
    projector = universal_projector(model)
    print('PASS universal full36 native projector, rank3/33 and exact Fourier reality identities', flush=True)
    old = candidate['old_coordinate_slice']
    pivots = old['pivots']
    minor = model.V[pivots, :]
    eq(minor, decode(old['minor'], symbols))
    zero(s.expand(minor.det()-model.a*(model.k[0]**2-model.a**2)))
    oldzero = decode(old['actual_zero_momentum'])
    zero(model.at(minor, oldzero).det())
    oldV, oldP = model.at(model.V, oldzero), model.at(model.P, oldzero)
    assert oldV.rank() == 3 and oldP.rank() == 33
    eq(oldP*oldP, oldP)
    eq(oldP.H*model.G, model.G*oldP)
    actual = candidate['actual_nonaxis_consumer']
    k, field = decode(actual['momentum']), decode(actual['field'])
    parameter, transverse, longitudinal, norms = model.least_squares(k, field)
    for matrix, key in ((parameter, 'parameter'), (transverse, 'transverse'), (longitudinal, 'longitudinal')):
        eq(matrix, decode(actual[key]))
    for value, key in zip(norms, ('original_native_norm', 'transverse_norm', 'longitudinal_norm')):
        zero(value-s.sympify(actual[key]))
    assert norms[1] > 0 and norms[2] > 0
    P = model.at(model.P, k)
    eq(P*field, transverse); eq(P*P, P); eq(P.H*model.G, model.G*P)
    conjugate = model.least_squares(-k, field.conjugate())
    eq(conjugate[0], parameter.conjugate()); eq(conjugate[1], transverse.conjugate())
    print('PASS independently solved nonaxis source least-squares decomposition and old-coordinate-minor-zero control', flush=True)
    assert candidate['Hamiltonian_kinetic_replaced'] is False
    assert candidate['full126_generator_spliced'] is False
    assert candidate['global_nonlinear_gauge_or_Hilbert_or_decay_measure_claimed'] is False
    paths = [HERE/name for name in ('independent_source_spatial_stabilizer_orbit.py',
        'source_spatial_stabilizer_orbit.py', 'source_spatial_stabilizer_orbit.json',
        'independent_source_joint_temporal_rates.py', 'independent_source_gauge_legendre.py',
        'independent_source_lorentz_contact.py', 'independent_source_constraint_preservation.py')]
    result = {'root': ROOT_ID, 'source_sha256': model.raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_UNIFORM_ALL_REAL_MOMENTUM_SOURCE_STABILIZER_ORBIT_AND_NATIVE_PROJECTOR',
        'scope': candidate['scope'], 'checked_input_bindings': count, 'candidate_constructor_imported': False,
        'original_spatial_Gauss_sign': 'The original smeared div(Pi)-ad(A)^T Pi gives delta A=-partial epsilon-ad(A)epsilon. With epsilon=S c exp(i k.x), its coefficient is the independently generated V_i=-ad(A_i)S-i k_i S.',
        'original_all_momentum_Gram': encode(model.N),
        'independent_inverse_method': 'Let D=N-Tr(N)I/3. Its exact cubic D^3=16 a^2|k|^2 D generates Ninv=I/alpha-D/den+D^2/(alpha*den), den=alpha^2-16a^2|k|^2. Both original3x3 products are checked.',
        'native_positivity': positivity, 'universal_projector': projector,
        'actual_nonaxis_consumer': {'parameter': encode(parameter), 'transverse': encode(transverse),
            'longitudinal': encode(longitudinal), 'native_norms': list(map(str, norms)),
            'real_Fourier_partner_recomputed': True},
        'old_minor_zero': {'old_minor_zero': True, 'complete_orbit_rank': 3, 'complete_native_projection_rank': 33},
        'scope_review': 'A full real-momentum source linear gauge-orbit projector is generated, with the original derivative sign and native positive pairing. No Hamiltonian kinetic block is replaced. Complete other-field gauge transport and its coupling to the constrained full generator are separate consumers; this is not a nonlinear global gauge or a spectral/decay measure.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_spatial_stabilizer_orbit.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent source spatial stabilizer orbit', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
