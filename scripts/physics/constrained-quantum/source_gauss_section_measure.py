#!/usr/bin/env python3
"""Canonical local measure of the original source Gauss section.

The103-coordinate Lebesgue density is disintegrated by its actual orbit map.
Coordinate Haar and native metric Haar keep their exact conversion factor.
The source slice Jacobian determines the
formal momentum adjoint and the half-density readout of the same Hamiltonian.
No group cutoff, global quotient, decay measure or operator reordering enters.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s
import mpmath as mp

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_quantum_gauss_section import SourceQuantumGaussSection, exterior_word, zero
from source_gauss_quantum_current import weighted_sum, encode_state
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode


def cross(vector):
    a, b, c = vector
    return s.Matrix([[0, -c, b], [c, 0, -a], [-b, a, 0]])


def norm_reduce(expression, symbols, relation):
    numerator, denominator = s.cancel(expression).as_numer_denom()
    return s.cancel(s.rem(s.Poly(numerator, symbols), s.Poly(relation, symbols)).as_expr()/denominator)


class SourceGaussSectionMeasure:
    def __init__(self):
        self.section = SourceQuantumGaussSection()
        m = self.section
        self.coordinates = s.Matrix(s.symbols('z0:100', real=True))
        self.z0 = clean(m.If.T*m.b0)
        self.gauge_a1 = m.free.index(68)
        self.gauge_a12 = m.free.index(79)
        a, b = self.coordinates[self.gauge_a1], self.coordinates[self.gauge_a12]
        self.rho = 8*a*a*b
        self.rho0 = s.factor(self.rho.subs(dict(zip(self.coordinates, self.z0))))
        assert self.rho0.is_positive
        self.log_gradient = s.zeros(100, 1)
        self.log_gradient[self.gauge_a1] = 2/a
        self.log_gradient[self.gauge_a12] = 1/b
        self.log_Hessian = self.log_gradient.jacobian(self.coordinates)
        self.ell0 = rational(self.log_gradient.subs(dict(zip(self.coordinates, self.z0))))
        self.log_Hessian0 = rational(self.log_Hessian.subs(dict(zip(self.coordinates, self.z0))))
        self.half_inverse_Hessian0 = rational(self.ell0*self.ell0.T/4-self.log_Hessian0/2)

    def half_density_jet(self, value, gradient, Hessian):
        """sqrt(rho0) times the actual jet of rho^-1/2 g at the source.

        Applying the original linear H and multiplying by sqrt(rho0) is
        therefore exactly U H U^-1, U f=sqrt(rho) f; no state normalization
        or modification of the original coefficient-left ordering is made.
        """
        words = set(value)|set(gradient)|set(Hessian)
        new_gradient, new_Hessian = {}, {}
        for word in words:
            v = value.get(word, 0)
            g = gradient.get(word, s.zeros(100, 1))
            H = Hessian.get(word, s.zeros(100))
            new_gradient[word] = rational(g-self.ell0*v/2)
            new_Hessian[word] = rational(H-(self.ell0*g.T+g*self.ell0.T)/2+self.half_inverse_Hessian0*v)
        return value.copy(), new_gradient, new_Hessian

    def source_support_radius(self):
        """A computed source D9 Neumann bound for the actual compact test."""
        m = self.section.native
        D0 = m.c.gram; inverse = D0.inv()
        columns = [clean(m.graph.O.T*T*m.graph.R) for T in m.rho_b]
        perturbations = [clean(inverse*s.Matrix.hstack(*(column[:, j] for column in columns))) for j in range(61)]
        bound = max(sum(abs(E[i, k]) for E in perturbations for k in range(9)) for i in range(9))
        delta = s.cancel(1/(10*(1+bound)))
        assert delta*bound < s.Rational(1, 10)
        assert delta < self.z0[self.gauge_a1]/2 and delta < self.z0[self.gauge_a12]/2
        assert delta < s.Rational(1, 2)
        return {'D9_inverse_row_bound': bound, 'delta': delta,
                'normalized_D9_perturbation_bound': s.cancel(delta*bound)}


def verify_Haar_and_Jacobian(model):
    m = model.section
    native_Gram = clean(m.native.S.T*m.native.gauge.gram*m.native.S)
    equal(native_Gram, 2*s.eye(3))
    metric_Haar_factor = s.sqrt(native_Gram.det())
    assert metric_Haar_factor == 2*s.sqrt(2)
    for L in m.L:
        assert s.trace(L) == 0
    for R in m.R:
        zero(R.H+R)
    orientation = (-1)**sum(row-j for j, row in enumerate(m.pivots))
    equal(s.Matrix([[m.V.row_join(m.If).det()]]), s.Matrix([[orientation*m.M.det()]]))
    b = m.If*model.coordinates+m.Ip*m.Ip.T*m.b0
    V = s.Matrix.hstack(*(L*b for L in m.L))
    M = m.Ip.T*V
    assert s.expand(M.det()+model.rho) == 0
    assert s.simplify(abs(m.M.det())-model.rho0) == 0

    r = s.Symbol('r', positive=True)
    c, d = s.symbols('cos_r sin_r', real=True)
    n = s.Matrix(s.symbols('n0:3', real=True)); N = n*n.T
    C = cross(n)
    zero(C*n)
    # The original quaternion product gives g^-1 dg in the K basis.
    du0 = -d*n.T
    du = c*N+d/r*(s.eye(3)-N)
    left = c*du-d*n*du0+d*C*du
    Haar_J = N+c*d/r*(s.eye(3)-N)+d*d/r*C
    zero(left-Haar_J-(c*c+d*d-1)*N)
    determinant = norm_reduce(Haar_J.det(), n[2], sum(x*x for x in n)-1)
    determinant = norm_reduce(determinant, c, c*c+d*d-1)
    assert s.cancel(determinant-d*d/r**2) == 0
    density = (s.sin(r)/r)**2
    assert s.limit(density, r, 0) == 1
    assert s.limit(s.diff(density, r, 2), r, 0) == -s.Rational(2, 3)

    # Actual nonidentity source forward Jacobian, with its two transverse
    # exponential-coordinate columns multiplied by r to keep exact rationals.
    cosine, sine = s.Rational(9999, 10001), s.Rational(200, 10001)
    g = m.group(s.Matrix([cosine, sine, 0, 0]))
    db = m.boson_group(g)
    assert s.factor(db.det()) == 1
    Jscaled = s.Matrix([[1, 0, 0], [0, cosine*sine, -sine*sine], [0, sine*sine, cosine*sine]])
    actual = db*(m.V*Jscaled).row_join(m.If)
    actual_det = s.factor(actual.det())
    assert s.simplify(actual_det-orientation*m.M.det()*sine*sine) == 0
    car = m.matter_group(g)
    equal(car.H*car, s.eye(504))
    saved = json.loads((HERE/'source_quantum_gauss_section.json').read_text())
    word = tuple(saved['actual_input']['CAR'])
    image = exterior_word(car, word)
    assert s.simplify(sum(s.conjugate(value)*value for value in image.values())-1) == 0
    return {'slice_orientation': orientation, 'source_forward_Jacobian_determinant': str(m.M.det()),
        'generic_slice_density': str(model.rho), 'source_slice_density': str(model.rho0),
        'source_generator_traces_zero': True, 'Haar_identity_density': 1,
        'Haar_convention': 'Coordinate Haar: the wedge of the three Maurer-Cartan coefficients in the displayed original K basis, with identity density1. This is not the native metric volume.',
        'native_stabilizer_Gram': encode(native_Gram),
        'native_metric_Haar_factor': str(metric_Haar_factor),
        'native_metric_Haar_density': '2*sqrt(2)*(sin(norm(alpha))/norm(alpha))^2',
        'slice_density_relative_to_native_metric_Haar': str(model.rho/metric_Haar_factor),
        'source_slice_density_relative_to_native_metric_Haar': str(s.simplify(model.rho0/metric_Haar_factor)),
        'Haar_exponential_density': '(sin(norm(alpha))/norm(alpha))^2, analytically1 at alpha=0',
        'Haar_source_radial_second_derivative': '-2/3',
        'original_quaternion_Maurer_Cartan_determinant_checked': True,
        'actual_unit_quaternion': list(map(str, (cosine, sine, 0, 0))),
        'actual_scaled_forward_determinant': str(actual_det),
        'actual_full103_group_determinant_one': True, 'all504_CAR_unitarity_and_actual_word_norm_checked': True,
        'disintegration': 'Phi^*(db103)=rho(z) dmu_coordinate(alpha) dz100=(rho(z)/(2*sqrt(2))) dmu_native_metric(alpha) dz100 on the actual one-to-one local orbit chart; rho=abs(det M).',
        'norm': 'Integral_{Phi(U x W)} ||E f||^2 db = mu_H(U) Integral_W rho(z)||f(z)||^2 dz.',
        'orbit_volume': 'mu_H denotes coordinate Haar and remains explicit. For a sufficiently small exponential ball of radius r0 contained in the chart, mu_H(U)=2*pi*r0-pi*sin(2*r0); native metric volume is exactly2*sqrt(2) times this.',
        'metric_Haar_pairing': 'mu_native_metric(U)*Integral_W (rho/(2*sqrt(2))) ||f||^2 dz is exactly the same original103 norm. The constant changes neither logarithmic derivatives nor U H U^-1.',
        'Haar_probability_normalization_or_extra_Z_inserted': False}


def verify_adjoint_and_packet(model):
    aidx, bidx = model.gauge_a1, model.gauge_a12
    z = model.coordinates
    h = s.sqrt(8)*z[aidx]*s.sqrt(z[bidx])
    # Work in the connected source chart a1>0,a12>0. Its positive square
    # root is fixed by rho, not supplied as a free field normalization.
    for j in (aidx, bidx):
        assert s.cancel(s.diff(h, z[j])/h-model.log_gradient[j]/2) == 0
        assert s.cancel(h*s.diff(1/h, z[j])+model.log_gradient[j]/2) == 0
        for k in (aidx, bidx):
            assert s.cancel(h*s.diff(1/h, z[j], z[k])-
                            (model.log_gradient[j]*model.log_gradient[k]/4-model.log_Hessian[j, k]/2)) == 0
    support = model.source_support_radius()
    delta, a0, b0 = support['delta'], model.z0[aidx], model.z0[bidx]
    mp.mp.dps = 80
    number = lambda x: mp.mpf(str(s.N(x, 85)))
    d, a, b = map(number, (delta, a0, b0))
    def eta(t):
        if abs(t) >= 1:
            return mp.mpf('0')
        return mp.exp(1-1/(1-t*t))
    def deta(t):
        if abs(t) >= 1:
            return mp.mpf('0')
        return -2*t*eta(t)/(1-t*t)**2
    integral = lambda f: mp.quad(f, [-1, 0, 1])
    c0 = integral(lambda t: eta(t)**2)
    c2 = integral(lambda t: t*t*eta(t)**2)
    assert c0 > 0 and c2 > 0
    A = a*a+d*d*c2/c0
    k1, k2 = mp.mpf(2)/7, -mp.mpf(3)/11
    norm = 8*b*A
    first = 8*b*integral(lambda t: (a+d*t)**2*eta(t)*(k1*eta(t)-1j*deta(t)/d))/c0
    second = 8*A*integral(lambda t: (b+d*t)*eta(t)*(k2*eta(t)-1j*deta(t)/d))/c0
    assert abs(first-(k1*norm+8j*a*b)) < mp.mpf('1e-65')
    assert abs(second-(k2*norm+4j*A)) < mp.mpf('1e-65')
    # Test the derived formal adjoint on the same actual compact packet.
    # The common strictly positive (delta*C0)^100 factor is retained below.
    formal_first = first-16j*a*b
    formal_second = second-8j*A
    assert abs(formal_first-mp.conj(first)) < mp.mpf('1e-65')
    assert abs(formal_second-mp.conj(second)) < mp.mpf('1e-65')
    assert first.imag != 0 and second.imag != 0
    return {'support': {key: str(value) for key, value in support.items()},
        'source_D9_source_chart_support_proved': '||D0^-1(D(x)-D0)||_infinity <= delta*C <1/10 on all61 scalar coordinates; all three positive coframe diagonals and a1,a12 stay positive.',
        'packet': 'f(z)=product_{j=0}^{99} eta((z_j-z_source_j)/delta) exp(i*(2/7)*(z_a-z_source_a)-i*(3/11)*(z_b-z_source_b)) tensor the original charged CAR word; eta(t)=exp(1-1/(1-t^2)) for |t|<1, zero otherwise.',
        'finite_positive_norm': '8*b0*(a0^2+delta^2*C2/C0)*(delta*C0)^100, Ck=Integral_{-1}^1 t^k eta(t)^2 dt',
        'positive_common_test_factor_retained': '(delta*C0)^100; no state normalization was imposed',
        'numerical_moments': {'C0': mp.nstr(c0, 45), 'C2': mp.nstr(c2, 45)},
        'scaled_pairings': {'norm': mp.nstr(norm, 45), 'p_a': mp.nstr(first, 45), 'p_b': mp.nstr(second, 45)},
        'quadrature_and_analytic_integration_by_parts_match_tolerance': '1e-65 after extracting the displayed positive test factor',
        'formal_adjoint': 'p_j^dagger=p_j-i partial_j(log rho) for p_j=-i partial_j on Cc_infinity of this slice chart.',
        'nonzero_source_log_gradient': encode(model.ell0), 'source_log_Hessian': encode(model.log_Hessian0),
        'half_density_map': 'U f=sqrt(rho) f sends the local weighted pairing to ordinary dz; U p_j U^-1=p_j+i*(partial_j log rho)/2.',
        'formally_symmetric_momentum_readout': 'p_j-i*(partial_j log rho)/2 is formally symmetric in rho dz. It is recorded as a derived readout and is not substituted into H_native.',
        'original_Hamiltonian_ordering_changed': False}


def main():
    started = time.monotonic(); model = SourceGaussSectionMeasure(); m = model.section
    measure = verify_Haar_and_Jacobian(model)
    print('PASS original full103 orbit Jacobian, coordinate/native-metric Haar conversion and unitary finite-CAR local norm disintegration', flush=True)
    adjoint = verify_adjoint_and_packet(model)
    print('PASS source slice density/half-density derivatives and actual compact100 wavepacket formal-adjoint pairing', flush=True)
    saved = json.loads((HERE/'source_quantum_gauss_section.json').read_text())
    word = tuple(saved['actual_input']['CAR']); value = {word: s.S.One}
    k = s.zeros(100, 1); k[model.gauge_a1] = s.Rational(2, 7); k[model.gauge_a12] = -s.Rational(3, 11)
    delta = s.sympify(adjoint['support']['delta'])
    gradient = {word: s.I*k}; Hessian = {word: -2*s.eye(100)/delta**2-k*k.T}
    original_jet = m.extend_jet(value, gradient, Hessian)
    transformed = model.half_density_jet(value, gradient, Hessian)
    transformed_jet = m.extend_jet(*transformed)
    m.verify_Gauss_jet(original_jet); m.verify_Gauss_jet(transformed_jet)
    original_parts, original_image = m.Hamiltonian_action(original_jet)
    half_parts, half_image = m.Hamiltonian_action(transformed_jet)
    defect = weighted_sum([(1, half_image), (-1, original_image)])
    assert original_image and half_image and defect
    print('PASS actual compact-packet native H_reduced and its source half-density conjugate, with nonzero generated correction', flush=True)
    paths = [HERE/name for name in ('source_gauss_section_measure.py', 'source_quantum_gauss_section.py',
        'source_quantum_gauss_section.json', 'independent_source_quantum_gauss_section.json',
        'source_stabilizer_phase_reduction.py', 'source_stabilizer_phase_reduction.json',
        'independent_source_stabilizer_phase_reduction.json', 'source_quantum_stabilizer.py',
        'source_quantum_stabilizer.json', 'independent_source_quantum_stabilizer.json')]
    result = {'root': ROOT_ID, 'source_sha256': m.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'CANONICAL_LOCAL_GAUSS_SECTION_DENSITY_PAIRING_AND_NATIVE_HAMILTONIAN_HALF_DENSITY_READOUT',
        'measure': measure, 'adjoint_and_actual_packet': adjoint,
        'slice_coordinates': {'density_gauge_A1_index': model.gauge_a1, 'density_gauge_A12_index': model.gauge_a12,
            'source': encode(model.z0)},
        'actual_Hamiltonian_consumer': {'CAR': list(word), 'compact_packet_gradient': encode(gradient[word]),
            'compact_packet_Hessian': encode(Hessian[word]), 'half_density_relative_gradient': encode(transformed[1][word]),
            'half_density_relative_Hessian': encode(transformed[2][word]),
            'original_four_components': {name: encode_state(part) for name, part in original_parts.items()},
            'half_density_four_components': {name: encode_state(part) for name, part in half_parts.items()},
            'original_image': encode_state(original_image), 'half_density_image': encode_state(half_image),
            'generated_similarity_correction': encode_state(defect),
            'operator': 'U R H_native E U^-1 with U=sqrt(rho), using the same original coefficient-left order and actual full103 second derivatives.',
            'both_extended_packets_all_Gauss_and_differentiated_Gauss_checked': True},
        'local_pairing_domain': 'Cc_infinity(W) tensor algebraic CAR504, W in the positive source slice chart; pairing Integral_W rho(z) inner_product(f,g) dz, rho>0. Original103 pairing disintegrates with the explicit local Haar factor.',
        'center_and_atlas': 'The signed source center action is retained. This local disintegration is not an arbitrary-section descent through global isotropy or a global orbit atlas.',
        'decay_phase_space_or_Hilbert_selfadjointness_or_time_unitarity_claimed': False,
        'original_native_Hamiltonian_formal_symmetry_classified': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_gauss_section_measure.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source Gauss section measure', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
