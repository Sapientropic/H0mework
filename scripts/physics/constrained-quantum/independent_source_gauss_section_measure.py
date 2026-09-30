#!/usr/bin/env python3
"""Independent local orbit-Jacobian and Gauss-section pairing audit.

The measure producer is not imported. Original native representations pay the
field Jacobian; a quaternion surface chart pays the Haar coordinate density.
The weighted adjoint is checked by its local integration-by-parts coefficient,
without assuming self-adjointness of the Hamiltonian or a global quotient.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from independent_source_quantum_gauss_section import (
    RawGaussSection, finite_wedge, compound, HERE, ROOT, ROOT_ID,
    bindings, clean, rational, eq, decode, encode, zero, terms,
    current, state_encode)
from independent_source_gauss_quantum_current import decoded_state
from independent_source_gauge_legendre import realify, source


class RawSectionMeasure:
    def __init__(self):
        self.section = RawGaussSection()
        self.native = self.section.native
        self.A = s.Matrix(s.symbols('gauge0:36', real=True))
        for index in self.section.fixed: self.A[index-67] = self.section.source[index]
        V = s.Matrix.hstack(*(s.kronecker_product(s.eye(3), ad)*self.A for ad in self.native.ads))
        self.M = clean(V[[j-67 for j in self.section.fixed], :])
        self.determinant = s.factor(self.M.det())
        source_point = {a: self.section.source[67+j] for j, a in enumerate(self.A) if isinstance(a, s.Symbol)}
        self.source_determinant = s.factor(self.determinant.subs(source_point))
        assert self.source_determinant != 0
        self.orientation = s.sign(self.source_determinant)
        self.density = s.factor(self.orientation*self.determinant)
        self.source_density = s.factor(self.density.subs(source_point)); assert self.source_density > 0
        self.point = source_point
        self.K = [clean(sum((self.native.S[j, h]*self.native.fund[j] for j in range(12)), s.zeros(7)))
                  for h in range(3)]
        self.P = clean(-self.K[0]*self.K[0])
        self.stabilizer_Gram = clean(self.native.S.T*self.native.Gram*self.native.S)
        self.metric_Haar_factor = s.sqrt(self.stabilizer_Gram.det())
        eq(self.stabilizer_Gram, 2*s.eye(3))
        zero(self.metric_Haar_factor-2*s.sqrt(2))
        for L in self.section.T: zero(s.trace(L))

    def quaternion(self, u):
        return clean(s.eye(7)-self.P+u[0]*self.P+
                     sum((u[h+1]*self.K[h] for h in range(3)), s.zeros(7)))

    def compose(self, u, v):
        return s.Matrix([u[0]*v[0]-sum(u[j]*v[j] for j in range(1, 4)),
            *[u[0]*v[h+1]+v[0]*u[h+1]+sum(self.native.structure[a][h, b]*u[a+1]*v[b+1]/2
              for a in range(3) for b in range(3)) for h in range(3)]])

    def group_boson(self, u):
        g = self.quaternion(u)
        scalar = clean(self.native.Rd.T*realify(compound(g, 4))*self.native.R)
        def pair(A, B):
            return s.expand(s.re(-s.trace(A[:3, :3]*B[:3, :3])-s.trace(A[3:5, 3:5]*B[3:5, 3:5])-A[5, 5]*B[5, 5]))
        ad = clean(self.native.Gram.inv()*s.Matrix(12, 12,
            lambda a, b: pair(self.native.fund[a], g*self.native.fund[b]*g.H)))
        return s.diag(s.eye(6), scalar, ad, ad, ad)

    def group_CAR(self, u):
        _, _, degrees, _ = source.parse_source(ROOT)
        internal = s.diag(*(compound(self.quaternion(u), d) for d in degrees))
        matter = s.diag(*[internal]*4)
        return s.diag(matter, matter.conjugate())


def quaternion_Haar(model):
    u, v = s.Matrix(s.symbols('u0:4', real=True)), s.Matrix(s.symbols('v0:4', real=True))
    left = model.compose(u, v).jacobian(v)
    norm = (u.T*u)[0]
    eq(left.T*left, norm*s.eye(4)); zero(left.det()-norm**2)
    # On the upper sphere chart u=(w,v), dw=-v.dv/w. Pull back the
    # original Euclidean quaternion metric before choosing any normalization.
    w = s.Symbol('w', positive=True); vec = s.Matrix(s.symbols('v1:4', real=True))
    r2 = (vec.T*vec)[0]
    differential = (-vec.T/w).col_join(s.eye(3))
    metric = clean(differential.T*differential)
    sphere_equation = w*w+r2-1
    theta = model.compose(s.Matrix([w, *(-vec)]), s.Matrix(s.symbols('du0:4', real=True)))
    du = s.Matrix(s.symbols('du0:4', real=True))
    theta = clean(theta.jacobian(du)[1:, :]*differential)
    def on_sphere(expression):
        return s.factor(s.rem(s.together(expression).as_numer_denom()[0], sphere_equation, w))
    for x in theta.T*theta-metric: assert on_sphere(x) == 0
    assert on_sphere(theta.det()-1/w) == 0
    assert on_sphere(metric.det()-1/w**2) == 0
    # Exponential coordinates have u0=cos r, uvec=(sin r/r) alpha.
    # Radial/tangential derivative eigenvalues are cos r,sin r/r,sin r/r.
    r = s.Symbol('r', positive=True)
    dv_dalpha = s.diag(s.cos(r), s.sin(r)/r, s.sin(r)/r)
    density = s.simplify(dv_dalpha.det()/s.cos(r))
    zero(density-(s.sin(r)/r)**2)
    assert s.limit(density, r, 0) == 1
    series = s.series(density, r, 0, 6).removeO()
    zero(series-1+r*r/3-2*r**4/45)
    return {'quaternion_left_translation_orthogonal_orientation': True,
            'source_native_stabilizer_Gram': encode(model.stabilizer_Gram),
            'native_metric_Haar_relative_to_identity_coordinate_Haar': str(model.metric_Haar_factor),
            'same_disintegration_with_native_metric_Haar': 'rho/(2*sqrt(2)) dmu_native dz = rho dmu_coordinate dz',
            'surface_chart_density': 'du1 du2 du3 / u0 for u0>0',
            'Maurer_Cartan_surface_chart_determinant': '1/u0',
            'exponential_coordinate_density': '(sin(r)/r)^2, r=|alpha|; value1 at alpha=0',
            'normalization': 'identity coordinate density1; total SU2 Haar volume2*pi^2 would need a separately retained factor for probability normalization',
            'source_Haar_gradient': encode(s.zeros(3, 1)), 'source_Haar_Hessian': encode(-s.Rational(2, 3)*s.eye(3))}


def generic_field_Jacobian(model):
    # Local group determinant is identically1 because all three original
    # field generators are traceless. The variational equation for a path
    # g(t) gives d log det(T(g))/dt=Tr(L(g^-1 dg/dt))=0, det at1=1.
    # Column ordering only affects orientation; absolute density is invariant.
    source_orbit = clean(s.Matrix.hstack(*(L*model.section.source for L in model.section.T)))
    forward = source_orbit.row_join(model.section.free_reader.T)
    density = s.Abs(s.factor(forward.det()))
    zero(density-model.source_density)
    # This block determinant is universal in the actual97 field values: move
    # the three fixed rows first, then the original retained coordinate rows.
    q = model.section.source.copy(); q[67:, :] = model.A
    V = clean(s.Matrix.hstack(*(L*q for L in model.section.T)))
    fixed, free = model.section.fixed, model.section.free
    ordered = V.row_join(model.section.free_reader.T)[fixed+free, :]
    eq(ordered[:3, :3], model.M); eq(ordered[:3, 3:], s.zeros(3, 100))
    eq(ordered[3:, 3:], s.eye(100))
    return {'actual_source103_forward_Jacobian_nonzero': True,
            'universal_field_block_determinant': 'det[V(z),If]=orientation*det M(z)',
            'whole_original_field_group_determinant_one': True,
            'local_density': 'abs(det M(z))*j_Haar(alpha) d^3alpha d^100z',
            'source_density': str(model.source_density)}


def formal_adjoint_checks(model):
    variables = [a for a in model.A if isinstance(a, s.Symbol)]
    log_gradient = [s.cancel(s.diff(model.density, x)/model.density) for x in variables]
    f, fp, g, gp = s.symbols('f fp g gp', complex=True)
    rho, drho = s.symbols('rho drho', real=True)
    # Pointwise divergence identity; integrate against compact support.
    # bar(f) p(g) rho - overline((p-i dlogrho)f)g rho
    # equals -i partial(bar(f)g rho).
    lhs = s.conjugate(f)*(-s.I*gp)*rho-s.conjugate(-s.I*fp-s.I*drho*f/rho)*g*rho
    zero(s.expand(lhs+s.I*(s.conjugate(fp)*g*rho+s.conjugate(f)*gp*rho+s.conjugate(f)*g*drho)))
    # Multiplication by sqrt(rho) pays the canonical half-density transport.
    root = s.sqrt(rho)
    transported_symmetric = root*(-s.I*(fp/root-f*drho/(2*rho*root))-s.I*drho*f/(2*rho*root))
    zero(transported_symmetric+s.I*fp)
    source_first = [s.factor(value.subs(model.point)) for value in log_gradient]
    source_second = s.Matrix(len(variables), len(variables),
        lambda i, j: s.factor(s.diff(log_gradient[i], variables[j]).subs(model.point)))
    return dict(variables=variables, log_gradient=log_gradient, source_log_gradient=s.Matrix(source_first),
                source_log_Hessian=source_second,
                formal_adjoint='p_j^*=p_j-i partial_j(log rho) on the compact smooth local weighted domain',
                symmetric_momentum='p_rho,j=p_j-i partial_j(log rho)/2',
                half_density='U=sqrt(rho): U p_rho U^-1=-i partial; the original p is not silently declared symmetric')


def actual_group_Jacobian(model, candidate):
    u = s.Matrix(list(map(s.sympify, candidate['measure']['actual_unit_quaternion'])))
    zero((u.T*u)[0]-1)
    c, d = u[0], u[1]
    assert u[2] == u[3] == 0
    # These are derivatives of (cos r,sin r*n) at n=(1,0,0), with
    # transverse columns multiplied by r exactly as in the saved consumer.
    du = s.Matrix([[-d, 0, 0], [c, 0, 0], [0, d, 0], [0, 0, d]])
    body = s.Matrix.hstack(*(model.compose(s.Matrix([u[0], *(-u[1:, :])]), du[:, j])[1:, :]
                             for j in range(3)))
    group = model.group_boson(u); zero(group.det()-1)
    V = s.Matrix.hstack(*(L*model.section.source for L in model.section.T))
    forward = group*(V*body).row_join(model.section.free_reader.T)
    determinant = s.factor(forward.det())
    zero(determinant-s.sympify(candidate['measure']['actual_scaled_forward_determinant']))
    zero(s.Abs(determinant)-model.source_density*d*d)
    CAR = model.group_CAR(u); eq(CAR.H*CAR, s.eye(504))
    word = tuple(candidate['actual_Hamiltonian_consumer']['CAR'])
    moved = finite_wedge(CAR, word)
    zero(sum(s.conjugate(x)*x for x in moved.values())-1)
    return {'actual_nonidentity_full103_Jacobian': str(determinant),
            'actual_full504_unitarity_and_finite_CAR_norm': True}


def compact_packet_and_source_derivatives(model, candidate, formal):
    import mpmath as mp
    native = model.native
    zero_values = dict.fromkeys(native.x_symbols, 0)
    D0 = native.Dsymbol.subs(zero_values)
    eq(D0, native.O.T*native.O)
    perturbations = [rational(D0.inv()*native.Dsymbol.diff(x)) for x in native.x_symbols]
    bound = max(sum(abs(E[i, j]) for E in perturbations for j in range(9)) for i in range(9))
    delta = s.cancel(1/(10*(1+bound)))
    expected = candidate['adjoint_and_actual_packet']
    zero(bound-s.sympify(expected['support']['D9_inverse_row_bound']))
    zero(delta-s.sympify(expected['support']['delta']))
    zero(delta*bound-s.sympify(expected['support']['normalized_D9_perturbation_bound']))
    assert delta*bound < s.Rational(1, 10)
    source_slice = model.section.free_reader*model.section.source
    eq(source_slice, decode(candidate['slice_coordinates']['source']))
    ia, ib = model.section.free.index(68), model.section.free.index(79)
    assert ia == candidate['slice_coordinates']['density_gauge_A1_index']
    assert ib == candidate['slice_coordinates']['density_gauge_A12_index']
    a, b = source_slice[ia], source_slice[ib]
    assert delta < min(a/2, b/2, s.Rational(1, 2))
    ell, Hesslog = s.zeros(100, 1), s.zeros(100)
    for i, x in enumerate(formal['variables']):
        index = model.section.free.index(67+list(model.A).index(x))
        ell[index] = formal['source_log_gradient'][i]
        for j, y in enumerate(formal['variables']):
            second = model.section.free.index(67+list(model.A).index(y))
            Hesslog[index, second] = formal['source_log_Hessian'][i, j]
    eq(ell, decode(expected['nonzero_source_log_gradient']))
    eq(Hesslog, decode(expected['source_log_Hessian']))
    # eta has all one-sided derivatives zero at its support boundary: every
    # derivative is rational in(1-t^2) times exp(-1/(1-t^2)). Its powers and
    # derivatives therefore have zero boundary terms for the exact IBP below.
    t = s.Symbol('t', real=True)
    eta = s.exp(1-1/(1-t*t))
    zero(eta.subs(t, 0)-1); zero(s.diff(eta, t).subs(t, 0))
    zero(s.diff(eta, t, 2).subs(t, 0)+2)
    M0, M2 = s.symbols('M0 M2', positive=True)
    a0, b0, eps = s.symbols('a0 b0 eps', positive=True)
    A = a0*a0+eps*eps*M2/M0
    rho_average = 8*b0*A
    density_da_average, density_db_average = 16*a0*b0, 8*A
    # The exact packet norms/pairings follow by parity and integration by
    # parts, independently of the producer's direct 80-digit quadrature.
    k1, k2 = s.Rational(2, 7), -s.Rational(3, 11)
    pairing_a = k1*rho_average+s.I*density_da_average/2
    pairing_b = k2*rho_average+s.I*density_db_average/2
    zero(s.conjugate(pairing_a)-(pairing_a-s.I*density_da_average))
    zero(s.conjugate(pairing_b)-(pairing_b-s.I*density_db_average))
    mp.mp.dps = 70
    def beta(x):
        return mp.exp(1-1/(1-x*x)) if abs(x) < 1 else mp.mpf(0)
    # Gauss-Legendre quadrature is independent of the producer's default
    # tanh-sinh rule; only displayed45-digit numbers are compared here.
    integrate = lambda fun: mp.quadgl(fun, [-1, -mp.mpf('0.5'), 0, mp.mpf('0.5'), 1])
    c0 = integrate(lambda x: beta(x)**2)
    c2 = integrate(lambda x: x*x*beta(x)**2)
    assert c0 > 0 and c2 > 0
    assert abs(c0-mp.mpf(expected['numerical_moments']['C0'])) < mp.mpf('1e-42')
    assert abs(c2-mp.mpf(expected['numerical_moments']['C2'])) < mp.mpf('1e-42')
    substitutions = {a0: a, b0: b, eps: delta, M0: s.Float(mp.nstr(c0, 72), 72), M2: s.Float(mp.nstr(c2, 72), 72)}
    def complex_number(expr):
        value = s.N(expr.subs(substitutions), 65)
        return mp.mpc(str(s.re(value)), str(s.im(value)))
    scaled = {key: complex_number(expr) for key, expr in [('norm', rho_average), ('p_a', pairing_a), ('p_b', pairing_b)]}
    for key, actual in scaled.items():
        text = expected['scaled_pairings'][key].replace('j', '*I')
        reported = s.sympify(text, rational=True)
        got = mp.mpc(str(s.re(reported).evalf(60)), str(s.im(reported).evalf(60)))
        assert abs(actual-got) < mp.mpf('1e-42'), key
    return {'D9_bound': str(bound), 'delta': str(delta), 'same_actual_positive_source_support': True,
            'compact_bump_all_boundary_terms_zero': True,
            'independent_Gauss_Legendre_moments': {'C0': mp.nstr(c0, 45), 'C2': mp.nstr(c2, 45)},
            'exact_IBP_scaled_pairings': {'norm': str(rho_average), 'p_a': str(pairing_a), 'p_b': str(pairing_b)},
            'positive_factor_retained': '(delta*M0)^100',
            'displayed_numeric_pairings_match_tolerance': '1e-42'}, ell, Hesslog, delta


def main():
    began = time.monotonic()
    path = HERE/'source_gauss_section_measure.json'; candidate = json.loads(path.read_text())
    count = bindings(candidate); assert candidate['root'] == ROOT_ID
    paid = ['independent_source_quantum_gauss_section.json', 'independent_source_quantum_stabilizer.json']
    for name in paid: count += bindings(json.loads((HERE/name).read_text()))
    model = RawSectionMeasure(); assert model.native.hashes == candidate['source_sha256']
    zero(model.source_density-s.sympify(candidate['measure']['source_slice_density']))
    assert candidate['measure']['Haar_identity_density'] == 1
    eq(model.stabilizer_Gram, decode(candidate['measure']['native_stabilizer_Gram']))
    zero(model.metric_Haar_factor-s.sympify(candidate['measure']['native_metric_Haar_factor']))
    zero(model.source_density/model.metric_Haar_factor-s.sympify(candidate['measure']['source_slice_density_relative_to_native_metric_Haar']))
    z = s.symbols('z0:100', real=True)
    metric_density = s.sympify(candidate['measure']['slice_density_relative_to_native_metric_Haar'], locals={str(x): x for x in z})
    metric_density = metric_density.subs({z[model.section.free.index(68)]: model.A[1], z[model.section.free.index(79)]: model.A[12]})
    zero(metric_density-model.density/model.metric_Haar_factor)
    group = quaternion_Haar(model)
    jacobian = generic_field_Jacobian(model)
    actual = actual_group_Jacobian(model, candidate)
    # The local ball's volume retains identity-normalized Haar, rather than
    # inserting a probability normalization into the disintegration.
    r, r0 = s.symbols('r r0', positive=True)
    zero(s.trigsimp(s.integrate(4*s.pi*s.sin(r)**2, (r, 0, r0))-(2*s.pi*r0-s.pi*s.sin(2*r0))))
    print('PASS independent quaternion surface Haar, generic FP factor and actual full103 Jacobian/CAR norm', flush=True)
    formal = formal_adjoint_checks(model)
    packet, ell, Hesslog, delta = compact_packet_and_source_derivatives(model, candidate, formal)
    print('PASS exact compact-support pairing, independent quadrature, source log density and weighted momentum adjoint', flush=True)
    from independent_source_quantum_gauss_section import raw_whole_action
    hc = candidate['actual_Hamiltonian_consumer']; word = tuple(hc['CAR'])
    k = s.zeros(100, 1)
    k[model.section.free.index(68)] = s.Rational(2, 7)
    k[model.section.free.index(79)] = -s.Rational(3, 11)
    gradient, Hessian = s.I*k, -2*s.eye(100)/delta**2-k*k.T
    eq(gradient, decode(hc['compact_packet_gradient'])); eq(Hessian, decode(hc['compact_packet_Hessian']))
    half_gradient = gradient-ell/2
    half_Hessian = Hessian-(ell*gradient.T+gradient*ell.T)/2+ell*ell.T/4-Hesslog/2
    eq(half_gradient, decode(hc['half_density_relative_gradient']))
    eq(half_Hessian, decode(hc['half_density_relative_Hessian']))
    # Differentiate the actual scalar half-density, rather than inserting
    # a freely chosen leg normalization or changing the operator ordering.
    aa, bb = s.symbols('aa bb', positive=True)
    weight_root = s.sqrt(8)*aa*s.sqrt(bb)
    for i, x in enumerate((aa, bb)):
        log_derivative = s.diff(s.log(weight_root**2), x)
        zero(weight_root*s.diff(1/weight_root, x)+log_derivative/2)
        for y in (aa, bb):
            zero(weight_root*s.diff(1/weight_root, x, y)-log_derivative*s.diff(s.log(weight_root**2), y)/4+
                 s.diff(s.log(weight_root**2), x, y)/2)
    _, original_jet = model.section.extension_jet(model.section.source, {word: 1}, {word: gradient}, {word: Hessian})
    _, half_jet = model.section.extension_jet(model.section.source, {word: 1}, {word: half_gradient}, {word: half_Hessian})
    model.section.Gauss_checks(model.section.source, original_jet)
    model.section.Gauss_checks(model.section.source, half_jet)
    original = raw_whole_action(model.section, model.section.source, original_jet)
    half = raw_whole_action(model.section, model.section.source, half_jet)
    for key in original:
        assert terms([(1, original[key]), (-1, decoded_state(hc['original_four_components'][key]))]) == {}, key
        assert terms([(1, half[key]), (-1, decoded_state(hc['half_density_four_components'][key]))]) == {}, key
    image = terms((1, value) for value in original.values())
    half_image = terms((1, value) for value in half.values())
    defect = terms([(1, half_image), (-1, image)]); assert defect
    for actual_state, key in [(image, 'original_image'), (half_image, 'half_density_image'), (defect, 'generated_similarity_correction')]:
        assert terms([(1, actual_state), (-1, decoded_state(hc[key]))]) == {}, key
    print('PASS original-order four-energy action on both complete Gauss jets and actual half-density conjugation', flush=True)
    assert candidate['decay_phase_space_or_Hilbert_selfadjointness_or_time_unitarity_claimed'] is False
    assert candidate['original_native_Hamiltonian_formal_symmetry_classified'] is False
    assert candidate['measure']['Haar_probability_normalization_or_extra_Z_inserted'] is False
    assert candidate['adjoint_and_actual_packet']['original_Hamiltonian_ordering_changed'] is False
    paths = [HERE/name for name in ('independent_source_gauss_section_measure.py', 'source_gauss_section_measure.py',
        'source_gauss_section_measure.json', 'independent_source_quantum_gauss_section.py',
        'independent_source_quantum_stabilizer.py', 'independent_source_joint_local_quantum.py')]+[HERE/name for name in paid]
    result = {'root': ROOT_ID, 'source_sha256': model.native.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_LOCAL_SOURCE_GAUSS_DENSITY_PAIRING_AND_NATIVE_HALF_DENSITY_CONJUGATION',
        'scope': candidate['scope'], 'checked_input_bindings': count, 'candidate_constructor_imported': False,
        'Haar': group, 'generic_Jacobian': jacobian, 'actual_nonidentity_consumer': actual,
        'compact_packet': packet,
        'formal_adjoint': {key: formal[key] for key in ('formal_adjoint', 'symmetric_momentum', 'half_density')},
        'pairing_review': 'The fixed original103 canonical-coordinate Lebesgue realization pulls back by the actual local orbit map. Its determinant is rho(z) times identity-normalized Haar density. Original finite exterior CAR is unitary, so all local section pairings disintegrate with the explicit Haar volume factor. The chart cutoff is on slice variables; no compact orbit cutoff is imposed as a Gauss solution.',
        'both_original_and_half_density_full_Gauss_jets_checked': True,
        'actual_original_four_components': {key: state_encode(value) for key, value in original.items()},
        'actual_half_density_four_components': {key: state_encode(value) for key, value in half.items()},
        'actual_nonzero_similarity_correction': state_encode(defect),
        'global_quotient_decay_phase_space_Hilbert_selfadjointness_or_evolution_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_gauss_section_measure.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent source Gauss section measure', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
