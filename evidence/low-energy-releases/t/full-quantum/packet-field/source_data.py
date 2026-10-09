#!/usr/bin/env python3
"""Native pole columns and uniform coefficient bounds for the 289-field lift.

The inputs are the certified original field numerator and native finite-circle
data. Every bound is generated from those coefficients, not supplied by a
caller. This file only writes inside its own packet-field capsule.
"""
from collections import Counter
import hashlib
import importlib.util
import json
from math import isqrt
from pathlib import Path
import re
import sys
import time

import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = ROOT / 'Verification/physics/low-energy-phenomenology'
FQ = BASE / 'full-quantum'
u, q, r, w, rho, a = s.symbols('u q r w rho a', real=True)


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def read(path):
    return json.loads(path.read_text())


def clean(matrix):
    return s.SparseMatrix(matrix.rows, matrix.cols,
        {key: value for key, raw in s.SparseMatrix(matrix).todok().items()
         if (value := s.expand(raw)) != 0})


def matrix_json(matrix):
    return {'shape': [matrix.rows, matrix.cols],
        'entries': [[i, j, str(value)] for (i, j), value in sorted(matrix.todok().items())]}


def circle_coefficients(certificate):
    scale = s.Integer(certificate['field_constant_denominator'])
    matrices = [s.MutableSparseMatrix(289, 289, {}) for _ in range(9)]
    for i, j, coefficients in certificate['field_numerator']:
        assert len(coefficients) <= 9
        for power, coefficient in enumerate(coefficients):
            coefficient = s.Rational(coefficient)/scale
            assert coefficient.is_real and coefficient.is_Rational
            if coefficient:
                matrices[power][i, j] = coefficient
    return [s.SparseMatrix(matrix) for matrix in matrices]


def rational_abs_upper(value):
    """A rational bound generated from the original single radical coefficient."""
    scalar, radical = value.as_coeff_Mul()
    assert scalar.is_Rational
    if radical == 1:
        return abs(scalar)
    square = s.expand(radical**2)
    assert square.is_Integer and square > 0 and radical.is_positive
    ceil = isqrt(int(square))
    if ceil*ceil < square:
        ceil += 1
    return abs(scalar)*ceil


def ceil_rational(value, digits=6):
    value = s.Rational(value)
    scale = 10**digits
    return s.Rational((int(value.p)*scale + int(value.q)-1)//int(value.q), scale)


def original_data():
    actual = read(BASE/'active-gauge/receipt.json')
    field = read(FQ/'light-modes/field-receipt.json')
    finite = read(BASE/'active-gauge/rotation/finite.json')
    generators = read(BASE/'active-gauge/rotation/generators.json')
    assert actual['source_sha256'] == field['source_sha256']
    for path, digest in actual['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    V = s.SparseMatrix(289, 1, {(i, j): s.sympify(value, locals={'u': u, 'q': q})
        for i, j, value in field['axial_original289_pole_leg']['entries']})
    F = s.Poly(s.sympify(field['axial_source_factor'], locals={'u': u, 'q': q}), u, q)
    return actual, field, finite, generators, V, F


def root_data(F):
    coefficient = F.coeff_monomial(u**2)
    center = -F.coeff_monomial(q**2)/coefficient
    assert all(i % 2 == j % 2 == 0 and i+j >= 2 for (i, j), _ in F.terms())
    normalized = s.expand(sum(c/coefficient*r**(i//2)*w**((i+j)//2-1)
        for (i, j), c in F.terms()))
    remainder = s.Poly(s.cancel((normalized-r+center)/w), r, w)
    text = (ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/LightModes/Source.lean').read_text()
    eps = s.Rational(re.search(r'def momentumRadius : ℝ := ([0-9]+/[0-9]+)', text).group(1))
    block = text.split('| .axialPhase =>', 1)[1].split('center_bound', 1)[0]
    formal = {(int(i), int(j)): s.Rational(c)
        for i, j, c in re.findall(r'⟨(\d+),(\d+),([^⟩]+)⟩', block)}
    assert dict(remainder.terms()) == formal
    bound = lambda p: sum(abs(c)*2**i for (i, _), c in p.terms())
    derivative = remainder.diff(r)
    source_radius = 1/(40*(1+bound(remainder)+bound(derivative)))
    assert 0 < eps < 1 and eps**2 < source_radius
    low, high = center-s.Rational(1, 20), center+s.Rational(1, 20)
    assert s.Rational(4, 5)**2 < low < high < 1
    D = 1+w*derivative.as_expr()
    for sigma in [1, -1]:
        for direction in [1, -1]:
            actual = s.diff(F.as_expr(), u).subs({u: sigma*rho*a, q: direction*rho}, simultaneous=True)
            expected = 2*coefficient*sigma*rho*a*D.subs({r: a*a, w: rho*rho})
            assert s.expand(actual-expected) == 0
    return {'coefficient': coefficient, 'center': center, 'remainder': remainder,
        'derivative': D, 'epsilon': eps, 'radius': source_radius, 'low': low, 'high': high}


def main():
    started = time.monotonic()
    actual, field, finite, generators, V, F = original_data()
    root = root_data(F)
    eps, cf = root['epsilon'], root['coefficient']
    lapse = s.sympify(actual['source_lapse'])
    clock = s.simplify(lapse*s.sqrt(2))
    assert s.simplify(clock**2) == s.Rational(108, 125) and clock < 1
    descriptors = actual['fields']
    records, degree_counts, bounds = [], Counter(), s.zeros(289, 1)
    radical_types = set()
    for (index, _), value in sorted(V.todok().items()):
        terms = []
        weighted_upper = 0
        for (time_degree, space_degree), coefficient in s.Poly(s.expand(value), u, q).terms():
            assert time_degree+space_degree >= 1
            real = s.simplify(coefficient/s.I**space_degree)
            assert real.is_real
            assert s.expand(real*s.I**space_degree-coefficient) == 0
            radical_types.add(str(real.as_coeff_Mul()[1]))
            degree_counts[time_degree+space_degree] += 1
            weighted_upper += rational_abs_upper(real)*eps**(time_degree+space_degree-1)
            terms.append({'coefficient': str(real), 'timeDegree': time_degree,
                'spaceDegree': space_degree, 'radialDegree': time_degree+space_degree-1})
        reconstructed = sum(s.sympify(term['coefficient'])*u**term['timeDegree']*
            (s.I*q)**term['spaceDegree'] for term in terms)
        assert s.expand(reconstructed-value) == 0
        assert s.expand(s.conjugate(value)-value.subs(q, -q)) == 0
        for sigma in [1, -1]:
            for direction in [1, -1]:
                divided = sum(s.sympify(term['coefficient'])*(sigma*a)**term['timeDegree']*
                    (s.I*direction)**term['spaceDegree']*rho**term['radialDegree'] for term in terms)
                assert s.expand(value.subs({u: sigma*rho*a, q: direction*rho}, simultaneous=True)-rho*divided) == 0
        # sqrt(r)>=4/5, D>=39/40, clock<1. Every factor is source-generated.
        residue_bound = ceil_rational(25*weighted_upper/(39*abs(cf)))
        bounds[index] = residue_bound
        records.append({'index': index, 'field': descriptors[index], 'terms': terms,
            'residue_uniform_rational_bound': str(residue_bound)})
    assert len(records) == 79 and sum(degree_counts.values()) == 2013
    print('PASS 79 original columns / 2013 nonconstant real i^space terms / four signed radial divisions', flush=True)

    # Replay the actual original linearized equation, without taking a supplied kernel certificate.
    momenta = [clock*u, 0, 0, s.I*s.sqrt(2)*q]
    H = s.MutableSparseMatrix(289, 289, {})
    for i, j, powers, coefficient in actual['Fourier_Jacobi_entries']:
        H[i, j] += s.sympify(coefficient)*s.prod(x**degree for x, degree in zip(momenta, powers))
    H = clean(H)
    injection = s.zeros(289, 1)
    injection[57] = -2*lapse
    assert clean(H*V-F.as_expr()*injection) == s.zeros(289, 1)
    assert clean(H.subs(q, -q)*V.subs(q, -q)-F.as_expr()*injection) == s.zeros(289, 1)
    wrong_fourier = clean(H*V.subs(q, -q)-F.as_expr()*injection)
    assert wrong_fourier != s.zeros(289, 1)
    scalar_rows = [i for i, row in enumerate(descriptors) if row['group'] == 'scalar_J']
    assert all(V[i] == 0 for i in scalar_rows)
    print('PASS all289 original source equations / reflected equations / wrong Fourier sign control', flush=True)

    # The two poles are a particular channel of the full inverse. Compute the
    # actual source projection it solves, rather than claiming that it is j_g00.
    Htime = [s.SparseMatrix(289, 289, {(i, j): s.Poly(v, u).nth(degree)/clock**degree
        for (i, j), v in H.todok().items() if s.Poly(v, u).nth(degree) != 0}) for degree in range(3)]
    assert all(s.Poly(v, u).degree() <= 2 for v in H.todok().values())
    reflected_time = V.subs(u, -u)
    odd = clean((V-reflected_time).applyfunc(lambda v: s.cancel(v/(2*u))))
    even = clean((V+reflected_time)/2)
    assert all(s.fraction(v)[1].free_symbols == set() for v in odd.todok().values())
    A, B = clean(-clock/cf*odd), clean(-clock**2/cf*even)
    projection = clean(Htime[1]*A)
    assert clean(Htime[2]*V) == s.zeros(289, 1)
    assert clean(Htime[2]*A) == clean(Htime[2]*B) == s.zeros(289, 1)
    assert clean(Htime[0]*A+Htime[1]*B) == s.zeros(289, 1)
    assert clean(Htime[0]*B+clock**2*u**2*projection+clock**2/cf*F.as_expr()*injection) == s.zeros(289, 1)
    derivative_factor = s.cancel(s.diff(F.as_expr(), u)/(2*cf*u))
    assert s.fraction(derivative_factor)[1].free_symbols == set()
    assert clean(projection+derivative_factor*injection) != s.zeros(289, 1)
    pole_projection = {'physical_spectral_variable': 'lambda',
        'sign_convention': 'NEGATIVE_INVERSE_POLE_CHANNEL: G_theta=-sum ell_sigma/(lambda-sigma*c*u); the source numerator Z already includes this minus sign',
        'factor_D': str(derivative_factor), 'pair_numerator_linear': matrix_json(A),
        'pair_numerator_constant': matrix_json(B), 'source_projection_numerator': matrix_json(projection),
        'pole_response': 'G_theta(lambda,q)=(lambda*A+B)/(D*(lambda^2-c^2*u^2)) = -sum_sigma ell_sigma/(lambda-sigma*c*u)',
        'exact_original_equation': 'H(lambda,q)*(lambda*A+B)=(lambda^2-c^2*u^2)*Z-(c^2/cF)*F(u,q)*j_g00',
        'on_root_source_equation': 'H(lambda,q)*G_theta=Z/D; Z=H1*A',
        'time_consumer': 'Xi=-sum_sigma ell_sigma*Phi_sigma, Phi_sigma_prime=sigma*c*u*Phi_sigma+J and Phi_sigma(0)=0, gives H(partial_t,q)Xi=(Z/D)*J',
        'full_second_time_coefficient_annihilates_pole_legs': True,
        'not_the_complete_negative_g00_source': True,
        'time_regularity': 'Only C1 Phi_sigma is needed: H2*Xi is the identically zero function, so its second distributional/classical derivative is zero without requiring Xi to be C2',
        'source_projection_nonzero_rows': len(projection.todok()),
        'spatial_sign': 'For the requested XiHat(k) built from ell(-k), use q(-k) and spatialFourier (exp(-ikx)), preserving the original +h current smear.'}
    (HERE/'pole-source.json').write_text(json.dumps(pole_projection, indent=2)+'\n')
    print('PASS genuine theta pole source projection / all time-polynomial coefficients / no full-source substitution', flush=True)

    matrices = {}
    circle_records = []
    zero = s.zeros(289)
    for axis, certificate in enumerate(finite['certificates']):
        coeffs = circle_coefficients(certificate)
        matrices[axis] = coeffs
        generator = s.SparseMatrix(289, 289, {(i, j): s.sympify(v)
            for i, j, v in generators['generators'][axis]['field_generator']})
        assert coeffs[0] == s.eye(289) and coeffs[1] == 4*generator
        get = lambda n: coeffs[n] if 0 <= n < 9 else zero
        for power in range(10):
            assert clean((power+1)*get(power+1)+(power-9)*get(power-1)-4*generator*get(power)) == zero
        for power in range(17):
            product = sum(((-1)**i*coeffs[i]*coeffs[power-i]
                for i in range(9) if 0 <= power-i < 9), zero)
            target = s.binomial(8, power//2)*s.eye(289) if power % 2 == 0 else zero
            assert clean(product-target) == zero
        for matrix in coeffs:
            assert all(i in scalar_rows or value == 0 for (j, i), value in matrix.todok().items() if j in scalar_rows)
        absolute = sum((m.applyfunc(abs) for m in coeffs), zero)
        circle_records.append({'axis': axis, 'degree': 8, 'denominator': '(1+t^2)^4',
            'coefficients': [{'power': n, **matrix_json(m)} for n, m in enumerate(coeffs)],
            'entry_uniform_coefficient_sum': matrix_json(s.SparseMatrix(absolute)),
            'maximum_row_sum_bound': str(max(sum(absolute[i, j] for j in range(289)) for i in range(289))),
            'initial_identity': True, 'native_generator_ODE': True, 'inverse_parameter_negation': True,
            'scalar_subspace_preserved': True})
    z_stabilizer = []
    for degree, matrix in enumerate(matrices[2]):
        expected = s.binomial(4, degree//2)*V if degree % 2 == 0 else s.zeros(289, 1)
        assert clean(matrix*V-expected) == s.zeros(289, 1)
        z_stabilizer.append(degree)
    # Full reconstruction uses Lz(z)Ly(y), exactly the inverse spatial-alignment order.
    abs_matrix = lambda axis: sum((m.applyfunc(abs) for m in matrices[axis]), zero)
    rotated_bounds = abs_matrix(2)*abs_matrix(1)*bounds
    assert all(value.is_Rational and value >= 0 for value in rotated_bounds)
    print('PASS all three native real circles / coefficient bounds / axial Lz stabilizer / full289 bound', flush=True)

    input_paths = [BASE/'active-gauge/receipt.json', FQ/'light-modes/field-receipt.json',
        BASE/'active-gauge/rotation/finite.json', BASE/'active-gauge/rotation/generators.json',
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/LightModes/Source.lean']
    data = {'scope': 'ORIGINAL289_POLETERM_SOURCE_TABLE_AND_BOUNDED_PHYSICAL_RESIDUES',
        'source_sha256': actual['source_sha256'], 'input_sha256': {str(p.relative_to(ROOT)):
            hashlib.sha256(p.read_bytes()).hexdigest() for p in input_paths},
        'fields': records, 'nonzero_columns': len(records), 'monomials': sum(degree_counts.values()),
        'total_degree_counts': dict(sorted(degree_counts.items())), 'radical_types': sorted(radical_types),
        'root': {'center': str(root['center']), 'window': [str(root['low']), str(root['high'])],
            'epsilon': str(eps), 'root_source_radius': str(root['radius']), 'rho_domain': '0<rho<=epsilon',
            'sqrt_root_lower': '4/5', 'sqrt_root_upper': '1', 'derivative_lower': '39/40',
            'derivative_upper': '41/40', 'source_coefficient': str(cf),
            'root_remainder': str(root['remainder'].as_expr()),
            'normalized_derivative': str(root['derivative']),
            'physical_clock': str(clock), 'four_signed_derivative_identities': True},
        'normalization': {'raw': 'V_i(u,q)=sum c_ab u^a (I*q)^b',
            'reduced': 'W_sigma,s,i(rho,a)=sum c_ab (sigma*a)^a_degree (I*s)^b rho^(a_degree+b-1)',
            'own_derivative': 'd_u F(sigma*rho*sqrt(r),s*rho)=2*cF*sigma*rho*sqrt(r)*D(r,rho^2)',
            'physical_residue': 'ell_sigma,s=c*W_sigma,s/(2*cF*sigma*sqrt(r)*D)',
            'coefficient_bound': 'sum |c_ab| epsilon^(a+b-1); each radical rounded upward before rational rounding',
            'residue_bound_factor': '25/(39*abs(cF)), from c<1,sqrt(r)>4/5,D>=39/40'},
        'fourier_reality': 'conj(V_sigma,s)=V_sigma,-s; each real native circle commutes with conjugation; same paired frame gives conj(ell_sigma(k))=ell_sigma(-k)',
        'scalar_increment_zero': True,
        'original_equation': 'H289(c*u,0,0,I*sqrt(2)*q) V(u,q)=F(u,q)*j_g00, j_g00[57]=-2*N',
        'original_reflected_equation_verified': True,
        'wrong_Fourier_sign_nonzero_rows': len(wrong_fourier.todok()),
        'axial_z_stabilizer_coefficients': z_stabilizer,
        'rotated_field_bounds': [[i, str(value)] for i, value in enumerate(rotated_bounds) if value],
        'rotated_max_coordinate_bound': str(max(rotated_bounds)),
        'rotated_l2_coefficient_squared_bound': str(sum(value**2 for value in rotated_bounds)),
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'field-data.json').write_text(json.dumps(data, indent=2)+'\n')
    (HERE/'circle-data.json').write_text(json.dumps({'circles': circle_records}, indent=2)+'\n')
    print('PASS source data written', data['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
