#!/usr/bin/env python3
"""Independent original-density audit of the temporal reduced symbol.

Raw BF/Dirac/scalar/native gauge densities rebuild the compression. Ordinary
symbolic differentiation and Euclidean polynomial inversion replace the new
producer's temporal automatic differentiation and truncated Jet arithmetic.
The resulting object is a commuting classical symbol before quantization.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
import time
import sympy as s

from independent_source_coframe_live_ordering import RawLiveCoefficients, FREE, rational, eq
from independent_source_coframe_legendre import quotient_right_inverse, quotient_inverse
from independent_source_lorentz_contact import original_hessian, geometric_load, original_density_ports, original_gamma
from independent_source_scalar_gauss_reduction import OriginalGaussGraph
from independent_source_gauge_legendre import ETA, W, SIGMA, hodge
from independent_retained_hamiltonian_reduction import HERE, BASE, ROOT, ROOT_ID, DOMAIN, check_bindings
from independent_source_joint_temporal_rates import encode, decode

EPS = s.Symbol('source_epsilon', real=True)
SYMMETRIC = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))
N = 3*s.sqrt(30)/25


def zero(value): assert s.cancel(s.expand(value)) == 0


@lru_cache(maxsize=None)
def homogeneous_linear(value, ys):
    value = s.cancel(value)
    first = [s.cancel(s.diff(value, y)) for y in ys]
    assert all(not(set(ys)&coefficient.free_symbols) for coefficient in first)
    zero(value-sum(y*coefficient for y, coefficient in zip(ys, first)))


def all_original_affinity():
    raw = RawLiveCoefficients()
    n = s.Symbol('temporal_n', positive=True)
    b = s.symbols('temporal_b1:4', real=True)
    ys = (n, *b); e = raw.e.copy(); e[:, 0] = s.Matrix(ys)
    transform = s.kronecker_product(e, s.eye(6))
    Hi = rational(transform.T*original_hessian(s.eye(4)).inv()*transform/e.det())
    eq(original_hessian(e)*Hi, s.eye(24))
    symbols = s.Matrix(4, 4, s.symbols('audit_raw_e0:16', real=True))
    Gt = rational(geometric_load(symbols).xreplace(dict(zip(symbols, e)))[:, :16])
    R = quotient_right_inverse(e)
    Q = rational(R*quotient_inverse(e, e[:, 1:].T*ETA*e[:, 1:])*R.T)
    E, vertices = original_density_ports(e, original_gamma())
    J = [rational(s.diag(s.I*E.inv()*V, s.I*(E.inv()*V).conjugate())) for V in vertices]
    L = rational(raw.S*s.eye(24)[:6, :]+Gt.T*Hi)
    T = [rational(sum((L[i, a]*J[a] for a in range(24)), s.zeros(8))) for i in range(16)]
    K = rational(raw.A.T*Q*raw.A/2)
    Wcurrent = rational((L.T*Q*L+Hi)/2)
    coefficients = s.Matrix.hstack(*(current.reshape(64, 1) for current in J))
    tensor = rational(coefficients*Wcurrent*coefficients.T)
    mixed = [rational(sum(((raw.A.T*Q)[r, j]*T[j] for j in range(16)), s.zeros(8))) for r in range(6)]
    drift = rational(-s.I*sum(((raw.A.T*Q)[r, j]*raw.A.diff(q)[j, :]
        for r, q in enumerate(raw.q) for j in range(16)), s.zeros(1, 6))/2)
    correction = rational(-s.I*sum(((raw.A.T*Q)[r, j]*T[j].diff(q)
        for r, q in enumerate(raw.q) for j in range(16)), s.zeros(8))/2)
    einv = rational(e.adjugate()/e.det()); metric = rational(e.det()*einv*ETA*einv.T)
    scalar = s.zeros(4); scalar[0, 0] = 1/metric[0, 0]
    scalar[0, 1:] = -metric[0, 1:]/metric[0, 0]
    scalar[1:, 1:] = metric[1:, 0]*metric[0, 1:]/metric[0, 0]-metric[1:, 1:]
    families = {'coframe_kinetic': K, 'coframe_two_ordered_current_slots': tensor,
        'live_drift': drift, 'live_current_derivative': correction,
        'scalar_momentum_and_potential': rational(scalar), 'source_volume': s.Matrix([[e.det()]])}
    families.update({f'coframe_mixed_{i}': value for i, value in enumerate(mixed)})
    gamma = original_gamma()
    principal = [rational(s.I*e.det()*sum((einv[mu, a]*gamma[a] for a in range(4)), s.zeros(4))) for mu in range(4)]
    families.update({f'matter_principal_{i}': rational(E.inv()*principal[i]) for i in range(1, 4)})
    families['Yukawa_coefficient'] = rational(e.det()*E.inv())
    counts = {}
    for name, values in families.items():
        entries = list(values.todok().values())
        for value in entries: homogeneous_linear(value, ys)
        counts[name] = len(entries)
    for y in ys:
        eq(E.diff(y), s.zeros(4)); eq(raw.A.diff(y), s.zeros(16, 6)); eq(raw.S.diff(y), s.zeros(16, 6))
    return raw, ys, e, counts


def original_gauge_compression(e, ys):
    # Compute the original constitutive form through the Hodge definition,
    # then perform its actual velocity Legendre transform in one native color.
    # Polarization and the constant native Gram give the complete12 version.
    K = rational(-W*hodge(e)/SIGMA)
    metric = e.T*ETA*e
    pairs = ((0, 1), (0, 2), (0, 3), (2, 3), (3, 1), (1, 2))
    wedge = s.Matrix(6, 6, lambda i, j: -(metric[pairs[i][0], pairs[j][0]]*metric[pairs[i][1], pairs[j][1]]-
        metric[pairs[i][0], pairs[j][1]]*metric[pairs[i][1], pairs[j][0]])/(SIGMA*e.det()))
    eq(K, wedge)
    electric = K[:3, :3]; mixed = K[:3, 3:]; magnetic = K[3:, 3:]
    inverse = rational(electric.adjugate()/electric.det())
    eq(electric*inverse, s.eye(3)); eq(inverse*electric, s.eye(3))
    p = s.Matrix(s.symbols('audit_pi0:3', real=True)); B = s.Matrix(s.symbols('audit_B0:3', real=True))
    velocity = rational(inverse*(p-mixed*B))
    F = velocity.col_join(B)
    density = (F.T*K*F)[0]/2
    H = s.cancel((p.T*velocity)[0]-density)
    block = rational(s.hessian(H, (*p, *B)))
    eq(block[:3, :3], inverse); eq(block[:3, 3:], -inverse*mixed)
    eq(block[3:, 3:], mixed.T*inverse*mixed-magnetic)
    return K, block


def actual_compression(raw_cf, ys, e_generic, candidate):
    graph = OriginalGaussGraph(); raw = graph.raw
    qs = (s.S.One, 0, s.S.One, 0, 0, s.S.One)
    e = e_generic.subs(dict(zip(raw_cf.q, qs)))
    x, pi = s.zeros(61, 1), s.zeros(61, 1)
    x[19], pi[7] = EPS/29, EPS/31
    kappa = s.Matrix([EPS*s.Rational(j+1, 43) for j in range(6)])
    A = raw.A.copy(); A[0, :] = s.zeros(1, 12)
    PiA = s.zeros(3, 12)
    PiA[0, 0], PiA[1, 6], PiA[2, 1] = EPS/37, 2*EPS/41, -EPS/47
    E = s.kronecker_product(raw.principals(s.diag(N, 1, 1, 1))[0], s.eye(63))
    p = -s.I*raw.chi0*E
    section = graph.embed(x, pi, A, PiA, [s.zeros(3, 12)]*3, raw.psi0, p)
    source_current = raw.current(e, raw.psi0, raw.chi0)
    primary_A, primary_S = raw_cf.at(raw_cf.A, qs), raw_cf.at(raw_cf.S, qs)
    Pie = rational(primary_A*kappa+primary_S*source_current[:6, :])
    eq(raw_cf.at(raw_cf.Z, qs).T*Pie+source_current[:6, :], s.zeros(6, 1))
    eq(Pie[(0, 4, 8, 12), :], s.zeros(4, 1))
    eq(graph.select.T*section['current']['total'], s.zeros(9, 1))
    original = graph.original_bulk_H(e, Pie, section, [s.zeros(70, 1)]*3, A, PiA,
        s.zeros(3, 48), [s.zeros(3, 12)]*3, raw.psi0, p)
    nongauge = s.cancel(sum(v for name, v in original['components'].items() if name != 'gauge'))
    a = [s.cancel(s.diff(nongauge, y)) for y in ys]
    for coefficient in a: assert not(set(ys)&coefficient.free_symbols)
    zero(nongauge-sum(y*c for y, c in zip(ys, a)))
    B = raw.curvature(A)[3:, :]
    Egram, Cgram, Mgram = PiA*raw.Gram.inv()*PiA.T, PiA*B.T, B*raw.Gram*B.T
    data = [*a, *qs, *[Egram[i, j] for i, j in SYMMETRIC], *list(Cgram), *[Mgram[i, j] for i, j in SYMMETRIC]]
    supplied = [s.sympify(value, locals={str(EPS): EPS}) for value in candidate['generated_input_germ']]
    eq(s.Matrix(data), s.Matrix(supplied))
    H = s.cancel(original['bulk'])
    expected = s.sympify(candidate['actual_source_canonical_germ']['whole_original_Hamiltonian'],
        locals={str(v): v for v in (*ys, EPS)})
    zero(H-expected)
    residual = graph.kernel.T*section['current']['total']
    eq(residual, decode(candidate['actual_source_canonical_germ']['residual_stabilizer_Gauss'], {str(EPS): EPS}))
    assert residual.todok()
    return H, data, residual, raw.hashes


def polynomial_substitute(poly, values, modulus):
    result = s.Poly(0, EPS, domain=DOMAIN)
    for powers, coefficient in poly.terms():
        term = s.Poly(coefficient, EPS, domain=DOMAIN)
        for value, power in zip(values, powers):
            if power: term = (term*value**power).rem(modulus)
        result += term
    return result.rem(modulus)


def rational_series(expression, variables, values, order):
    numerator, denominator = s.fraction(s.cancel(expression))
    modulus = s.Poly(EPS**(order+1), EPS, domain=DOMAIN)
    top = polynomial_substitute(s.Poly(numerator, *variables, domain=DOMAIN), values, modulus)
    bottom = polynomial_substitute(s.Poly(denominator, *variables, domain=DOMAIN), values, modulus)
    assert bottom.nth(0) != 0
    inverse = s.invert(bottom, modulus)
    assert (bottom*inverse).rem(modulus).as_expr() == 1
    return (top*inverse).rem(modulus)


def source_order7(H, ys, candidate):
    F = [-s.diff(H, y) for y in ys]
    source_point = {EPS: 0, **dict(zip(ys, (N, 0, 0, 0)))}
    eq(s.Matrix(F).subs(source_point), s.zeros(4, 1))
    J = rational(s.Matrix(F).jacobian(ys).subs(source_point))
    expected_J = s.diag(-s.sqrt(30), *[-2*s.sqrt(30)/3]*3)
    eq(J, expected_J); zero(J.det()-s.Rational(800, 3))
    eq(J, decode(candidate['source_Jacobian']))
    order = 7
    y = [s.Poly(v, EPS, domain=DOMAIN) for v in (N, 0, 0, 0)]
    eps_poly = s.Poly(EPS, EPS, domain=DOMAIN)
    coefficients = []
    for n in range(1, order+1):
        force = s.Matrix([rational_series(f, (*ys, EPS), [*y, eps_poly], n).nth(n) for f in F])
        # Solve the complete actual Jacobian using LU, independently of the
        # producer's preselected diagonal element division.
        step = J.inv(method='DM')*(-force)
        for a in range(4): y[a] += s.Poly(step[a]*EPS**n, EPS, domain=DOMAIN)
        for f in F: assert rational_series(f, (*ys, EPS), [*y, eps_poly], n).is_zero
        coefficients.append([str(s.simplify(value)) for value in step])
    reduced = rational_series(H, (*ys, EPS), [*y, eps_poly], order)
    supplied = candidate['actual_order7']
    for actual, saved_row in zip(y, supplied['temporal_coefficients']):
        for n, expected in enumerate(saved_row): zero(actual.nth(n)-s.sympify(expected))
    for n, expected in enumerate(supplied['reduced_Hamiltonian_coefficients']): zero(reduced.nth(n)-s.sympify(expected))
    # A different four-dimensional perturbation provides another finite
    # regression. The universal law is justified separately by rational
    # composition at a unit denominator; this test is not its formal proof.
    delta = s.Matrix([s.Rational(-2, 13), s.Rational(5, 17), s.Rational(7, 19), s.Rational(-11, 23)])
    changed = [value+s.Poly(delta[a]*EPS**order, EPS, domain=DOMAIN) for a, value in enumerate(y)]
    for a, f in enumerate(F):
        defect = rational_series(f, (*ys, EPS), [*changed, eps_poly], order)
        zero(defect.nth(order)-(J*delta)[a])
        assert all(defect.nth(n) == 0 for n in range(order))
    return J, coefficients, [str(s.simplify(reduced.nth(n))) for n in range(order+1)]


def main():
    began = time.monotonic(); candidate_path = HERE/'source_quantum_temporal_symbol.json'
    candidate = json.loads(candidate_path.read_text()); checks = check_bindings(candidate)
    assert candidate['root'] == ROOT_ID
    raw_cf, ys, e, counts = all_original_affinity()
    assert counts == candidate['generic_time_affinity_coefficient_counts']
    _, block = original_gauge_compression(e, ys)
    print('PASS raw generic sixq/fourtime nongauge affinity, ordered current slots and original native Legendre compression', flush=True)
    H, data, residual, hashes = actual_compression(raw_cf, ys, e, candidate)
    assert hashes == candidate['source_sha256']
    # The21 source Gram values contract the independently obtained6x6 Hessian.
    Egram = s.zeros(3); Mgram = s.zeros(3)
    for (i, j), value in zip(SYMMETRIC, data[10:16]): Egram[i, j] = Egram[j, i] = value
    for (i, j), value in zip(SYMMETRIC, data[25:31]): Mgram[i, j] = Mgram[j, i] = value
    Cgram = s.Matrix(3, 3, data[16:25])
    block = block.subs(dict(zip(raw_cf.q, data[4:10])))
    contraction = sum(block[i, j]*Egram[i, j]/2+block[i, j+3]*Cgram[i, j]+
        block[i+3, j+3]*Mgram[i, j]/2 for i in range(3) for j in range(3))
    zero(H-sum(y*a for y, a in zip(ys, data[:4]))-contraction)
    print('PASS actual full canonical/primary/broken-Gauss germ, source31 arguments and whole raw Hamiltonian', flush=True)
    J, steps, Hseries = source_order7(H, ys, candidate)
    print('PASS independent ordinary-derivative four constraints, Euclidean series inverse, order7 branch and source Hred', flush=True)
    assert candidate['full_quantum_evolution_spectrum_or_lifetime_generated'] is False
    paths = [candidate_path]+[HERE/name for name in ('source_quantum_temporal_symbol.py',
        'independent_source_quantum_temporal_symbol.py', 'ImplicitSourceCoefficients.lean',
        'independent_source_coframe_live_ordering.py', 'independent_source_coframe_legendre.py',
        'independent_source_lorentz_contact.py', 'independent_source_scalar_gauss_reduction.py',
        'independent_source_gauge_legendre.py', 'independent_source_joint_temporal_rates.py',
        'source_temporal_dirac_reduction.json', 'independent_source_temporal_dirac_reduction.json')]
    result = {'root': ROOT_ID, 'source_sha256': hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_COMPLETE_HOMOGENEOUS_TEMPORAL_CLASSICAL_SYMBOL_AND_SOURCE_COEFFICIENT_PRODUCER',
        'scope': candidate['scope'], 'checked_input_bindings': checks, 'candidate_constructor_or_Jet_imported': False,
        'generic_original_affinity_counts': counts, 'all21_original_gauge_Gram_coefficients': True,
        'actual_source_Jacobian': encode(J), 'actual_source_Jacobian_determinant': str(J.det()),
        'all31_actual_canonical_arguments_reconstructed': True,
        'actual_residual_stabilizer_Gauss': encode(residual),
        'actual_order7_independent_steps': steps, 'actual_order7_reduced_Hamiltonian': Hseries,
        'all_order_rational_argument': 'At the fixed source every denominator in the original rational H/F is a unit. For n>=1, changing y by epsilon^n*d changes F modulo epsilon^(n+1) by epsilon^n*(d_y F at source)*d: products use their constant factors, and inversion follows b^-1-a^-1=-(b-a)/(ab). Repeated sums, products and inverses prove the same law for the entire source rational expression. Since det J0=800/3, each next coefficient is uniquely generated from lower ones. This proves truncation compatibility and formal uniqueness; the already signed analytic IFT identifies these coefficients with its local real analytic source branch.',
        'formal_Lean_boundary': 'ImplicitSourceCoefficients.lean certifies generic recursion and uniqueness with axioms propext/Quot.sound. The actual31-parameter rational coefficient law is established by source reconstruction plus the stated rational-algebra argument, not installed as a Lean instance. The displayed order7 delta checks are finite regressions, not a universal formal-law proof.',
        'chart_scope': 'Positive source triangular coframe and nonzero original scalar/Gauss/electric denominators, near the original source. Four temporal second-class equations are removed; the actual fixture retains the displayed three stabilizer Gauss values. Full stabilizer quantum descent is not silently asserted.',
        'quantum_scope': 'Actual commuting reduced classical analytic symbol before quantization. No noncommuting root substitution, common quantum evolution, interacting measure, proton pole or lifetime is generated by this receipt.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_quantum_temporal_symbol.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent source temporal reduced symbol', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
