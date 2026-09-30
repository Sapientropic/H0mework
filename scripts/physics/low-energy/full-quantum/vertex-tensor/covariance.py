#!/usr/bin/env python3
"""Original cubic-current Hessians and their full-field rotation transport.

Q_a is the second derivative of the original current, not the linearized
field-equation Hessian. The native circle representation and the constant
trilinear Lie identity generate full parameter covariance by a linear ODE.
"""
import json
from pathlib import Path
import time
import sympy as s
import compute

HERE = Path(__file__).resolve().parent
t = s.symbols('t', real=True)


def clean(matrix):
    return s.SparseMatrix(matrix.rows, matrix.cols, {key: value for key, raw in s.SparseMatrix(matrix).todok().items()
        if (value := s.expand(raw)) != 0})


def source_hessians(context):
    idx, e0, blocks = context['indices'], context['coframe'], context['blocks']
    pi, ci, x0, y0 = context['primal_indices'], context['dual_indices'], context['primal'], context['dual']
    pairs, generators, helper = context['pairs'], context['fundamental'], context['helper']
    adj = {}
    import itertools
    for mu, a in itertools.product(range(4), repeat=2):
        rows = [i for i in range(4) if i != a]
        cols = [i for i in range(4) if i != mu]
        constant, first, second = s.Integer(0), {}, {}
        for permutation in itertools.permutations(range(3)):
            sign = s.Integer((-1)**(mu+a)*helper.parity(permutation))
            positions = [(row, cols[j]) for row, j in zip(rows, permutation)]
            values = [e0[position] for position in positions]
            constant += sign*s.prod(values)
            for k in range(3):
                i = idx['coframe', positions[k]]
                first[i] = first.get(i, 0)+sign*s.prod(values[j] for j in range(3) if j != k)
                for l in range(3):
                    if l == k:
                        continue
                    j = idx['coframe', positions[l]]
                    second[i, j] = second.get((i, j), 0)+sign*values[3-k-l]
        adj[mu, a] = (s.expand(constant), {i: s.expand(v) for i, v in first.items() if s.expand(v) != 0},
            {ij: s.expand(v) for ij, v in second.items() if s.expand(v) != 0})
    result = {}
    for mu, gen in itertools.product(range(4), range(12)):
        entries = {}
        def add(i, j, value):
            if value != 0:
                entries[i, j] = entries.get((i, j), 0)+value
        def cross(i, j, value):
            add(i, j, value)
            add(j, i, value)
        for a in range(4):
            zeroth, first, second = adj[mu, a]
            B = s.SparseMatrix(blocks[gen, a])
            for (i, j), value in B.todok().items():
                cross(ci[i], pi[j], zeroth*value)
            xread, yread = B*x0, y0.T*B
            for ei, coefficient in first.items():
                for i in range(24):
                    cross(ei, ci[i], coefficient*xread[i])
                    cross(ei, pi[i], coefficient*yread[i])
            background = (y0.T*B*x0)[0]
            for (i, j), coefficient in second.items():
                add(i, j, coefficient*background)
        for bi, (rho, sigma) in enumerate(pairs):
            for fi, (a, b) in enumerate(pairs):
                if len({rho, sigma, a, b}) != 4:
                    continue
                wedge = -helper.parity((rho, sigma, a, b))
                for nu, ga in itertools.product(range(4), range(12)):
                    curvature = ((generators[gen]*generators[ga]-generators[ga]*generators[gen]) if (mu == a and nu == b) else s.zeros(7)) + \
                        ((generators[ga]*generators[gen]-generators[gen]*generators[ga]) if (mu == b and nu == a) else s.zeros(7))
                    if curvature.is_zero_matrix:
                        continue
                    for gb in range(12):
                        cross(idx['gauge_B', (bi, gb)], idx['gauge_A', (nu, ga)], wedge*s.trace(generators[gb]*curvature))
        Q = clean(s.SparseMatrix(289, 289, entries))
        assert Q == Q.T
        result[mu, gen] = Q
    return result


def circle_coefficients(certificate):
    scale = s.Integer(certificate['field_constant_denominator'])
    degree = max(len(poly) for _, _, poly in certificate['field_numerator'])-1
    matrices = [s.MutableSparseMatrix(289, 289, {}) for _ in range(degree+1)]
    for i, j, coefficients in certificate['field_numerator']:
        for power, coefficient in enumerate(coefficients):
            if coefficient:
                matrices[power][i, j] = s.Rational(coefficient)/scale
    return [s.SparseMatrix(matrix) for matrix in matrices]


def main():
    start = time.monotonic()
    actual, _, _, _, context = compute.source_tables(generate_tables=False)
    Q = source_hessians(context)
    print('PASS original adjugate matter + BF Hessians', sum(len(m.todok()) for m in Q.values()), flush=True)
    signed = json.loads((HERE/'receipt.json').read_text())
    at = {compute.u: s.Rational(1, 3), compute.q: s.Rational(1, 7)}
    plus = context['leg'].subs(at)
    for label, second in [('same', 1), ('opposite', -1)]:
        minus = context['leg'].subs({compute.u: second*compute.u, compute.q: -compute.q}, simultaneous=True).subs(at)
        for row in signed['pairings'][label]['all48']:
            key = tuple(row['coordinate'])
            expected = s.sympify(row['total'], locals={'u': compute.u, 'q': compute.q}).subs(at)
            assert s.simplify((plus.T*Q[key]*minus)[0]-expected) == 0
    print('PASS independent constant Hessians read all96 actual light cubics', flush=True)
    finite = json.loads((compute.BASE/'active-gauge/rotation/finite.json').read_text())
    gauge = {key: context['indices']['gauge_A', key] for key in Q}
    scalar_rows = [i for i, row in enumerate(actual['fields']) if row['group'] == 'scalar_J']
    results = []
    circle_data = {}
    for axis in [1, 2]:
        coefficients = circle_coefficients(finite['certificates'][axis])
        circle_data[axis] = coefficients
        assert coefficients[0] == s.eye(289)
        for matrix in coefficients:
            scalar_increment = matrix.extract(scalar_rows, list(range(289)))*context['leg']
            assert all(s.expand(value) == 0 for value in scalar_increment)
        J = coefficients[1]
        # L=P/(1+t²)^4. The actual coefficient identity is (1+t²)P'−8tP=JP.
        zero = s.zeros(289)
        for power in range(len(coefficients)+1):
            coefficient = lambda degree: coefficients[degree] if 0 <= degree < len(coefficients) else zero
            generated = (power+1)*coefficient(power+1)+(power-1)*coefficient(power-1)-8*coefficient(power-1)-J*coefficient(power)
            assert clean(generated) == zero, (axis, power)
        for power in range(2*len(coefficients)-1):
            inverse_product = sum(((-1)**i*coefficients[i]*coefficients[power-i]
                for i in range(len(coefficients)) if 0 <= power-i < len(coefficients)), zero)
            expected = s.binomial(8, power//2)*s.eye(289) if power % 2 == 0 else zero
            assert clean(inverse_product-expected) == zero, ('source_inverse', axis, power)
        assert all(J[row, col] == 0 for col in gauge.values() for row in range(289) if row not in gauge.values())
        assert all(matrix[row, col] == 0 for matrix in coefficients for col in gauge.values()
            for row in range(289) if row not in gauge.values())
        count = 0
        wrong_inverse_components = 0
        for source, source_index in gauge.items():
            correction = sum((J[target_index, source_index]*Q[target]
                for target, target_index in gauge.items() if J[target_index, source_index] != 0), zero)
            defect = clean(J.T*Q[source]+Q[source]*J+correction)
            assert defect == zero, (axis, source, list(defect.todok().items())[:3])
            if clean(J.T*Q[source]+Q[source]*J-correction) != zero:
                wrong_inverse_components += 1
            count += 1
        assert wrong_inverse_components > 0
        literal_coefficients = 0
        for source, source_index in gauge.items():
            left = [matrix.T*Q[source] for matrix in coefficients]
            for power in range(2*len(coefficients)-1):
                lhs = sum((left[i]*coefficients[power-i]
                    for i in range(len(coefficients)) if 0 <= power-i < len(coefficients)), zero)
                rhs = zero
                for denominator_power in range(5):
                    degree = power-2*denominator_power
                    if 0 <= degree < len(coefficients):
                        rhs += sum((s.binomial(4, denominator_power)*(-1)**degree*
                            coefficients[degree][target_index, source_index]*Q[target]
                            for target, target_index in gauge.items()
                            if coefficients[degree][target_index, source_index] != 0), zero)
                defect = clean(lhs-rhs)
                assert defect == zero, ('literal_cubic', axis, source, power, list(defect.todok().items())[:3])
                literal_coefficients += 1
        print('PASS full source cubic infinitesimal covariance / rational-circle ODE', axis, count, flush=True)
        print('PASS literal full-parameter cubic covariance coefficients', axis, literal_coefficients, flush=True)
        results.append({'axis': axis, 'field_dimension': 289, 'all_current_components': count,
            'generator_nonzero_entries': len(J.todok()), 'representation_initial_identity': True,
            'wrong_source_inverse_sign_nonzero_components': wrong_inverse_components,
            'inverse_original_circle': 'L(t)^-1 = L(-t), verified by all polynomial coefficients',
            'transported_actual_light_scalar_increment_zero': True,
            'literal_full_cubic_matrix_coefficients': literal_coefficients,
            'literal_identity': 'P(t)^T Q_a P(t) = (1+t^2)^4 sum_b P(-t)_ba Q_b; denominator (1+t^2)^8',
            'full_parameter_ODE': '(1+t^2) L_prime(t) = J L(t)',
            'source_cubic_identity': 'J^T Q_a + Q_a J + sum_b J_ba Q_b = 0'})
    y, z = s.symbols('y z', real=True)
    source_index = gauge[1, 1]
    pulled = {key: s.Integer(0) for key in gauge}
    for i, first in enumerate(circle_data[1]):
        for j, second in enumerate(circle_data[2]):
            column = first*second[:, source_index]
            for key in gauge:
                pulled[key] += (-1)**(i+j)*column[gauge[key]]*y**i*z**j
    assert all(s.expand(value) == 0 for (mu, gen), value in pulled.items() if gen not in {0, 1, 6, 7})
    assert all(s.expand(pulled[mu, 6]+pulled[mu, 7]) == 0 for mu in range(4))
    assert all(s.expand(pulled[0, gen]) == 0 for gen in range(12))
    def spatial_numerator(axis, variable):
        return s.SparseMatrix(4, 4, {(i, j): sum(coefficient*variable**power
            for power, coefficient in enumerate(coefficients))
            for i, j, coefficients in finite['certificates'][axis]['spatial_numerator']})
    spatial = spatial_numerator(1, y)*spatial_numerator(2, z)
    normal_numerator = s.expand(spatial[3, 1]**2)
    denominator = (1+y**2)**4*(1+z**2)**4
    assert s.expand(pulled[1, 1]+pulled[2, 0]-(denominator-normal_numerator)) == 0
    assert s.expand((pulled[3, 6]-pulled[3, 7])/2-normal_numerator) == 0
    assert s.expand(pulled[0, 6]) == s.expand(pulled[0, 7]) == 0
    print('PASS literal two-circle fixed A1 pullback: CT+(CL-CT)n1^2, all parameters', flush=True)
    # C(LP,LQ,La) has denominator (1+t²)^12 and numerator degree <=24.
    # Its actual derivative vanishes by the checked Lie tensor identity. The
    # resulting coefficient recurrence determines its entire numerator from C(P,Q,a).
    recurrence = [s.Rational(1), s.Rational(0)]
    for power in range(1, 24):
        recurrence.append(s.cancel((25-power)*recurrence[power-1]/(power+1)))
    assert recurrence == [s.binomial(12, i//2) if i % 2 == 0 else 0 for i in range(25)]
    output = {'scope': 'ORIGINAL_ADJUGATE_MATTER_PLUS_BF_CURRENT_CUBIC_COVARIANCE',
        'source_sha256': actual['source_sha256'], 'current_hessians': 48,
        'nonzero_hessian_entries': sum(len(m.todok()) for m in Q.values()),
        'independent_light_cubic_consumers': 96, 'circles': results,
        'fixed_A1_two_circle_native_projection': {
            'field_action': 'Lz(z) Ly(y)', 'inverse_source': 'Ly(-y) Lz(-z) A1(S01)',
            'spatial_action': 'Ry(y) Rz(z)', 'direction_n1': '(Ry Rz)[3,1]',
            'transverse_weight_numerator': str(s.expand(pulled[1, 1]+pulled[2, 0])),
            'longitudinal_weight_numerator': str(normal_numerator),
            'common_denominator': str(s.expand(denominator)),
            'temporal_source_weights_exactly_zero': True,
            'source_stays_in_original_scalar_annihilating_color_triplet': True,
            'identity': 'C(Lz Ly V_sigma, Lz Ly V_tau)[A1(S01)] = CT+(CL-CT)n1^2; no restriction on u,q,y,z'},
        'trilinear_constant_polynomial_recurrence': {
            'equation': '(n+1) p[n+1] = (25-n) p[n-1]',
            'initial': 'p[0]=C(P,Q,a), p[1]=0',
            'generated_coefficients_relative_to_p0': list(map(str, recurrence)),
            'result': 'P(t)=(1+t^2)^12 C(P,Q,a)'},
        'full_parameter_consequence': 'C(L(t)P,L(t)Q)[a] = C(P,Q)[L(t)^-1 a]',
        'derivation': 'All coefficients of the literal cleared rational matrix identity were checked, along with the original inverse. The independent Lie/ODE checks and finite polynomial recurrence verify the same full-parameter identity a second way. These are the actual adjugate matter and BF cubic-current Hessians, not quadratic equation covariance.',
        'elapsed_seconds': round(time.monotonic()-start, 3)}
    (HERE/'covariance-receipt.json').write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
