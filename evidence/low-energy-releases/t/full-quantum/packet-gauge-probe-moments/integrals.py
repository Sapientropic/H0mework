#!/usr/bin/env python3
"""Whole-halfline J transforms at the actual preparation and Sylvester poles."""
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import importlib.util
import json
from math import factorial
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]


def main():
    began = time.monotonic()
    kernel_path = HERE/'kernels.json'
    data = json.loads(kernel_path.read_text())
    operators = json.loads((HERE/'operators.json').read_text())
    exact_path = FQ/'packet-noise/source-kernel-receipt.json'
    exact = json.loads(exact_path.read_text())['exact_source']
    interval_path = FQ/'packet-band-kernel/intervals.py'
    spec = importlib.util.spec_from_file_location('probe_moments_intervals', interval_path)
    interval = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(interval)
    Box, cmul = interval.Box, interval.complex_product
    czero, cone = (Box(0), Box(0)), (Box(1), Box(0))
    def add(*values):
        return sum((v[0] for v in values), Box(0)), sum((v[1] for v in values), Box(0))
    def scale(value, coefficient):
        return value[0]*coefficient, value[1]*coefficient
    def star(value):
        return value[0], -value[1]
    def divide(left, right):
        norm = right[0].square()+right[1].square()
        assert norm.lo > 0
        product = cmul(left, star(right))
        return product[0]/norm, product[1]/norm
    def power(value, degree):
        if degree < 0:
            return divide(cone, power(value, -degree))
        result = cone
        for _ in range(degree):
            result = cmul(result, value)
        return result

    @lru_cache(None)
    def evaluate(expression):
        if expression.is_Rational:
            return Box(F(int(expression.p), int(expression.q))), Box(0)
        if expression == s.I:
            return Box(0), Box(1)
        if expression.is_Add:
            return add(*(evaluate(value) for value in expression.args))
        if expression.is_Mul:
            result = cone
            for value in expression.args:
                result = cmul(result, evaluate(value))
            return result
        if expression.is_Pow:
            base, exponent = expression.args
            if exponent.is_Integer:
                return power(evaluate(base), int(exponent))
            assert exponent == s.Rational(1, 2) and base.is_Rational and base > 0
            return Box(F(int(base.p), int(base.q))).sqrt(), Box(0)
        raise AssertionError(expression)

    x, y = s.symbols('x y', real=True)
    number = s.QQ.algebraic_field(s.sqrt(15), s.I)
    N, omega = map(s.sympify, [exact['lapse'], exact['frequency']])
    N2 = s.simplify(N*N)
    masses = [s.Integer(0), s.simplify((1-3*omega**2+4*s.I*omega)/N2),
              s.simplify((1-3*omega**2-4*s.I*omega)/N2)]
    source_D = sum(s.sympify(value)*x**powers[3] for powers, value in operators['blocks'][0]['D'])
    coefficient, factors = s.factor_list(s.Poly(source_D, x, domain=s.QQ_I))
    assert sum(f.degree()*multiplicity for f, multiplicity in factors) == 4
    frequency_masses = []
    for factor, multiplicity in factors:
        assert factor.degree() == multiplicity == 1
        # The circuit uses x=|physical p|²/2; its x+mass pole becomes y+2mass.
        mass = s.expand(2*factor.nth(0)/factor.nth(1))
        frequency_masses.extend([mass, s.conjugate(mass)])
    for mass in frequency_masses:
        if mass not in masses:
            masses.append(mass)
    assert len(masses) == 11
    decompositions = {}
    all_texts = sorted(set(text for row in data['weights'] for text in row['radical_components']))
    for text in all_texts:
        expression = s.sympify(text, locals={'x': y/2})
        numerator, denominator = expression.as_numer_denom()
        P, Q = s.Poly(numerator, y, domain=number), s.Poly(denominator, y, domain=number)
        quotient, remainder = P.div(Q)
        assert quotient.is_zero or quotient.degree() == 0
        poles = []
        rebuilt = quotient*Q
        accounted = s.Poly(1, y, domain=number)
        for mass in masses:
            linear = s.Poly(y+mass, y, domain=number)
            remaining, multiplicity = Q, 0
            while True:
                reduced, residual = remaining.div(linear)
                if not residual.is_zero:
                    break
                multiplicity += 1
                remaining = reduced
            if multiplicity == 0:
                continue
            assert mass != 0 or multiplicity == 1
            accounted *= linear**multiplicity
            root = number.from_sympy(-mass)
            pp, qp = remainder.rep, remaining.rep
            pjet, qjet = [], []
            for j in range(multiplicity):
                pjet.append(pp.eval(root)/number.convert(factorial(j)))
                qjet.append(qp.eval(root)/number.convert(factorial(j)))
                pp, qp = pp.diff(), qp.diff()
            assert qjet[0] != number.zero
            jet = []
            for j in range(multiplicity):
                value = (pjet[j]-sum((qjet[k]*jet[j-k] for k in range(1, j+1)), number.zero))/qjet[0]
                jet.append(value)
                order = multiplicity-j
                scalar = number.to_sympy(value)
                poles.append({'mass_squared': str(mass), 'order': order, 'coefficient': str(scalar)})
                rebuilt += Q.exquo(linear**order).mul_ground(scalar)
        assert accounted.degree() == Q.degree()
        assert rebuilt == P
        decompositions[text] = {'constant': str(quotient.nth(0)), 'poles': poles,
            'original_rational_weight_identity': True}
    max_order = max(pole['order'] for record in decompositions.values() for pole in record['poles'])
    print('PASS all actual radial denominators and exact partial fractions; poles', len(masses),
          'maximum order', max_order, flush=True)

    kap = s.Symbol('kap')
    J = s.symbols('J0:'+str(max_order))
    transforms = {1: J[0]}
    for order in range(1, max_order):
        value = transforms[order]
        diff = s.diff(value, kap)+sum(s.diff(value, J[j])*J[j+1] for j in range(max_order-1))
        transforms[order+1] = s.expand(-diff/(2*order*kap))
    degree = 130
    tail = F(2, 5)*F(3**14)*F(14**(degree+1), factorial(degree+1))
    pole_values = {}
    pole_records = []
    for mass in masses[1:]:
        mr, mi = evaluate(mass)
        assert mi.lo > 0 or mi.hi < 0
        modulus = (mr.square()+mi.square()).sqrt()
        assert modulus.hi < 49
        kr = ((modulus+mr)/2).sqrt()
        ki = ((modulus-mr)/2).sqrt()
        if mi.hi < 0:
            ki = -ki
        assert kr.lo > 0
        kappa = kr, ki
        derivatives = [czero for _ in range(max_order)]
        kpower = cone
        for n in range(degree+1):
            for j in range(max_order):
                moment = F(3*2**(n+j+2), (n+j+2)*(n+j+3)*(n+j+5))
                derivatives[j] = add(derivatives[j], scale(kpower, (-1)**j*moment/F(factorial(n))))
            kpower = cmul(kpower, (-kr, -ki))
        derivatives = [tuple(value.grow(2**j*tail) for value in entry) for j, entry in enumerate(derivatives)]
        def binding_value(expression):
            if expression == kap:
                return kappa
            if expression in J:
                return derivatives[J.index(expression)]
            if expression.is_Rational or expression == s.I:
                return evaluate(expression)
            if expression.is_Add:
                return add(*(binding_value(v) for v in expression.args))
            if expression.is_Mul:
                result = cone
                for v in expression.args:
                    result = cmul(result, binding_value(v))
                return result
            if expression.is_Pow and expression.exp.is_Integer:
                return power(binding_value(expression.base), int(expression.exp))
            raise AssertionError(expression)
        for order in range(1, max_order+1):
            pole_values[str(mass), order] = binding_value(transforms[order])
        pole_records.append({'mass_squared': str(mass), 'kappa_real': kr.record(),
            'kappa_imaginary': ki.record(), 'true_Re_kappa_positive': True, 'abs_kappa_lt7': True})
    pole_values['0', 1] = Box(F(2, 5)), Box(0)

    @lru_cache(None)
    def integrate_component(text):
        record = decompositions[text]
        answer = evaluate(s.sympify(record['constant']))
        for pole in record['poles']:
            answer = add(answer, cmul(evaluate(s.sympify(pole['coefficient'])),
                         pole_values[pole['mass_squared'], pole['order']]))
        return answer

    radicals = [1, s.sqrt(2), s.sqrt(15), s.sqrt(30)]
    integrated = {}
    for row in data['weights']:
        value = czero
        for radical, text in zip(radicals, row['radical_components']):
            value = add(value, cmul(evaluate(s.sympify(radical)), integrate_component(text)))
        integrated[row['name']] = value
    n2 = integrated['packet_norm'][0]
    assert n2.lo > 0 and integrated['packet_norm'][1].lo <= 0 <= integrated['packet_norm'][1].hi
    original_norm = json.loads((FQ/'packet-current-hessian/integrals.json').read_text())['raw_filtered_norm_squared']['rational']
    intersection = n2.intersect(Box(*original_norm))
    n2 = intersection
    for name, value in integrated.items():
        if name != 'packet_norm':
            integrated[name] = value[0]/n2, value[1]/n2
    def mu(kind, suffix):
        return integrated['mean_'+kind+'_'+suffix]
    def product(left, right):
        return cmul(star(left), right)
    def output(value):
        return {'real': value[0].record(), 'imaginary': value[1].record()}
    moments = []
    for family in ['N0', 'N1']:
        for row in data['weights']:
            name = row['name']
            if not name.startswith(family+'_'):
                continue
            location, axes = name.split('_')[1:]
            if location == 'right':
                left, right = 'base', axes
            elif location == 'left':
                left, right = axes, 'base'
            else:
                left, right = axes[0], axes[1]
            mean = product(mu('B', left), mu('B', right)) if family == 'N0' else add(
                product(mu('C', left), mu('B', right)), product(mu('B', left), mu('C', right)))
            raw_value = integrated[name]
            connected = add(raw_value, (-mean[0], -mean[1]))
            moments.append({'name': name, 'raw': output(raw_value), 'mean': output(mean),
                            'connected': output(connected)})
            if location == 'mixed' and axes[0] == axes[1]:
                assert raw_value[1].lo <= 0 <= raw_value[1].hi
                if family == 'N0':
                    assert connected[0].lo > 0
            if location == 'right' and axes in ['00', '11', '22']:
                print(family, axes, 'connected real', connected[0].decimals(22),
                    'imag', connected[1].decimals(22), flush=True)
    result = {'scope': 'STRIKE_STRICT_FULL_TIME_SOURCE_PROBE_GRAM_HESSIAN_INTEGRALS',
        'source_sha256': data['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [kernel_path, HERE/'operators.json', exact_path, interval_path,
                FQ/'packet-current-hessian/integrals.json']},
        'measure': 'whole original physical d³p/(2pi)³; weight x is evaluated at |p|²/2, without changing the measure or packet',
        'new_frequency_poles_generated_from_actual_Sylvester_D': list(map(str, frequency_masses)),
        'all_poles': pole_records, 'partial_fractions': decompositions,
        'maximum_pole_order': max_order, 'pole_transforms': {str(k): str(v) for k, v in transforms.items()},
        'J_moments': '3*2^(j+2)/[(j+2)(j+3)(j+5)]',
        'exponential_series_degree': degree, 'uniform_J_derivative_tail': '2^j*(2/5)*3^14*14^131/131!',
        'uniform_J_tail_exact': str(tail), 'no_UV_or_time_tail_cutoff': True,
        'raw_filtered_norm_squared': n2.record(),
        'actual_complex_mean_jets': {name: output(value) for name, value in integrated.items() if name.startswith('mean_')},
        'all_two_probe_Gram_jets': moments,
        'fixed_P_after_whole_source_integral': True,
        'physical_frequency': data['physical_frequency'],
        'new_Lean_declarations': 0, 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'integrals.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS whole-halfline actual mean and complete two-probe source moments', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
