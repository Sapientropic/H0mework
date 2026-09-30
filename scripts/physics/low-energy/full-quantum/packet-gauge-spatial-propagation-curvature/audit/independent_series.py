#!/usr/bin/env python3
"""Exact inverse-table differentiation checks the dyadic source-solution balls."""
import ast
from fractions import Fraction as F
from functools import lru_cache
import gzip
import json
from math import factorial, isqrt
from pathlib import Path
import sys
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
sys.setrecursionlimit(20000)
HERE = Path(__file__).resolve().parent
CANDIDATE = HERE.parent
FQ = CANDIDATE.parent
sys.path.insert(0, str(FQ/'packet-gauge-bilocal'))
import hermitian as h
K, QI = h.K, s.QQ_I
LENGTH = 5


def read(path):
    blob = path.read_bytes()
    return json.loads(gzip.decompress(blob) if path.suffix == '.gz' else blob)


class Jet:
    def __init__(self, values, field):
        self.values = list(values)+[field.zero]*(LENGTH-len(values))
        self.field = field

    def __add__(self, b):
        return Jet([a+c for a, c in zip(self.values, b.values)], self.field)

    def __neg__(self):
        return Jet([-a for a in self.values], self.field)

    def __sub__(self, b):
        return self+-b

    def __mul__(self, b):
        return Jet([sum((self.values[j]*b.values[n-j] for j in range(n+1)), self.field.zero)
                    for n in range(LENGTH)], self.field)

    def inverse(self):
        a, Fld = self.values, self.field
        assert a[0]
        result = [Fld.one/a[0]]
        for n in range(1, LENGTH):
            result.append(-sum((a[j]*result[n-j] for j in range(1, n+1)), Fld.zero)/a[0])
        return Jet(result, Fld)

    def __pow__(self, power):
        if power < 0:
            return self.inverse()**(-power)
        result, value = Jet([self.field.one], self.field), self
        while power:
            if power % 2:
                result = result*value
            value = value*value
            power //= 2
        return result


def integer(node):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -integer(node.operand)
    raise AssertionError(ast.dump(node))


def parse(text, field, symbols):
    def walk(node):
        if isinstance(node, ast.Constant):
            assert isinstance(node.value, int)
            return Jet([field.convert(node.value)], field)
        if isinstance(node, ast.Name):
            if node.id == 'I':
                return Jet([field.from_sympy(s.I) if field == QI else h.scalar(s.I)], field)
            return symbols[node.id]
        if isinstance(node, ast.UnaryOp):
            assert isinstance(node.op, (ast.USub, ast.UAdd))
            value = walk(node.operand)
            return -value if isinstance(node.op, ast.USub) else value
        if isinstance(node, ast.Call):
            assert isinstance(node.func, ast.Name) and node.func.id == 'sqrt' and field == K
            return Jet([h.scalar(s.sqrt(integer(node.args[0])))], field)
        assert isinstance(node, ast.BinOp)
        a = walk(node.left)
        if isinstance(node.op, ast.Pow):
            return a**integer(node.right)
        b = walk(node.right)
        if isinstance(node.op, ast.Add): return a+b
        if isinstance(node.op, ast.Sub): return a-b
        if isinstance(node.op, ast.Mult): return a*b
        if isinstance(node.op, ast.Div): return a*b.inverse()
        raise AssertionError(ast.dump(node))
    return walk(ast.parse(text, mode='eval').body)


def matrix_jets(record, field, symbols, columns=None):
    shape = tuple(record['shape'])
    if columns is None:
        columns = list(range(shape[1]))
    cmap = {j: i for i, j in enumerate(columns)}
    tables = [{} for _ in range(LENGTH)]
    for i, j, raw in record['entries']:
        if j not in cmap:
            continue
        for n, value in enumerate(parse(raw, field, symbols).values):
            if value:
                tables[n][i, cmap[j]] = value
    return [DM.from_dok(v, (shape[0], len(columns)), field) for v in tables]


def mul(a, b):
    field = a[0].domain
    return [sum((a[j].matmul(b[n-j]) for j in range(n+1)),
                DM.zeros((a[0].shape[0], b[0].shape[1]), field)) for n in range(LENGTH)]


def add(a, b, sign=1):
    return [x+y if sign == 1 else x-y for x, y in zip(a, b)]


def to_source(M):
    return h.matrix(*M.shape, [(i, j, h.scalar(QI.to_sympy(v))) for (i, j), v in M.to_dok().items()])


@lru_cache(None)
def enclosure(value, imaginary):
    expression = s.expand(K.to_sympy(value))
    remaining = s.expand(s.im(expression) if imaginary else s.re(expression))
    unit = 2**512
    lo = hi = F(0)
    for number in [30, 15, 2]:
        radical = s.sqrt(number)
        coefficient = remaining.coeff(radical)
        assert coefficient.is_Rational
        a = F(str(coefficient))
        root = isqrt(number*unit*unit)
        ends = [a*F(root, unit), a*F(root+1, unit)]
        lo += min(ends); hi += max(ends)
        remaining = s.expand(remaining-coefficient*radical)
    assert remaining.is_Rational
    return lo+F(str(remaining)), hi+F(str(remaining))


def main():
    started = time.monotonic()
    kernel = read(CANDIDATE/'kernel.json')
    radial = read(CANDIDATE/'radial-inverse.json.gz')
    glob = read(FQ/'packet-gauge-global-transfer/source.json')
    captured = read(HERE/'captured-source-series.json.gz')
    qold = Jet([QI.zero, -QI.one], QI)
    qcur = Jet([QI.zero, QI.one], QI)
    Pentries = [{} for _ in range(LENGTH)]
    for block in radial['blocks']:
        rows = block['indices']
        reciprocal = parse(block['denominator'], QI, {'q': qold}).inverse()
        for i, j, raw in block['numerator']:
            value = parse(raw, QI, {'q': qold})*reciprocal
            for n, coefficient in enumerate(value.values):
                if coefficient:
                    Pentries[n][rows[i], rows[j]] = coefficient
    Pi = [DM.from_dok(v, (112, 112), QI) for v in Pentries]
    operators = {tuple(beta): matrix_jets(rec, QI, {'q': qcur})
                 for beta, rec in kernel['normalized_operator_jets']}
    zero = (0, 0, 0)
    identity = [DM.eye(112, QI)]+[DM.zeros((112, 112), QI) for _ in range(4)]
    assert mul(Pi, operators[zero]) == mul(operators[zero], Pi) == identity
    print('PASS independent AST scalar division of the complete old inverse at negativeq, both identities through order4', flush=True)

    qsrc = Jet([K.zero, K.one], K)
    us = Jet([], K)
    cF = parse(glob['source_coefficient'], K, {}).inverse()
    Fhat = glob['complete_Fhat']
    for n in [2, 4]:
        value = parse(Fhat, K, {'U': us, 'T': qsrc*qsrc})*cF
        us.values[n] = -value.values[n]
    assert not any((parse(Fhat, K, {'U': us, 'T': qsrc*qsrc})*cF).values)
    denominator = parse(kernel['same_source_common_denominator'], K, {'q': qsrc, 'U': us}).inverse()
    selected = [0, 4, 8]
    force = {}
    for beta, record in kernel['normalized_force_jets']:
        value = matrix_jets(record, K, {'q': qsrc, 'U': us}, selected)
        force[tuple(beta)] = [sum((value[j].scalarmul(denominator.values[n-j]) for j in range(n+1)),
                               DM.zeros((112, 3), K)) for n in range(LENGTH)]
    p = list(map(to_source, Pi))
    a = {beta: list(map(to_source, values)) for beta, values in operators.items()}
    result = {zero: mul(p, force[zero])}
    first = [tuple(int(i == j) for i in range(3)) for j in range(3)]
    for beta in first:
        result[beta] = mul(p, add(force[beta], mul(a[beta], result[zero]), -1))
    for i in range(3):
        for j in range(i, 3):
            beta = tuple(x+y for x, y in zip(first[i], first[j]))
            rhs = add(force[beta], mul(a[beta], result[zero]), -1)
            rhs = add(rhs, mul(a[first[i]], result[first[j]]), -1)
            rhs = add(rhs, mul(a[first[j]], result[first[i]]), -1)
            result[beta] = mul(p, rhs)
    unit = 2**captured['precision_bits']
    count = nonzero = 0
    for record in captured['coefficient_rectangles']:
        beta, n = tuple(record['external']), record['radial_degree']
        exact = result[beta][n].to_dok()
        for i, j, re, im, rad in record['rectangles']:
            value = exact.get((i, selected.index(j)), K.zero)
            nonzero += bool(value)
            for imaginary, center in [(False, int(re)), (True, int(im))]:
                lo, hi = enclosure(value, imaginary)
                assert F(center-int(rad), unit) <= lo <= hi <= F(center+int(rad), unit), (beta, n, i, j, imaginary)
            count += 1
    assert count == 11760
    print('PASS every selected actual source coefficient lies in its independently captured256bit rectangle', flush=True)

    # A sharper exact derivative of the geometric-series tail independently
    # checks both forty-order inverse and thirty-six-order solution remainders.
    tails = []
    for filename, order, bound_key, beta_key, contour_key in [
        ('inverse-series.json', 40, 'analytic_tail', 'transverse', 'transverse_contour_bounds'),
        ('solution-series.json', 36, 'true_analytic_tail', 'external_multiindex', 'actual_source_contour_bounds')]:
        data = read(CANDIDATE/filename)
        R = F(data['actual_source_circle_radius'] if order == 40 else data['actual_q_circle'])
        eps = F(data['whole_original_light_radius_q'] if order == 40 else data['light_q_radius'])
        t = eps/R
        contour = {tuple(beta): F(value) for beta, value in data[contour_key]}
        for row in data['uniform_derivatives']:
            beta, derivative = tuple(row[beta_key]), row['radial_order']
            exact_tail = F(0)
            for j in range(derivative+1):
                falling = F(factorial(order+1), factorial(order+1-derivative+j))
                exact_tail += F(int(s.binomial(derivative, j)))*falling*factorial(j)*t**(order+1-derivative+j)/(1-t)**(j+1)
            exact_tail *= contour[beta]/R**derivative
            if order == 40:
                exact_tail *= factorial(beta[0])*factorial(beta[1])
            assert exact_tail <= F(row[bound_key])
        tails.append({'file': filename, 'all_sharper_geometric_derivative_tails_below_candidate': True})
    report = {'passed': True, 'exact_coefficient_algorithm': 'truncated AST scalar division of full rational P_old(-q), followed by explicit first/second inverse-derivative products',
        'both_original112_inverse_coefficients_through_order4': True,
        'implicit_root_coefficients_U_q2_U_q4': [str(K.to_sympy(us.values[n])) for n in [2, 4]],
        'source_profiles': selected, 'source_solution_rectangles_checked': count,
        'nonzero_exact_source_coefficients': nonzero, 'comparison_precision_bits': 512,
        'candidate_rectangle_precision_bits': captured['precision_bits'],
        'all_mixed_total_orders_through4_and_external_order_at_most2': True,
        'tail_consumers': tails, 'seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent-series.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS exact source series and strict complete analytic tails', report['seconds'], flush=True)


if __name__ == '__main__':
    main()
