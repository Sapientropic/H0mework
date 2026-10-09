#!/usr/bin/env python3
"""Exact parameter-dependent Schur expansion at infinite frequency."""
import hashlib
import json
from pathlib import Path
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix

HERE = Path(__file__).resolve().parent
FQ = HERE.parent
x, epsilon, a = s.symbols('x epsilon a', real=True)
BASE = s.QQ_I
FIELD = BASE.frac_field(a)
ORDER = 4


def zero(rows, columns):
    return DomainMatrix.zeros((rows, columns), FIELD)


def at_zero(M):
    result = {}
    for ij, value in M.to_dok().items():
        numerator = value.numer.get((0,), BASE.zero)
        denominator = value.denom.get((0,), BASE.zero)
        assert denominator, ('source pivot has pole at the original parameter', ij)
        result[ij] = numerator/denominator
    return DomainMatrix.from_dok(result, M.shape, BASE)


def encoded(M):
    return {'shape': list(M.shape), 'entries': [[i, j, str(FIELD.to_sympy(value))]
            for (i, j), value in sorted(M.to_dok().items())]}


def connected_components(M):
    adjacency = [set() for _ in range(M[0].shape[0])]
    for coefficient in M:
        for i, j in coefficient.to_dok():
            adjacency[i].add(j)
            adjacency[j].add(i)
    seen, result = set(), []
    for initial in range(len(adjacency)):
        if initial in seen:
            continue
        current, remaining = set(), [initial]
        while remaining:
            index = remaining.pop()
            if index not in current:
                current.add(index)
                remaining.extend(adjacency[index]-current)
        result.append(sorted(current))
        seen |= current
    return result


def eliminate(series, label):
    dimension = series[0].shape[0]
    size, valuation, steps = dimension, 0, []
    while size:
        original_constant = at_zero(series[0])
        _, columns = original_constant.rref()
        rank = len(columns)
        if rank == 0:
            assert series[0].is_zero_matrix, ('generic leading rank increased', label, valuation)
            steps.append({'size': size, 'rank': 0, 'whole_leading_coefficient_zero': True})
            valuation += size
            series = series[1:]
            assert series, ('insufficient actual infinity order', label)
            print('exact zero leading block', label, size, flush=True)
            continue
        _, rows = original_constant.extract(range(size), columns).transpose().rref()
        other_rows = [i for i in range(size) if i not in rows]
        other_columns = [i for i in range(size) if i not in columns]
        A = [M.extract(rows, columns) for M in series]
        pivot_inverse = A[0].inv()
        assert A[0].matmul(pivot_inverse) == DomainMatrix.eye((rank, rank), FIELD)
        determinant = A[0].det()
        assert determinant
        steps.append({'size': size, 'rank': rank, 'pivot_rows': list(rows), 'pivot_columns': list(columns),
                      'pivot': encoded(A[0]), 'pivot_determinant': str(FIELD.to_sympy(determinant)),
                      'pivot_inverse': encoded(pivot_inverse)})
        if rank == size:
            break
        B = [M.extract(rows, other_columns) for M in series]
        C = [M.extract(other_rows, columns) for M in series]
        D = [M.extract(other_rows, other_columns) for M in series]
        inverse = [pivot_inverse]
        for degree in range(1, len(series)):
            coefficient = zero(rank, rank)
            for index in range(1, degree+1):
                if not A[index].is_zero_matrix and not inverse[degree-index].is_zero_matrix:
                    coefficient += A[index].matmul(inverse[degree-index])
            inverse.append(-pivot_inverse.matmul(coefficient))
        product = []
        for degree in range(len(series)):
            coefficient = zero(size-rank, rank)
            for index in range(degree+1):
                if not C[index].is_zero_matrix and not inverse[degree-index].is_zero_matrix:
                    coefficient += C[index].matmul(inverse[degree-index])
            product.append(coefficient)
        remainder = []
        for degree in range(len(series)):
            coefficient = D[degree]
            for index in range(degree+1):
                if not product[index].is_zero_matrix and not B[degree-index].is_zero_matrix:
                    coefficient -= product[index].matmul(B[degree-index])
            remainder.append(coefficient)
        assert remainder[0].is_zero_matrix, ('generic infinity rank differs from original', label, rank)
        steps[-1]['generic_constant_schur_zero'] = True
        size -= rank
        valuation += size
        series = remainder[1:]
        assert series, ('insufficient actual infinity order', label)
        print('exact infinity Schur', label, 'pivot', rank, 'remaining', size, flush=True)
    return {'indices': label, 'dimension': dimension, 'infinity_multiplicity': valuation,
            'exact_frequency_degree_for_small_parameter': 2*dimension-valuation, 'steps': steps}


def main():
    began = time.monotonic()
    path = HERE/'source.json'
    source = json.loads(path.read_text())
    old = json.loads((FQ/'packet-gauge-causal/source.json').read_text())
    scales = {i: s.sympify(value) for i, j, value in old['scales103']['entries'] if i == j}
    diagonal = [s.Integer(1)]*9+[scales[i] for i in range(103)]
    lapse = 3*s.sqrt(30)/25
    data = [{}, {}, {}]
    for i, j, text in source['complete112']['entries']:
        value = s.expand(s.sympify(text, locals={'x': x, 'epsilon': epsilon}).subs(epsilon, 3*s.sqrt(2)*a/10)
                         *diagonal[i]*diagonal[j]/lapse)
        s.Poly(value, x, a, domain=BASE)
        for (degree,), coefficient in s.Poly(value, x).terms():
            data[2-degree][i, j] = FIELD.from_sympy(coefficient)
    normalized = [DomainMatrix.from_dok(value, (112, 112), FIELD) for value in data]
    # A constant permutation exposes genuine source components before any
    # frequency inversion; no forcing component is discarded.
    components = connected_components(normalized)
    result = []
    for component in components:
        series = [M.extract(component, component) for M in normalized]
        series += [zero(len(component), len(component)) for _ in range(ORDER-2)]
        result.append(eliminate(series, component))
        print('PASS complete original component at infinity', len(component), result[-1]['exact_frequency_degree_for_small_parameter'], flush=True)
    degree = sum(row['exact_frequency_degree_for_small_parameter'] for row in result)
    original_degree = sum(s.degree(s.sympify(factor['polynomial'], locals={'x': x}), x)*factor['multiplicity']
                          for block in old['all103_source_factor_blocks'] for factor in block['factors'])
    assert degree == original_degree
    output = {'scope': 'STRIKE_EXACT_PARAMETER_INFINITY_SCHUR_AND_CONSTANT_SOURCE_DETERMINANT_DEGREE',
        'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'parameter_identity': 'epsilon=3*sqrt(2)*a/10', 'frequency_identity': 'lambda=(6*sqrt(15)/25)*x',
        'reversed_polynomial': 'tau^2 D M112(1/tau,epsilon) D/N, D=diag(I9,original scales103)',
        'series_order': ORDER, 'components': result, 'complete_frequency_degree': int(degree),
        'analytic_scope': 'Every displayed rational parameter pivot is regular and invertible at a=0; exact zero Schur blocks hold over Q(i)(a), so they persist on a generated nonempty real neighborhood.',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'infinity.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS original complete parameter degree', degree, output['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
