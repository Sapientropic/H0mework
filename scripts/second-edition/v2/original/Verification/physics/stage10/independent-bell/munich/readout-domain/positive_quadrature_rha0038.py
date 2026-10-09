"""Positive dyadic quadrature checked on the complete polynomial basis.

Legendre roots only propose nodes. Exact integer Chebyshev moments determine
the price; a monomial construction independently checks the integration rule.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json

SCHEMA = 'stage10-positive-complete-polynomial-quadrature/rha0038'


def require(value, reason):
    if not value: raise ValueError(reason)


def rounded(value, bits):
    return Q(round(Q(value)*(1 << bits)), 1 << bits)


def upper(value, bits):
    value = Q(value)*(1 << bits)
    return Q(-((-value.numerator)//value.denominator), 1 << bits)


def legendre(x, n, bits):
    before, current = Q(1), x
    for k in range(2, n+1):
        before, current = current, rounded(((2*k-1)*x*current-(k-1)*before)/k, bits)
    return current, rounded(n*(x*current-before)/(x*x-1), bits)


def propose(points=160, degree=296, bits=192):
    import numpy as np
    require(type(points) is int and 2 <= points <= 256 and type(degree) is int and 0 <= degree <= 512 and
            type(bits) is int and 160 <= bits <= 384, 'bounded complete quadrature proposal required')
    guesses, _ = np.polynomial.legendre.leggauss(points); rows = []
    for guess in guesses:
        x = Q(str(float(guess)))
        for _ in range(8):
            value, derivative = legendre(x, points, bits+64)
            x = rounded(x-value/derivative, bits+64)
        x = rounded(x, bits); _, derivative = legendre(x, points, bits+64)
        weight = rounded(1/((1-x*x)*derivative*derivative), bits)
        rows.append([int(x*(1 << bits)), int(weight*(1 << bits))])
    return {'schema': SCHEMA, 'points': points, 'degree': degree, 'bits': bits,
            'unit_interval_rule': '(x+1)/2 with weights summing approximately to one',
            'nodes_and_weights': sorted(rows), 'root_solver_correctness_assumed': False}


def polynomial_basis(degree):
    before, current = [1], [0, 1]
    yield before
    if degree: yield current
    for _ in range(1, degree):
        following = [0]+[2*x for x in current]
        for k, value in enumerate(before): following[k] -= value
        before, current = current, following
        yield current


def check(grid, *, maximum_defect=Q(1, 1 << 144)):
    require(type(grid) is dict and grid.get('schema') == SCHEMA and
            grid.get('root_solver_correctness_assumed') is False, 'closed quadrature witness required')
    n, degree, bits = (grid[k] for k in ('points', 'degree', 'bits'))
    require(type(bits) is int and 160 <= bits <= 384, 'bounded dyadic quadrature precision required')
    quantum = 1 << bits
    rows = grid['nodes_and_weights']
    require(type(n) is int and 2 <= n <= 256 and type(degree) is int and 0 <= degree <= 512 and
            type(bits) is int and 160 <= bits <= 384 and type(rows) is list and len(rows) == n and
            all(type(r) is list and len(r) == 2 and all(type(x) is int for x in r) and
                -quantum < r[0] < quantum and r[1] > 0 for r in rows) and
            rows == sorted(rows) and len({r[0] for r in rows}) == n,
            'complete distinct interior nodes and positive dyadic weights required')
    require(Q(maximum_defect) >= 0, 'nonnegative quadrature accuracy required')
    x, weights = zip(*rows); before = [1]*n; current = list(x); scale = 1
    moments, records = [], []
    for k, coefficients in enumerate(polynomial_basis(degree)):
        if k == 0: values = before
        elif k == 1: values = current
        else:
            before, current = current, [2*a*b-quantum*quantum*c for a,b,c in zip(x,current,before)]
            values = current
        if k: scale *= quantum
        moment = Q(sum(w*t for w,t in zip(weights,values)), quantum*scale)
        integral = Q(0) if k % 2 else Q(1, 1-k*k)
        independent_integral = sum((Q(a, j+1) for j,a in enumerate(coefficients) if j % 2 == 0), Q(0))
        require(independent_integral == integral, 'independent monomial integration disagrees')
        moments.append(moment)
        records.append({'degree': k, 'moment_defect_upper': str(upper(abs(moment-integral),bits))})
    # Monomial moments and integer polynomial evaluation do not use the
    # primary Chebyshev recurrence at the selected complete source columns.
    powers = [1]*n; monomials = []; scale = 1
    for k in range(degree+1):
        if k: powers = [a*b for a,b in zip(powers,x)]; scale *= quantum
        monomials.append(Q(sum(w*t for w,t in zip(weights,powers)), quantum*scale))
    selected = sorted({0, degree//2, degree}); independent = []
    for k, coefficients in enumerate(polynomial_basis(degree)):
        if k in selected:
            value = sum((a*m for a,m in zip(coefficients,monomials)),Q(0))
            require(value == moments[k], 'independent exact quadrature moment disagrees')
            independent.append(k)
    maximum = max(Q(r['moment_defect_upper']) for r in records)
    return {'schema': SCHEMA+'/checked', 'complete_basis_degree': degree, 'complete_basis_columns': degree+1,
        'positive_node_count': n, 'dyadic_bits': bits, 'moment_defects': records,
        'maximum_moment_defect_upper': str(maximum), 'registered_maximum_defect': str(maximum_defect),
        'registered_accuracy_passed': maximum <= maximum_defect,
        'independent_monomial_integrals_checked': degree+1, 'independent_node_moments_checked': independent,
        'absolute_weight_mass': str(Q(sum(weights),quantum)), 'root_solver_correctness_assumed': False}


if __name__ == '__main__':
    p=argparse.ArgumentParser(); p.add_argument('--output',type=Path,required=True)
    p.add_argument('--points',type=int,default=160); p.add_argument('--degree',type=int,default=296)
    args=p.parse_args(); grid=propose(args.points,args.degree); checked=check(grid)
    require(checked['registered_accuracy_passed'], 'quadrature accuracy gate failed')
    with args.output.open('x') as handle: json.dump({'grid':grid,'checked':checked},handle,sort_keys=True);handle.write('\n')
    print(json.dumps({k:checked[k] for k in ('positive_node_count','complete_basis_columns','maximum_moment_defect_upper')}))
