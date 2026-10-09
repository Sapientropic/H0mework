#!/usr/bin/env python3
"""Original fixed source through the exact parameter infinity elimination."""
import hashlib
import json
from pathlib import Path
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix

import infinity as inf

HERE = Path(__file__).resolve().parent
FQ = HERE.parent
x, epsilon, a = inf.x, inf.epsilon, inf.a
F = inf.FIELD
ORDER = 6
RETURN_POWER = 2
radicals = [s.Integer(1), s.sqrt(2), s.sqrt(15), s.sqrt(30)]


def add_at(out, degree, value):
    if not value.is_zero_matrix:
        out[degree] = out.get(degree, inf.zero(*value.shape))+value
        if out[degree].is_zero_matrix:
            del out[degree]


def product(left, right, highest):
    result = {}
    for i, A in left.items():
        for j, B in right.items():
            if i+j <= highest and not A.is_zero_matrix and not B.is_zero_matrix:
                add_at(result, i+j, A.matmul(B))
    return result


def extract(series, rows, columns):
    return {power: M.extract(rows, columns) for power, M in series.items()
            if not M.extract(rows, columns).is_zero_matrix}


def solve(series, rhs, columns, trace, original_labels):
    size = series[0].shape[0]
    assert min(rhs, default=1) >= 1
    assert len(series) >= RETURN_POWER+1
    at0 = inf.at_zero(series[0])
    _, pivot_columns = at0.rref()
    rank = len(pivot_columns)
    if not rank:
        assert series[0].is_zero_matrix
        assert min(rhs, default=2) >= 2
        assert len(series) > 1
        trace.append({'dimension': size, 'rank': 0, 'rhs_lowest_power': min(rhs, default=None)})
        return solve(series[1:], {power-1: M for power, M in rhs.items()}, columns, trace, original_labels)
    _, pivot_rows = at0.extract(range(size), pivot_columns).transpose().rref()
    other_rows = [i for i in range(size) if i not in pivot_rows]
    other_columns = [i for i in range(size) if i not in pivot_columns]
    A = [M.extract(pivot_rows, pivot_columns) for M in series]
    inverse = [A[0].inv()]
    for degree in range(1, len(series)):
        value = inf.zero(rank, rank)
        for k in range(1, degree+1):
            if not A[k].is_zero_matrix and not inverse[degree-k].is_zero_matrix:
                value += A[k].matmul(inverse[degree-k])
        inverse.append(-inverse[0].matmul(value))
    upper = len(series)-1+min(0, min(rhs, default=0))
    first = extract(rhs, pivot_rows, range(columns))
    first = product(dict(enumerate(inverse)), first, upper)
    trace.append({'dimension': size, 'rank': rank, 'rhs_lowest_power': min(rhs, default=None),
                  'tracked_highest_power': upper})
    print('actual source infinity pivot', size, rank, 'rhs lower', min(rhs, default=None), 'upper', upper, flush=True)
    if rank == size:
        result = {}
        for power, M in first.items():
            if power > RETURN_POWER:
                continue
            entries = {(pivot_columns[i], j): value for (i, j), value in M.to_dok().items()}
            result[power] = DomainMatrix.from_dok(entries, (size, columns), F)
        return result
    B = {i: M.extract(pivot_rows, other_columns) for i, M in enumerate(series)}
    C = {i: M.extract(other_rows, pivot_columns) for i, M in enumerate(series)}
    inverse_B = product(dict(enumerate(inverse)), B, len(series)-1)
    CB = product(C, inverse_B, len(series)-1)
    remainder = [M.extract(other_rows, other_columns)-CB.get(i, inf.zero(size-rank, size-rank))
                 for i, M in enumerate(series)]
    assert remainder[0].is_zero_matrix
    lower_rhs = extract(rhs, other_rows, range(columns))
    for power, M in product(C, first, upper).items():
        add_at(lower_rhs, power, -M)
    rest = solve(remainder[1:], {power-1: M for power, M in lower_rhs.items()}, columns, trace,
                 [original_labels[i] for i in other_columns])
    # Every exact reduced source starts at tau, and every pivot is invertible
    # at tau=0. Induction makes the actual solution O(tau); its first two
    # coefficients therefore use only these first two back-substitution terms.
    first = {power: M for power, M in first.items() if power <= RETURN_POWER}
    for power, M in product(inverse_B, rest, RETURN_POWER).items():
        add_at(first, power, -M)
    result = {}
    for series_part, labels in [(first, pivot_columns), (rest, other_columns)]:
        for power, M in series_part.items():
            entries = {(labels[i], j): value for (i, j), value in M.to_dok().items()}
            add_at(result, power, DomainMatrix.from_dok(entries, (size, columns), F))
    return result


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
        s.Poly(value, x, a, domain=inf.BASE)
        for (degree,), coefficient in s.Poly(value, x).terms():
            data[2-degree][i, j] = F.from_sympy(coefficient)
    normalized = [DomainMatrix.from_dok(value, (112, 112), F) for value in data]
    source_degree = source['section_source_numerator']['shape'][1]
    rhs_data = {}
    for i, j, text in source['section_source_numerator']['entries']:
        value = s.expand(s.sympify(text, locals={'x': x, 'epsilon': epsilon}).subs(epsilon, 3*s.sqrt(2)*a/10)
                         *diagonal[i]/lapse)
        parts = [value]
        for radical in radicals[1:]:
            coefficient = parts[0].coeff(radical)
            parts[0] -= radical*coefficient
            parts.append(coefficient)
        assert s.expand(sum(r*p for r, p in zip(radicals, parts))-value) == 0
        for index, part in enumerate(parts):
            s.Poly(part, x, a, domain=inf.BASE)
            for (degree,), coefficient in s.Poly(part, x).terms():
                rhs_data.setdefault(2-degree, {})[i, j+index*source_degree] = F.from_sympy(coefficient)
    rhs = {power: DomainMatrix.from_dok(value, (112, 4*source_degree), F) for power, value in rhs_data.items()}
    responses, reports = {}, []
    for component in inf.connected_components(normalized):
        forcing = extract(rhs, component, range(4*source_degree))
        if not forcing:
            reports.append({'indices': component, 'all_parameter_forcing_zero': True})
            continue
        series = [M.extract(component, component) for M in normalized]
        series += [inf.zero(len(component), len(component)) for _ in range(ORDER-2)]
        trace = []
        solution = solve(series, forcing, 4*source_degree, trace, component)
        # The exact analytic Schur identities pay the two coefficients. This
        # additional check reads them back in the original reversed equation.
        residual = product(dict(enumerate(series[:3])), solution, RETURN_POWER)
        for power, M in forcing.items():
            add_at(residual, power, -M)
        assert not residual, ('original source Laurent residual', sorted(residual))
        for power, M in solution.items():
            entries = {(component[i], j): value for (i, j), value in M.to_dok().items()}
            add_at(responses, power, DomainMatrix.from_dok(entries, (112, 4*source_degree), F))
        assert min(solution, default=1) >= 1
        reports.append({'indices': component, 'trace': trace,
            'all_exact_reduced_sources_vanish_at_tau_zero': True,
            'exact_analytic_solution_vanishes_at_tau_zero': True,
            'source_coefficients_generated_through_tau_power': RETURN_POWER,
            'original_reversed_residual_order_at_least': RETURN_POWER+1})
    output = {'scope': 'STRIKE_ACTUAL_PARAMETER_SOURCE_LAURENT_SOLUTION',
        'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'order': ORDER,
        'column_convention': 'Column j+r*6 is sqrt-basis[r] times U^j, all divided by D(U).',
        'radical_basis': list(map(str, radicals)), 'components': reports,
        'section_coefficients': {str(power): inf.encoded(M) for power, M in responses.items() if power <= 2},
        'nonpositive_section_powers': sorted(power for power in responses if power <= 0),
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'proper.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS original source infinity solution; nonpositive powers', output['nonpositive_section_powers'], output['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
