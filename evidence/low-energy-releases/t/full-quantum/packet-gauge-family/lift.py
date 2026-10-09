#!/usr/bin/env python3
"""Recover actual auxiliary source contacts from the proper section response."""
import hashlib
import json
from pathlib import Path
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix

import infinity as inf
import source as original

HERE = Path(__file__).resolve().parent
x, epsilon, a = inf.x, inf.epsilon, inf.a
F = inf.FIELD
radicals = [s.Integer(1), s.sqrt(2), s.sqrt(15), s.sqrt(30)]


def matrix(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(value, locals={'x': x, 'epsilon': epsilon})
                                          for i, j, value in record['entries']})


def parts(value):
    values = [s.expand(value)]
    for radical in radicals[1:]:
        coefficient = values[0].coeff(radical)
        values[0] -= coefficient*radical
        values.append(coefficient)
    return [s.expand(v) for v in values]


def coefficient_matrices(M):
    data = {}
    for (i, j), value in M.todok().items():
        value = s.expand(value.subs(epsilon, 3*s.sqrt(2)*a/10))
        for radical, component in enumerate(parts(value)):
            for (power,), coefficient in s.Poly(component, x).terms():
                data.setdefault((power, radical), {})[i, j] = F.from_sympy(coefficient)
    return {key: DomainMatrix.from_dok(value, M.shape, F) for key, value in data.items()}


def main():
    began = time.monotonic()
    src = json.loads((HERE/'source.json').read_text())
    proper = json.loads((HERE/'proper.json').read_text())
    assert proper['nonpositive_section_powers'] == []
    old = json.loads((HERE.parent/'packet-gauge-causal/source.json').read_text())
    keep = src['keep121']
    lift = s.MutableSparseMatrix(289, 112, {(row, j): 1 for j, row in enumerate(keep)})
    particular = s.zeros(289, 6)
    for step in reversed(src['auxiliary_steps']):
        back = matrix(step['back'])
        rows, active = step['eliminated'], step['kept']
        R = original.clean(back*lift.extract(active, range(112)))
        S = original.clean(matrix(step['particular_source'])+back*particular.extract(active, range(6)))
        for i, row in enumerate(rows):
            lift[row, :] = R[i, :]
            particular[row, :] = S[i, :]
    assert max(s.degree(v, x) for v in lift if v != 0) <= 2
    scales = {i: s.sympify(value) for i, j, value in old['scales103']['entries'] if i == j}
    diagonal = s.diag(*([s.Integer(1)]*9+[scales[i] for i in range(103)]))
    lift = original.clean(lift*diagonal)
    readers = coefficient_matrices(lift)
    contacts = coefficient_matrices(original.clean(particular))
    section = {}
    for time_power, record in proper['section_coefficients'].items():
        M = DomainMatrix.from_dok({(i, j): F.from_sympy(s.sympify(value, locals={'a': a}))
                                  for i, j, value in record['entries']}, tuple(record['shape']), F)
        for radical in range(4):
            section[int(time_power), radical] = M.extract(range(112), range(6*radical, 6*(radical+1)))
    actual = {}
    for (degree, radical), M in contacts.items():
        if not M.is_zero_matrix:
            actual[-degree, radical] = M
    for (frequency_power, left_radical), M in readers.items():
        for (time_power, right_radical), X in section.items():
            power = time_power-frequency_power
            if power > 0 or M.is_zero_matrix or X.is_zero_matrix:
                continue
            overlap = left_radical & right_radical
            multiplier = F.convert((2 if overlap & 1 else 1)*(15 if overlap & 2 else 1))
            key = power, left_radical ^ right_radical
            actual[key] = actual.get(key, inf.zero(289, 6))+M.matmul(X).scalarmul(multiplier)
            if actual[key].is_zero_matrix:
                del actual[key]
    result = {'scope': 'STRIKE_SOURCE_AUXILIARY_CONTACT_RECONSTRUCTION_FOR_THE_ACTUAL_PARAMETER_FAMILY',
        'input_sha256': {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in ['source.json', 'proper.json']},
        'full289_reconstruction_degree_at_most': 2,
        'full289_nonpositive_coefficients': {f'{power},{radical}': inf.encoded(M) for (power, radical), M in actual.items()},
        'all289_strictly_proper_for_the_same_parameter_family': not actual,
        'source_denominator': src['source_denominator'], 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'lift.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS actual all168 reconstruction; whole289 strictly proper', not actual, result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
