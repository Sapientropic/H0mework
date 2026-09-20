#!/usr/bin/env python3
"""Exact determinant blocks of the faithful 103-coordinate source quotient.

Only invertible constant coordinate and momentum changes are used. The output
is a characteristic divisor; poles of individual responses require the
corresponding adjugate numerator, so no determinant root is counted as a particle.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--quotient', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    source = json.loads(args.receipt.read_text())
    quotient = json.loads(args.quotient.read_text())
    lam, k, u, q = s.symbols('lam k u q', real=True)
    n = s.sympify(source['source_lapse'])
    retained = quotient['retained_original_fields']
    scale = []
    for index in retained:
        field = source['fields'][index]
        value = 1
        if field['group'] in ['gauge_A', 'dual_H']:
            value = s.sqrt(2)
            if field['group'] == 'gauge_A' and field['coordinate'][0] == 0:
                value *= n
        elif field['group'] == 'coframe' and field['coordinate'][1] == 0:
            value = n
        scale.append(value)
    entries = {}
    for i, j, value in quotient['quotient_operator_103_by_103']:
        value = s.sympify(value.replace('lambda', 'lam'), locals={'lam': lam, 'k': k})
        value = s.expand(value.subs({lam: n*s.sqrt(2)*u, k: s.sqrt(2)*q})*scale[i]*scale[j]/n)
        polynomial = s.Poly(value, u, q, domain=s.QQ_I)
        assert polynomial.as_expr() == value
        entries[i, j] = value
    normalized = s.SparseMatrix(103, 103, entries)
    adjacency = defaultdict(set)
    for i, j in entries:
        adjacency[i].add(j)
        adjacency[j].add(i)
    unseen, blocks = set(range(103)), []
    while unseen:
        seed = unseen.pop()
        block, stack = {seed}, [seed]
        while stack:
            new = adjacency[stack.pop()] & unseen
            unseen -= new
            block |= new
            stack.extend(new)
        blocks.append(sorted(block))
    blocks.sort(key=lambda block: (len(block), block[0]))
    result = {'scope': 'FAITHFUL_SOURCE_QUOTIENT_EXACT_AXIAL_CHARACTERISTIC_DIVISOR',
        'normalization': 'lambda=N*sqrt(2)*u; k=sqrt(2)*q; G=S^T K S/N',
        'constant_diagonal_field_scaling': [str(value) for value in scale],
        'determinant_readback': 'det K = N^103/prod(S_ii^2) * det G(lambda/(N*sqrt(2)),k/sqrt(2))',
        'determinant_constant_multiplier': str(s.simplify(n**103/s.prod(value**2 for value in scale))),
        'source_section_is_faithful_for_all_lambda_k': True,
        'blocks': [], 'all_blocks_complete': False, 'physical_particle_count': None,
        'response_numerator_cancellations_checked': False}
    for number, block in enumerate(blocks):
        started = time.monotonic()
        print('computing structural block', number, 'size', len(block), flush=True)
        matrix = normalized[block, block]
        row_denominators = []
        for row in matrix.tolist():
            denominator = 1
            for entry in row:
                for coefficient in s.Poly(entry, u, q, domain=s.QQ_I).coeffs():
                    denominator = s.ilcm(denominator, s.denom(s.re(coefficient)), s.denom(s.im(coefficient)))
            row_denominators.append(denominator)
        integer_matrix = s.diag(*row_denominators)*matrix
        domain = s.ZZ_I.poly_ring(u, q)
        determinant = DomainMatrix.from_Matrix(integer_matrix).convert_to(domain).det()
        expression = domain.to_sympy(determinant)/s.prod(row_denominators)
        assert expression != 0
        polynomial = s.Poly(expression, u, q, domain=s.QQ_I)
        leading = polynomial.LC()
        rational_polynomial = s.Poly(s.expand(expression/leading), u, q, domain=s.QQ)
        coefficient, factors = s.factor_list(rational_polynomial.as_expr(), u, q)
        coefficient *= leading
        assert s.expand(coefficient*s.prod(factor**power for factor, power in factors)-expression) == 0
        entry = {'quotient_indices': block, 'original_fields': [retained[i] for i in block],
                 'dimension': len(block), 'constant': str(coefficient),
                 'constant_row_denominators_cleared': [str(value) for value in row_denominators],
                 'factor_coefficient_field': 'Q, with the overall nonzero constant retained separately',
                 'factors': [{'polynomial': str(factor), 'multiplicity': int(power)} for factor, power in factors],
                 'total_degree': s.Poly(expression, u, q).total_degree(),
                 'elapsed_seconds': round(time.monotonic()-started, 3)}
        result['blocks'].append(entry)
        args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
        print('PASS block', number, 'degree', entry['total_degree'], 'factors', len(factors),
              'seconds', entry['elapsed_seconds'], flush=True)
    result['all_blocks_complete'] = True
    result['quotient_dimension_verified'] = sum(block['dimension'] for block in result['blocks'])
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print('PASS: all exact determinant blocks cover the faithful 103-dimensional quotient', flush=True)


if __name__ == '__main__':
    main()
