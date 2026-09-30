#!/usr/bin/env python3
"""Actual126 source retarded inverse from characteristic-polynomial division.

Every SCC uses its newly computed exact source characteristic polynomial and
the kernel-checked Cayley-Hamilton synthetic quotient. The real source DAG
then generates the whole inverse; no dense symbolic126 inverse is assumed.
"""
from __future__ import annotations

import hashlib
import json
import time
from functools import cached_property
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from dynamic import HERE, ROOT, ROOT_ID
from retained_hamiltonian_reduction import DOMAIN, decode, dm, identity, zero, encode


Z = s.Symbol('retarded_laplace')
X = s.Symbol('formal_generator')
RING = DOMAIN.poly_ring(Z)
ZZ = RING.gens[0]
SCALAR_RING = DOMAIN.poly_ring(X, Z)
XX, ZS = SCALAR_RING.gens


def polynomial(coefficients, argument, ring):
    value = ring.zero
    for coefficient in coefficients:
        value = value*argument+ring.convert(coefficient, DOMAIN)
    return value


def stack_rows(blocks, groups, shape, domain):
    rows = {}
    for block, indices in zip(blocks, groups):
        for local, row in block.to_sparse().rep.items():
            rows[indices[local]] = dict(row)
    return DM(rows, shape, domain).to_sparse()


class SourceActiveResolventLeaf:
    def __init__(self, A, indices):
        self.A, self.indices = A, tuple(indices)
        self.n = A.shape[0]
        self.coefficients = A.charpoly()
        self.denominator = polynomial(self.coefficients, ZZ, RING)
        # Verify the exact scalar synthetic-division recipe. Substituting the
        # commuting pair (A,zI) and the compiled Cayley-Hamilton theorem pays
        # both matrix numerator products for arbitrary z, not just samples.
        current = numerator = SCALAR_RING.one
        for c in self.coefficients[1:-1]:
            current = XX*current+SCALAR_RING.convert(c, DOMAIN)
            numerator = ZS*numerator+current
        px = polynomial(self.coefficients, XX, SCALAR_RING)
        pz = polynomial(self.coefficients, ZS, SCALAR_RING)
        assert (ZS-XX)*numerator == pz-px
        assert numerator*(ZS-XX) == pz-px
        quotient, remainder = px.div(XX-ZS)
        assert quotient == numerator and remainder == pz

    @cached_property
    def polynomial_matrix(self):
        return self.A.convert_to(RING)

    def numerator_action(self, forcing, laplace=None):
        """The source synthetic quotient, evaluated on the actual forcing."""
        ring = forcing.domain
        A = self.polynomial_matrix if ring == RING else self.A.convert_to(ring)
        argument = ZZ if laplace is None else laplace
        current = forcing
        numerator = forcing
        for coefficient in self.coefficients[1:-1]:
            current = A*current+forcing.scalarmul(ring.convert(coefficient, DOMAIN))
            numerator = numerator.scalarmul(argument)+current
        return numerator

    def field_action(self, forcing, laplace):
        denominator = polynomial(self.coefficients, laplace, DOMAIN)
        assert denominator != DOMAIN.zero
        return self.numerator_action(forcing, laplace).scalarmul(DOMAIN.one/denominator)


class SourceActiveRetardedInverse:
    def __init__(self, record):
        self.record = record
        self.A = dm(decode(record['Hamiltonian_generator']))
        self.n = self.A.shape[0]
        assert self.n == 126
        raw = self.A.to_Matrix()
        raw_groups = [tuple(sorted(group)) for group in raw.strongly_connected_components()]
        owner = {j: i for i, group in enumerate(raw_groups) for j in group}
        edges = {(owner[j], owner[i]) for i, row in self.A.rep.items() for j in row if owner[i] != owner[j]}
        remaining = set(range(len(raw_groups))); order = []
        while remaining:
            ready = sorted((i for i in remaining if not any(target == i and source in remaining for source, target in edges)),
                           key=lambda i: min(raw_groups[i]))
            assert ready, 'the exact source SCC quotient must be acyclic'
            order.extend(ready); remaining.difference_update(ready)
        self.groups = [raw_groups[i] for i in order]
        self.owner = {j: i for i, group in enumerate(self.groups) for j in group}
        self.feeds = {}
        for i in range(len(self.groups)):
            for j in range(i):
                block = self.A.extract(self.groups[i], self.groups[j])
                if not block.is_zero_matrix:
                    self.feeds[i, j] = block
            for j in range(i+1, len(self.groups)):
                zero(self.A.extract(self.groups[i], self.groups[j]))
        self.leaves = []
        for group in self.groups:
            leaf = SourceActiveResolventLeaf(self.A.extract(group, group), group)
            self.leaves.append(leaf)
            print('PASS source active SCC characteristic/synthetic quotient', self.n, len(group), flush=True)
        self.ancestors = []
        for i in range(len(self.groups)):
            ancestors = set()
            for left, right in self.feeds:
                if left == i:
                    ancestors.update(self.ancestors[right]); ancestors.add(right)
            self.ancestors.append(ancestors)
        self.denominator = self.product(range(len(self.leaves)))
        original = s.sympify(record['linearized_characteristic_polynomial'],
                            locals={'source_laplace': Z})
        assert s.expand(RING.to_sympy(self.denominator)-original) == 0

    def product(self, indices):
        value = RING.one
        for j in sorted(indices):
            value *= self.leaves[j].denominator
        return value

    def field_action(self, forcing, laplace):
        laplace = DOMAIN.from_sympy(s.sympify(laplace))
        forcing = forcing.convert_to(DOMAIN)
        result = []
        for i, leaf in enumerate(self.leaves):
            rhs = forcing.extract(self.groups[i], range(forcing.shape[1]))
            for (target, source), feed in self.feeds.items():
                if target == i:
                    rhs += feed*result[source]
            result.append(leaf.field_action(rhs, laplace))
        return stack_rows(result, self.groups, forcing.shape, DOMAIN)

    def polynomial_action(self, forcing):
        """Complete source rational action as (numerator,det(zI-A)).

        Separate SCC denominators keep disconnected blocks cheap. Every
        denominator product is made from the actual finite ancestor set.
        """
        forcing = forcing.convert_to(RING)
        numerators = []
        for i, leaf in enumerate(self.leaves):
            ancestors = self.ancestors[i]
            rhs = forcing.extract(self.groups[i], range(forcing.shape[1])).scalarmul(self.product(ancestors))
            for (target, source), feed in self.feeds.items():
                if target == i:
                    remaining = ancestors-self.ancestors[source]-{source}
                    rhs += (feed.convert_to(RING)*numerators[source]).scalarmul(self.product(remaining))
            numerators.append(leaf.numerator_action(rhs))
        all_blocks = set(range(len(self.leaves)))
        common = [numerators[i].scalarmul(self.product(all_blocks-self.ancestors[i]-{i}))
                  for i in range(len(self.leaves))]
        return stack_rows(common, self.groups, forcing.shape, RING), self.denominator

    def source_bound(self):
        matrix = self.A.to_Matrix()
        entries = {(i, j): s.simplify(abs(s.re(v))+abs(s.im(v))) for (i, j), v in matrix.todok().items()}
        row = max(sum(v for (i, _), v in entries.items() if i == a) for a in range(self.n))
        col = max(sum(v for (_, j), v in entries.items() if j == a) for a in range(self.n))
        row, col = s.simplify(row), s.simplify(col)
        integer_bound = int(s.ceiling(max(row, col)))
        assert integer_bound > 0 and integer_bound >= row and integer_bound >= col
        return {'row': row, 'column': col, 'beta': s.sqrt(row*col), 'integer_upper': integer_bound}

    def time_coefficients(self, forcing, order):
        """The actual entire time action:sum t^j A^j f/j!."""
        values = [forcing.convert_to(DOMAIN)]
        for j in range(order):
            next_value = (self.A*values[-1]).scalarmul(DOMAIN.from_sympy(s.Rational(1, j+1)))
            zero(next_value.scalarmul(DOMAIN.convert(j+1))-self.A*values[-1])
            values.append(next_value)
        return values

    def vector_readout(self, vector):
        """Compact actual values; verification always consumes the whole vector."""
        rows = {0, self.n-1}
        for group in self.groups:
            rows.add(next((j for j in group if vector.rep.get(j, {}).get(0, DOMAIN.zero) != DOMAIN.zero), group[0]))
        rows = sorted(rows)
        return {'source_rows': rows, 'values': encode(vector.extract(rows, [0])),
                'full_vector_dimension': self.n,
                'selection': 'first and last source coordinates plus one actual nonzero coordinate per source SCC when available'}


def actual_consumer(model):
    m = model
    forcing = dm(s.Matrix([s.Rational((7*j+2) % 17-8, 31)+s.I*s.Rational((11*j+3) % 19-9, 37)
                           for j in range(m.n)]))
    numerator, denominator = m.polynomial_action(forcing)
    operator = identity(m.n).convert_to(RING).scalarmul(ZZ)-m.A.convert_to(RING)
    zero(operator*numerator-forcing.convert_to(RING).scalarmul(denominator))
    right_numerator, right_denominator = m.polynomial_action(operator*forcing.convert_to(RING))
    assert right_denominator == denominator
    zero(right_numerator-forcing.convert_to(RING).scalarmul(denominator))
    print('PASS whole126 actual arbitrary-z polynomial left/right action', m.record['momentum'], flush=True)
    bound = m.source_bound()
    points = [s.Integer(bound['integer_upper']+1)+s.I, s.Integer(bound['integer_upper']+2)+2*s.I]
    numerical = []
    for z in points:
        M = identity(m.n).scalarmul(DOMAIN.from_sympy(z))-m.A
        response = m.field_action(forcing, z)
        zero(M*response-forcing)
        zero(m.field_action(M*forcing, z)-forcing)
        evaluated = DM({i: {j: value.evaluate(0, DOMAIN.from_sympy(z)) for j, value in row.items()}
                        for i, row in numerator.rep.items()}, numerator.shape, DOMAIN)
        den = denominator.evaluate(0, DOMAIN.from_sympy(z))
        zero(evaluated-response.scalarmul(den))
        numerical.append({'laplace': str(z), 'response_readout': m.vector_readout(response),
                          'all126_left_right_and_polynomial_response_equations_checked': True})
    coefficients = m.time_coefficients(forcing, 20)
    t = s.Rational(1, 2*bound['integer_upper'])
    time_value = coefficients[0]
    for j in range(1, len(coefficients)):
        time_value += coefficients[j].scalarmul(DOMAIN.from_sympy(t**j))
    force_bound = sum(s.simplify(abs(s.re(v))+abs(s.im(v))) for v in forcing.to_Matrix())
    error = s.cancel(2*force_bound*s.Rational(1, 2)**21/s.factorial(21))
    assert error > 0
    print('PASS source active causal half-plane, actual algebraic responses and controlled time-series action', flush=True)
    return {'forcing': encode(forcing),
        'whole126_polynomial_left_and_right_residuals_exact_zero': True,
        'numerator_degree_bound': 125,
        'field_response_checks': numerical,
        'source_norm_bound': {key: str(value) for key, value in bound.items()},
        'time_consumer': {'time': str(t), 'order': 20, 'actual_partial_sum_readout': m.vector_readout(time_value),
            'Euclidean_remainder_upper_bound': str(error),
            'bound_proof': '||A||2<=sqrt(row_bound*column_bound)<=B; t=1/(2B), exp(||A||t)<2 and ||f||2<=the actual component1 bound. The tail is at most2*||f||bound*(1/2)^21/21!.',
            'all20_original_time_recursion_equations_checked': True}}


def main():
    started = time.monotonic()
    path = HERE/'retained_hamiltonian_reduction.json'
    source = json.loads(path.read_text()); assert source['root'] == ROOT_ID
    for kind in ('source_sha256', 'input_sha256'):
        for name, digest in source[kind].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    records = []
    for row in source['source_momenta']:
        m = SourceActiveRetardedInverse(row)
        consumer = actual_consumer(m)
        records.append({'momentum': row['momentum'],
            'source_topological_SCCs': [list(group) for group in m.groups],
            'source_DAG_feeds': [{'target': a, 'source': b, 'matrix': encode(feed)} for (a, b), feed in m.feeds.items()],
            'leaf_characteristic_polynomials': [str(s.factor(RING.to_sympy(leaf.denominator))) for leaf in m.leaves],
            'leaf_synthetic_division_identities_checked': True,
            'source_ancestor_sets': [sorted(indices) for indices in m.ancestors],
            'complete_determinant': str(s.factor(RING.to_sympy(m.denominator))),
            'complete_determinant_matches_original_source_charpoly': True,
            'actual_consumer': consumer})
    paths = [path, HERE/'retained_hamiltonian_reduction.py', HERE/'independent_retained_hamiltonian_reduction.json',
             HERE/'source_active_retarded_inverse.py', HERE/'CayleyHamiltonRetarded.lean']
    result = {'root': ROOT_ID, 'source_sha256': source['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'ACTUAL_SOURCE_ACTIVE126_GENERIC_LAPLACE_INVERSE_AND_CAUSAL_TIME_ACTION_ON_TWO_SIGNED_MOMENTUM_FIBRES',
        'Laplace_variable': str(Z),
        'source_fibres': records,
        'leaf_algorithm': 'c=charpoly(A) descending; current=f,numerator=f; for c_j excluding monic and constant:current=A*current+c_j*f,numerator=z*numerator+current. Divide by charpoly(A)(z).',
        'generic_kernel_theorem': 'SourceCayleyHamiltonRetarded.left_numerator/right_numerator/both_inverse_products: numerator=aeval A (charpoly(A) /monic (X-C z)); Matrix.aeval_self_charpoly is consumed, not assumed.',
        'same_synthetic_quotient': 'Each actual SCC charpoly is recomputed in the original source number field. Its scalar Horner recurrence is checked equal to the exact polynomial quotient in the free commuting variables X,z; evaluation at (A,zI) is exactly the compiled numerator.',
        'whole_inverse': 'Follow the actual source SCC DAG. The left inverse follows each paid leaf equation; applying the same recursion to (zI-A)v recovers each arbitrary v component in topological order using the paid right leaf equation. Thus both complete126 products are I whenever the displayed determinant is nonzero.',
        'retarded': 'G_A(t)=0 for t<0 and exp(t A) for t>0, with source-generated entire coefficients A^j/j! and the displayed source norm bound. Its jump is I126 and (partial_t-A)G_A=delta(t)I126. For Re(z)>beta_active its absolutely convergent Laplace integral is the same generated rational inverse.',
        'source_norm_bound': 'For each fibre beta_active=sqrt(max_row sum(|Re Aij|+|Im Aij|)*max_column sum(|Re Aij|+|Im Aij|)); no tail-only bound is applied to A126.',
        'future_common_half_plane': 'A common active/tail consumer must use Re(z)>max(beta_active,153*sqrt(30)/625), then consume its actual same-source X/R so the original constrained jump is T, not I1214.',
        'growing_poles_or_nonsemisimple_parts_discarded': False,
        'recording_scope': 'The program checks complete126-coordinate polynomial and field inverse equations and all20 complete time recursions. Only the displayed field/time values are sampled for compact recording; the source forcing, matrix, charpoly and exact recurrences reconstruct every coordinate.',
        'full_physical_X_R_or_tail_composition_claimed_here': False,
        'interacting_composite_measure_or_proton_pole_named': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_active_retarded_inverse.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source active126 retarded inverse', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
