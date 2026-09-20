#!/usr/bin/env python3
"""Transport the frozen axial characteristic divisor into squared-radius coordinates.

Each q -> -q orbit is paired algebraically.  The result is an exact polynomial
in x=u^2 and w=|k|^2/2, retaining the source factor multiplicities. The finite
289/112 congruences and nine-tangent intertwining supply its all-direction
meaning; this script performs the remaining exact factor readback.
"""
import argparse
import json
from pathlib import Path

import sympy as s


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalog', type=Path, required=True)
    parser.add_argument('--finite', type=Path, required=True)
    parser.add_argument('--transport', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    catalog = json.loads(args.catalog.read_text())
    finite = json.loads(args.finite.read_text())
    transport = json.loads(args.transport.read_text())
    assert len(finite['certificates']) == len(transport['certificates']) == 3
    assert all(c['inverse_matrix_polynomial_coefficients_verified'] for c in finite['certificates'])
    assert all(c['all_exact_intertwining_coefficients_zero'] and
               c['source_reduced_112_congruence_zero_coefficient_slots'] > 0
               for c in transport['certificates'])
    u, q, x, w = s.symbols('u q x w')
    entries = catalog['distinct_rational_factors']
    factors = [s.Poly(s.sympify(entry['polynomial']), u, q, domain=s.QQ) for entry in entries]
    visited, orbits = set(), []
    for i, polynomial in enumerate(factors):
        if i in visited:
            continue
        reflected = s.Poly(polynomial.as_expr().subs(q, -q), u, q, domain=s.QQ)
        matches = [j for j, candidate in enumerate(factors) if candidate == reflected]
        assert len(matches) == 1
        j = matches[0]
        assert entries[i]['multiplicity'] == entries[j]['multiplicity']
        orbit = [i] if i == j else [i, j]
        even = polynomial if i == j else polynomial*factors[j]
        assert all(a % 2 == b % 2 == 0 for a, b in even.monoms())
        invariant = s.Poly.from_dict({(a//2, b//2): coefficient
            for (a, b), coefficient in even.terms()}, (x, w), domain=s.QQ)
        assert s.Poly(invariant.as_expr().subs({x: u*u, w: q*q}), u, q) == even
        original_at_zero = s.prod(factors[index].as_expr().subs(q, 0) for index in orbit)
        assert s.expand(invariant.as_expr().subs({x: u*u, w: 0})-original_at_zero) == 0
        orbits.append({'axial_factor_indices': orbit, 'multiplicity': entries[i]['multiplicity'],
            'polynomial_in_x_w': str(invariant.as_expr()),
            'exact_coefficients': [[a, b, str(c)] for (a, b), c in invariant.terms()]})
        visited.update(orbit)
    assert visited == set(range(len(factors)))
    degree = sum(2*s.Poly(s.sympify(orbit['polynomial_in_x_w']), x, w).degree(x)*orbit['multiplicity']
                 for orbit in orbits)
    assert degree == catalog['total_divisor_degree']
    result = {'scope': 'ALL_REAL_THREE_MOMENTUM_SOURCE_CHARACTERISTIC_DIVISOR',
        'coordinates': {'x': 'lambda^2/(2*N^2)=125*lambda^2/108',
                        'w': '(k1^2+k2^2+k3^2)/2'},
        'construction': 'exact q-reflection orbits of the frozen axial factors, transported by the actual finite source congruence',
        'factor_readback': 'product(P(x,w)^multiplicity) equals the complete frozen axial divisor after x=u^2,w=q^2',
        'orbits': orbits, 'axial_factor_count': len(factors), 'radial_orbit_count': len(orbits),
        'temporal_polynomial_degree': degree,
        'all_nonzero_spatial_momenta': 'Lean momentum_alignment supplies finite y,z; S_total=S_Z(z) S_Y(y) transports the faithful axial section',
        'zero_spatial_momentum': 'identity rotation; original q=0 factors and origin partial multiplicities retained',
        'origin_partial_multiplicities': catalog['origin_partial_multiplicities'],
        'new_momentum_poles_from_rotation': False,
        'particle_identification': None}
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print('PASS: all', len(factors), 'factors form', len(orbits),
          'exact squared-radius orbits; temporal degree', degree, '; zero-momentum specialization preserved')


if __name__ == '__main__':
    main()
