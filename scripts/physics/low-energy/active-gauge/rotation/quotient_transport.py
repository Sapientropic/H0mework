#!/usr/bin/env python3
"""Exact finite transport of the nine source gauge directions.

The full-Hessian congruence transports physical response only after the actual
SU(2) and Lorentz tangent image is transported as well.  This checks the latter
identity in all four momenta and the whole rational rotation parameter.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path

from finite import accumulate, finite_congruence, mul, power, scale, source_integer_coefficients


def parameter_rotation(spatial):
    result = {}
    for block in range(3):
        for (row, column), polynomial in spatial.items():
            if row and column:
                result[3*block+column-1, 3*block+row-1] = polynomial
    return result


def tangent_image(source, spatial):
    result = {}
    for (row, column, powers, basis), coefficient in source.items():
        degree = sum(powers)
        assert degree <= 1
        if degree == 0:
            accumulate(result, (row, column, powers, basis),
                       scale(coefficient, power((1, 0, 1), 2)))
        else:
            component = powers.index(1)
            for target in range(4):
                value = spatial.get((target, component))
                if value:
                    new_powers = tuple(int(i == target) for i in range(4))
                    accumulate(result, (row, column, new_powers, basis), scale(coefficient, value))
    return result


def verify(source, reduced, entry):
    spatial = {(i, j): tuple(poly) for i, j, poly in entry['spatial_numerator']}
    full_field = {(i, j): tuple(poly) for i, j, poly in entry['field_numerator']}
    primitive = set(range(9, 121))
    for i, j in full_field:
        assert (i in primitive) == (j in primitive), (i, j)
    field = {(i, j): value for (i, j), value in full_field.items() if i in primitive}
    congruence_slots = finite_congruence(reduced, spatial,
                                        entry['field_constant_denominator'], field)
    parameters = parameter_rotation(spatial)
    image = tangent_image(source, spatial)
    parameter_rows = defaultdict(list)
    for (i, j), polynomial in parameters.items():
        parameter_rows[i].append((j, polynomial))
    left = {}
    for (i, j, powers, basis), polynomial in image.items():
        for column, coefficient in parameter_rows[j]:
            accumulate(left, (i, column, powers, basis),
                       scale(entry['field_constant_denominator'], mul(polynomial, coefficient)))
    source_rows = defaultdict(list)
    for (i, j, powers, basis), coefficient in source.items():
        source_rows[i].append((j, powers, basis, coefficient))
    for (i, j), polynomial in field.items():
        for column, powers, basis, coefficient in source_rows[j]:
            accumulate(left, (i, column, powers, basis), scale(-coefficient, polynomial))
    assert not left, list(left.items())[:10]
    return {'axis': entry['axis'], 'source_parameter_rotation': 'diag(R_spatial^T,R_spatial^T,R_spatial^T)',
            'primitive_subspace_preserved': True, 'all_exact_intertwining_coefficients_zero': True,
            'source_reduced_112_congruence_zero_coefficient_slots': congruence_slots,
            'parameter_numerator': [[i, j, list(value)] for (i, j), value in sorted(parameters.items())]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--symmetries', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--finite', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    symmetries = json.loads(args.symmetries.read_text())
    finite = json.loads(args.finite.read_text())
    receipt = json.loads(args.receipt.read_text())
    denominator, source = source_integer_coefficients(
        {'Fourier_Jacobi_entries': symmetries['source_symmetry_tangents_112']})
    assert all(9 <= i < 121 and 0 <= j < 9 for i, j, _, _ in source)
    _, reduced = source_integer_coefficients(
        {'Fourier_Jacobi_entries': receipt['equivalent_112_Fourier_Jacobi_entries']})
    certificates = []
    for entry in finite['certificates']:
        certificates.append(verify(source, reduced, entry))
        print('PASS: reduced 112-field congruence and source nine-tangent finite intertwining axis',
              entry['axis'], flush=True)
    result = {'scope': 'EXACT_FINITE_TRANSPORT_OF_THE_SOURCE_NINE_SYMMETRY_IMAGES',
        'source_order': symmetries['source_symmetry_order'],
        'identity': 'T(R(z)^T p) U(z)=S_112(z) T(p)',
        'reduced_symbol_identity': 'S_112(z)^T H_112(R(z)^T p) S_112(z)=H_112(p)',
        'parameter_matrix_denominator': '(1+z^2)^2',
        'source_tangent_common_denominator': denominator,
        'verification': 'all integer coefficients in z and every momentum monomial, no sampling',
        'consequence': 'the full-symbol congruence induces an invertible map on the faithful quotient by exactly these nine source directions',
        'additional_diffeomorphism_directions_inserted': False,
        'certificates': certificates}
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')


if __name__ == '__main__':
    main()
