#!/usr/bin/env python3
"""Read the original full-phase coefficient receipt into the peripheral flow."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as s


def decode(value):
    return s.SparseMatrix(*value['shape'], {
        (row, col): s.sympify(text) for row, col, text in value['entries']})


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def realify(matrix):
    real, imag = matrix.applyfunc(s.re), matrix.applyfunc(s.im)
    return s.SparseMatrix.vstack(s.SparseMatrix.hstack(real, -imag),
                                s.SparseMatrix.hstack(imag, real))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', type=Path, required=True)
    parser.add_argument('--generator', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    phase = json.loads(args.phase.read_text())
    generator = json.loads(args.generator.read_text())
    assert phase['source_sha256'] == generator['source_sha256']
    lapse = s.sympify(phase['source_lapse'])
    frequency = s.sympify(phase['source_frequency'])
    principal = list(map(decode, phase['principal_coefficients']))
    constant = decode(phase['stationary_primal_constant'])
    mixing = decode(phase['stationary_scalar_mixing'])
    inverse_time = clean(lapse**2 * principal[0])
    assert clean(inverse_time * principal[0]) == s.eye(252)
    assert clean(principal[0] * inverse_time) == s.eye(252)
    assert s.simplify(frequency / (lapse * s.sqrt(2))) == s.Rational(3, 5)
    assert clean(-inverse_time * constant / (lapse * s.sqrt(2))) == \
        decode(generator['primal_constant_generator'])
    assert clean(inverse_time.T * constant.T / (lapse * s.sqrt(2))) == \
        decode(generator['dual_constant_generator'])
    for index in range(3):
        assert clean(-inverse_time * principal[index + 1] / lapse) == \
            decode(generator['primal_spatial_generators'][index])
        assert clean(-inverse_time.T * principal[index + 1].T / lapse) == \
            decode(generator['dual_spatial_generators'][index])
    scalar = decode(generator['scalar_M_inclusion'])
    assert clean(realify(mixing * scalar)) == \
        decode(generator['original_normalized_Euler_readback']['primal_scalar'])
    result = {
        'scope': 'ORIGINAL_FULL_PHASE_TO_PERIPHERAL_GENERATOR_COEFFICIENT_IDENTITY',
        'source_sha256': phase['source_sha256'],
        'formal_phase_modules': [
            'SaturationMonoid.PhysicsCore.LowEnergy.FullPhase.' + name
            for name in ['Operator', 'Preparation', 'Derivative']],
        'normalization': generator['normalization'],
        'original_temporal_principal_two_sided_inverse': True,
        'primal_and_independent_dual_time_coefficients_equal': True,
        'all_three_primal_and_dual_spatial_coefficients_equal': True,
        'original_stationary_scalar_mixing_equal': True,
        'canonical_response_readback': phase['full_response'],
        'Hamiltonian_readback': phase['Hamiltonian_readback'],
        'original_time_coordinate': True,
    }
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print('PASS same source hashes; actual full-phase time, all spatial and scalar-mixing coefficients')


if __name__ == '__main__':
    main()
