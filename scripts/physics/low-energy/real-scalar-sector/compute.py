#!/usr/bin/env python3
"""Generate the maximal real scalar subspace annihilating the actual mixed maps."""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import exact_readout as r


def zero(rows, columns):
    return [[Q(0)] * columns for _ in range(rows)]


def realification(matrix, imaginary=False):
    rows, columns = len(matrix), len(matrix[0])
    result = zero(2 * rows, 2 * columns)
    for i in range(rows):
        for j in range(columns):
            if imaginary:
                result[i][columns + j] = -matrix[i][j]
                result[rows + i][j] = matrix[i][j]
            else:
                result[i][j] = result[rows + i][columns + j] = matrix[i][j]
    return result


def rank(matrix):
    return len(r.rref(matrix)[1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    names, scalar, _, source_hashes = r.parse_source(args.root)
    for name in ['ColorAlgebra', 'ColorDoublet', 'Spinor', 'Parameters']:
        source = Path('Lean/SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair') / (name + '.lean')
        source_hashes[str(source)] = hashlib.sha256((args.root / source).read_bytes()).hexdigest()
    b4 = list(itertools.combinations(range(7), 4))
    b6 = list(itertools.combinations(range(7), 6))
    ids6 = {subset: i for i, subset in enumerate(b6)}
    vacuum = [[Q(scalar.get(subset, 0))] for subset in b4]
    generators = r.generators([(0, 1, 2), (3, 4)])
    orbit_columns = []
    for _, imaginary, generator in generators:
        action = r.mul(r.exterior_action(generator, 4), vacuum)
        column = [row[0] for row in action]
        orbit_columns.append(([Q(0)] * 35 + column) if imaginary else (column + [Q(0)] * 35))
    orbit = r.transpose(orbit_columns)
    mixed = zero(14, 35)
    for state, (pair, sign) in enumerate([((1, 5), 1), ((0, 5), -1)]):
        for column, subset in enumerate(b4):
            if set(pair).isdisjoint(subset):
                mixed[7 * state + ids6[tuple(sorted(pair + subset))]][column] = Q(sign * r.sign(pair + subset))
    mixed_real = realification(mixed)
    constraints = r.transpose(orbit) + mixed_real
    basis = r.nullspace(constraints)
    dimension = len(basis[0])
    gram = r.mul(r.transpose(basis), basis)
    left = r.mul(r.inverse(gram), r.transpose(basis))
    projector = r.mul(basis, left)
    assert rank(basis) + rank(constraints) == 70
    assert r.mul(constraints, basis) == zero(len(constraints), dimension)
    assert r.mul(mixed_real, orbit) == zero(28, 12)
    assert r.transpose(projector) == projector and r.mul(projector, projector) == projector
    color = []
    for label, imaginary, entries in [
        ('Tx', True, [(0, 1, Q(1, 2)), (1, 0, Q(1, 2))]),
        ('Ty', False, [(0, 1, Q(1, 2)), (1, 0, Q(-1, 2))]),
        ('Tz', True, [(0, 0, Q(1, 2)), (1, 1, Q(-1, 2))]),
    ]:
        fundamental = zero(7, 7)
        for i, j, value in entries:
            fundamental[i][j] = value
        full = realification(r.exterior_action(fundamental, 4), imaginary)
        restricted = r.mul(r.mul(left, full), basis)
        assert r.mul(full, basis) == r.mul(basis, restricted)
        assert r.add(r.mul(gram, restricted), r.mul(r.transpose(restricted), gram)) == zero(dimension, dimension)
        color.append({'label': label, 'full': full, 'restricted': restricted})
    casimir = zero(dimension, dimension)
    for action in color:
        casimir = r.add(casimir, r.mul(action['restricted'], action['restricted']), Q(-1))
    doublet = [[Q(4, 3) * entry for entry in row] for row in casimir]
    assert r.mul(doublet, doublet) == doublet
    for i, first in enumerate(color):
        for j, second in enumerate(color):
            anticommutator = r.add(r.mul(first['restricted'], second['restricted']),
                                  r.mul(second['restricted'], first['restricted']))
            assert anticommutator == [[Q(-1, 2) * entry if i == j else Q(0)
                                      for entry in row] for row in doublet]
    singlets = r.nullspace(casimir)
    adapted_columns = r.transpose(singlets)
    singlet_dimension = len(adapted_columns)
    quaternion_blocks = []
    for column in r.transpose(doublet):
        if rank(r.transpose(adapted_columns + [column])) == len(adapted_columns):
            continue
        vector = [[entry] for entry in column]
        block = [column] + [[2 * row[0] for row in r.mul(action['restricted'], vector)] for action in color]
        assert rank(r.transpose(adapted_columns + block)) == len(adapted_columns) + 4
        quaternion_blocks.append(block)
        adapted_columns += block
        if len(adapted_columns) == dimension:
            break
    adapted = r.transpose(adapted_columns)
    inverse = r.inverse(adapted)
    transformed = [r.mul(r.mul(inverse, action['restricted']), adapted) for action in color]
    blocks = [matrix[singlet_dimension:singlet_dimension + 4] for matrix in transformed]
    blocks = [[row[singlet_dimension:singlet_dimension + 4] for row in matrix] for matrix in blocks]
    for matrix, block in zip(transformed, blocks):
        expected = zero(dimension, dimension)
        for n in range(len(quaternion_blocks)):
            for i in range(4):
                for j in range(4):
                    expected[singlet_dimension + 4 * n + i][singlet_dimension + 4 * n + j] = block[i][j]
        assert matrix == expected
    previous = json.loads((args.root / 'Verification/physics/low-energy-phenomenology/coupled-response/results.json').read_text())
    old_basis = realification([[Q(value) for value in row] for row in previous['subspace_basis_columns']])
    old_gram = r.mul(r.transpose(old_basis), old_basis)
    old_projector = r.mul(r.mul(old_basis, r.inverse(old_gram)), r.transpose(old_basis))
    assert r.mul(projector, old_basis) == old_basis
    extra_projector = r.add(projector, old_projector, Q(-1))
    assert r.mul(extra_projector, extra_projector) == extra_projector
    assert all(r.mul(action['full'], extra_projector) == zero(70, 70) for action in color)
    receipt = {
        'scope': 'ACTUAL_REAL_SCALAR_MIXED_KERNEL_AND_SPATIAL_SYMBOL',
        'source_sha256': source_hashes, 'basis_names': names, 'scalar_basis': b4,
        'degree_six_basis': b6, 'gauge_labels': [label for label, _, _ in generators],
        'gauge_column_imaginary': [imaginary for _, imaginary, _ in generators],
        'orbit_real': orbit, 'orbit_real_rank': rank(orbit), 'mixed_complex': mixed,
        'mixed_real': mixed_real, 'mixed_real_rank': rank(mixed_real),
        'constraints': constraints, 'constraint_rank': rank(constraints),
        'basis': basis, 'real_dimension': dimension, 'gram': gram,
        'projector': projector, 'background_color': color, 'casimir': casimir,
        'doublet_projector': doublet, 'adapted_basis': adapted,
        'singlet_dimension': singlet_dimension, 'quaternion_block_count': len(quaternion_blocks),
        'quaternion_generators': blocks,
        'previous_real_dimension': rank(old_basis), 'additional_projector': extra_projector,
        'additional_real_dimension': rank(extra_projector),
        'gauge_amplitude_squared': Q(18, 25), 'lapse_squared': Q(54, 125),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(r.encode(receipt), ensure_ascii=False, separators=(',', ':')) + '\n')
    print(f'PASS: real orbit rank={rank(orbit)}, real mixed rank={rank(mixed_real)}, kernel dimension={dimension}')
    print(f'Generated {singlet_dimension} real singlets and {len(quaternion_blocks)} real quaternion blocks.')
    print('All source constraints, Gram-skew identities, invariance and adapted block identities checked exactly.')


if __name__ == '__main__':
    main()
