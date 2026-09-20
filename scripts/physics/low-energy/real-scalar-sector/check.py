#!/usr/bin/env python3
"""Independent exterior-minor and exact real-kernel verification; no producer imports."""
import argparse
import copy
import hashlib
import itertools
import json
import re
import sys
from fractions import Fraction as Q
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_readout import matrix, trans, product, identity


def zero(a):
    return all(not value for row in a for value in row)


def rank(a):
    a = [row[:] for row in a]
    row = 0
    for column in range(len(a[0])):
        pivot = next((i for i in range(row, len(a)) if a[i][column]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        a[row] = [v / a[row][column] for v in a[row]]
        for i in range(row + 1, len(a)):
            coefficient = a[i][column]
            a[i] = [v - coefficient * w for v, w in zip(a[i], a[row])]
        row += 1
        if row == len(a):
            break
    return row


def entry(g, out, inp):
    removed, added = sorted(set(inp) - set(out)), sorted(set(out) - set(inp))
    if not removed:
        return sum(g[i][i] for i in inp)
    if len(removed) != 1:
        return Q(0)
    old, new = removed[0], added[0]
    return (-1) ** (inp.index(old) + out.index(new)) * g[new][old]


def fundamental(label):
    g = [[Q(0)] * 7 for _ in range(7)]
    if label == 'Y':
        g[5][5], g[6][6] = Q(1), Q(-1)
    elif label[0] in 'AS':
        i, j = int(label[1]), int(label[2])
        g[i][j], g[j][i] = Q(1), Q(-1 if label[0] == 'A' else 1)
    else:
        i, j = map(int, label[1:].split('-'))
        g[i][i], g[j][j] = Q(1), Q(-1)
    return g


def source_color(root):
    source = (root / 'Lean/SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair/ColorAlgebra.lean').read_text()
    declaration = source.split('def sourceColorRaw', 1)[1].split('theorem sourceColorP286Generator_color', 1)[0]
    matrices = re.findall(r'!!\[(.*?)\]', declaration, re.S)
    assert len(matrices) == 3
    result = []
    for text in matrices:
        real, imaginary = [[Q(0)] * 7 for _ in range(7)], [[Q(0)] * 7 for _ in range(7)]
        rows = text.split(';')
        assert len(rows) == 3
        for i, row in enumerate(rows):
            values = row.split(',')
            assert len(values) == 3
            for j, value in enumerate(values):
                value = value.strip()
                if 'Complex.I' in value:
                    imaginary[i][j] = Q(value.replace('Complex.I', '1'))
                else:
                    real[i][j] = Q(value)
        result.append((real, imaginary))
    return result


def check(root, data):
    assert data['scope'] == 'ACTUAL_REAL_SCALAR_MIXED_KERNEL_AND_SPATIAL_SYMBOL'
    for name, digest in data['source_sha256'].items():
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest
    prior = json.loads((root / 'Verification/physics/low-energy-phenomenology/results/exact-readout.json').read_text())
    for name, digest in prior['source_sha256'].items():
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest
    scalar = {tuple(subset): Q(coefficient) for subset, coefficient in prior['joint_scalar_terms']}
    b4 = list(itertools.combinations(range(7), 4))
    b6 = list(itertools.combinations(range(7), 6))
    assert data['scalar_basis'] == [list(subset) for subset in b4]
    assert data['degree_six_basis'] == [list(subset) for subset in b6]
    labels = ['A01', 'S01', 'A02', 'S02', 'A12', 'S12', 'D0-2', 'D1-2', 'A34', 'S34', 'D3-4', 'Y']
    assert data['gauge_labels'] == labels
    orbit = [[Q(0)] * 12 for _ in range(70)]
    for column, label in enumerate(labels):
        imaginary = not label.startswith('A')
        assert data['gauge_column_imaginary'][column] == imaginary
        for row, out in enumerate(b4):
            orbit[(35 if imaginary else 0) + row][column] = sum(entry(fundamental(label), out, inp) * c for inp, c in scalar.items())
    mixed = []
    for pair, sign in [((1, 5), 1), ((0, 5), -1)]:
        for out in b6:
            complement = tuple(i for i in out if i not in pair)
            mixed.append([Q(sign * (-1) ** sum(i > j for i in pair for j in inp))
                          if set(pair).issubset(out) and inp == complement else Q(0) for inp in b4])
    mixed_real = [row + [Q(0)] * 35 for row in mixed] + [[Q(0)] * 35 + row for row in mixed]
    assert matrix(data['orbit_real']) == orbit and matrix(data['mixed_complex']) == mixed
    assert matrix(data['mixed_real']) == mixed_real
    constraints = trans(orbit) + mixed_real
    assert matrix(data['constraints']) == constraints
    basis, gram, projector = map(matrix, [data['basis'], data['gram'], data['projector']])
    dimension = rank(basis)
    assert len(basis) == 70 and len(basis[0]) == dimension == data['real_dimension']
    assert rank(orbit) == data['orbit_real_rank'] == 9
    assert rank(mixed_real) == data['mixed_real_rank'] == 18
    assert rank(constraints) == data['constraint_rank'] == 70 - dimension == 27
    assert zero(product(constraints, basis)) and zero(product(mixed_real, orbit))
    assert gram == product(trans(basis), basis) and rank(gram) == dimension
    assert trans(projector) == projector and product(projector, projector) == projector
    assert product(projector, basis) == basis and rank(projector) == dimension
    color = source_color(root)
    actions = []
    for (real, imaginary), receipt in zip(color, data['background_color']):
        re4 = [[entry(real, out, inp) for inp in b4] for out in b4]
        im4 = [[entry(imaginary, out, inp) for inp in b4] for out in b4]
        full = [re + [-x for x in im] for re, im in zip(re4, im4)] + [im + re for re, im in zip(re4, im4)]
        restricted = matrix(receipt['restricted'])
        assert matrix(receipt['full']) == full
        assert product(full, basis) == product(basis, restricted)
        first, second = product(gram, restricted), product(trans(restricted), gram)
        assert zero([[x + y for x, y in zip(a, b)] for a, b in zip(first, second)])
        actions.append(restricted)
    squares = [product(action, action) for action in actions]
    casimir = [[-sum(square[i][j] for square in squares)
                for j in range(dimension)] for i in range(dimension)]
    assert casimir == matrix(data['casimir'])
    doublet = matrix(data['doublet_projector'])
    assert doublet == [[Q(4, 3) * x for x in row] for row in casimir]
    assert product(doublet, doublet) == doublet
    adapted = matrix(data['adapted_basis'])
    assert rank(adapted) == dimension
    singlet, count = data['singlet_dimension'], data['quaternion_block_count']
    assert singlet == dimension - rank(casimir) == 23 and singlet + 4 * count == dimension
    for action, block in zip(actions, map(matrix, data['quaternion_generators'])):
        expected = [[Q(0)] * dimension for _ in range(dimension)]
        for n in range(count):
            for i in range(4):
                for j in range(4):
                    expected[singlet + 4 * n + i][singlet + 4 * n + j] = block[i][j]
        assert product(action, adapted) == product(adapted, expected)
    assert (Q(data['gauge_amplitude_squared']), Q(data['lapse_squared'])) == (Q(18, 25), Q(54, 125))
    previous = json.loads((root / 'Verification/physics/low-energy-phenomenology/coupled-response/results.json').read_text())
    for name, digest in previous['source_sha256'].items():
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest
    old = matrix(previous['subspace_basis_columns'])
    old_real = [row + [Q(0)] * len(row) for row in old] + [[Q(0)] * len(row) + row for row in old]
    extra = matrix(data['additional_projector'])
    assert rank(old_real) == data['previous_real_dimension'] == 40
    assert rank(extra) == data['additional_real_dimension'] == 3
    assert product(projector, old_real) == old_real and zero(product(extra, old_real))
    assert product(extra, extra) == extra and trans(extra) == extra
    assert product(projector, extra) == extra
    for action in data['background_color']:
        assert zero(product(matrix(action['full']), extra))
    return dimension, singlet, count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--controls', action='store_true')
    args = parser.parse_args()
    data = json.loads(args.receipt.read_text())
    dimension, singlet, count = check(args.root, data)
    print(f'PASS independent source/minor check: K has real dimension {dimension}; {singlet} singlets + {count} quaternion blocks.')
    if args.controls:
        mutations = [
            ('complex dimension confused with real dimension', lambda d: d.__setitem__('real_dimension', 40)),
            ('mixed Yukawa row deleted', lambda d: d['mixed_real'][0].__setitem__(0, '1')),
            ('kernel basis corrupted', lambda d: d['basis'][0].__setitem__(0, str(Q(d['basis'][0][0]) + 1))),
            ('source color sign reversed', lambda d: d['quaternion_generators'][0][0].__setitem__(1, '1/2')),
        ]
        for label, mutate in mutations:
            changed = copy.deepcopy(data)
            mutate(changed)
            try:
                check(args.root, changed)
            except AssertionError:
                print('REJECTED:', label)
            else:
                raise AssertionError('Invalid control accepted: ' + label)


if __name__ == '__main__':
    main()
