#!/usr/bin/env python3
"""Actual simultaneous spatial/spin/color rotations of all 289 source coordinates."""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import sys

import sympy as s

PARENT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PARENT))
from compute import source, active, source_matrices, PAIRS, ETA, GAMMA, COLOR, J
from compute import number, ZERO, stringify
from slice_checks import wedge_matrix, wedge_tangent


def build_generators(root, receipt):
    source_matrices(root)
    _, vacuum, _, _ = source.parse_source(root)
    raw = source.generators([(0, 1, 2), (3, 4)])
    fundamental = [s.Matrix(m)*(s.I if imaginary else 1) for _, imaginary, m in raw]
    gram = s.Matrix(12, 12, lambda i, j: s.re(-s.trace(fundamental[i]*fundamental[j])))
    inverse_gram = gram.inv()
    import itertools
    b4 = list(itertools.combinations(range(7), 4))
    vc = s.Matrix([vacuum.get(word, 0) for word in b4])
    v = vc.col_join(s.zeros(35, 1))
    rho4 = [active.realify(active.exterior(t, 4)) for t in fundamental]
    orbit = s.Matrix.hstack(*[a*v for a in rho4])
    inclusion = orbit[:, receipt['J_independent_columns']]
    inclusion_left = (inclusion.T*inclusion).inv()*inclusion.T
    groups = defaultdict(dict)
    for i, field in enumerate(receipt['fields']):
        groups[field['group']][tuple(field['coordinate'])] = i
    matrix = lambda rows: s.Matrix([[s.sympify(v) for v in row] for row in rows])
    e0 = matrix(receipt['actual_background']['coframe'])
    a0 = matrix(receipt['actual_background']['gauge_connection'])
    omega0 = matrix(receipt['actual_background']['lowered_Lorentz_connection'])
    prepared = s.Matrix([s.sympify(v) for v in receipt['actual_background']['primal_H']])
    spin = s.sympify(receipt['actual_background']['dual_multiple'])
    lorentz_basis = []
    for a, b in PAIRS:
        t = s.zeros(4)
        t[a, b], t[b, a] = ETA[a, a], -ETA[b, b]
        lorentz_basis.append(t)
    exterior0 = wedge_matrix(e0)
    hodge0 = exterior0.inv()*J*exterior0
    gauge0 = [sum((a0[mu, c]*fundamental[c] for c in range(12)), s.zeros(7)) for mu in range(4)]
    curvature = s.Matrix(6, 12, lambda i, j: 0)
    for pair, (mu, nu) in enumerate(PAIRS):
        commutator = gauge0[mu]*gauge0[nu]-gauge0[nu]*gauge0[mu]
        curvature[pair, :] = (inverse_gram*s.Matrix([s.re(-s.trace(t*commutator)) for t in fundamental])).T
    gauge_b0 = -hodge0*curvature/s.sympify(receipt['source_coupling'])
    omega_matrix = [sum((omega0[mu, pair]*lorentz_basis[pair] for pair in range(6)), s.zeros(4)) for mu in range(4)]
    gravity_curvature = s.Matrix(6, 6, lambda i, j: ETA[PAIRS[i][0], PAIRS[i][0]]*
        (omega_matrix[PAIRS[j][0]]*omega_matrix[PAIRS[j][1]]-
         omega_matrix[PAIRS[j][1]]*omega_matrix[PAIRS[j][0]])[PAIRS[i][0], PAIRS[i][1]])
    gravity_b0 = J*exterior0
    multiplier0 = J*gravity_b0-s.diag(-1, -1, -1, 1, 1, 1)*gravity_curvature
    result = []
    for axis in range(3):
        spatial = lorentz_basis[axis+3]
        color = s.diag(COLOR[axis], s.zeros(5))
        color_action = s.Matrix(12, 12, lambda i, j: 0)
        for j, t in enumerate(fundamental):
            commutator = -color*t+t*color
            column = inverse_gram*s.Matrix([s.re(-s.trace(g*commutator)) for g in fundamental])
            color_action[:, j] = column
            assert sum((column[i]*fundamental[i] for i in range(12)), s.zeros(7)) == commutator
        scalar = active.realify(active.exterior(-color, 4))
        scalar_small = inclusion_left*scalar*inclusion
        assert scalar*v == s.zeros(70, 1)
        assert scalar*inclusion == inclusion*scalar_small
        spacetime_two = wedge_tangent(s.eye(4), spatial)
        assert spacetime_two.T == -spacetime_two
        assert spacetime_two*J == J*spacetime_two
        spin_action = -GAMMA[PAIRS[axis+3][0]]*GAMMA[PAIRS[axis+3][1]]/2
        internal_h = -s.diag(COLOR[axis], s.zeros(1))
        matter = s.kronecker_product(spin_action, s.eye(3))+s.kronecker_product(s.eye(4), internal_h)
        chirality = s.kronecker_product(s.diag(-1, -1, 1, 1), s.eye(3))
        assert matter*chirality == chirality*matter
        assert matter*prepared == s.zeros(12, 1)
        assert spin*prepared.T*matter == s.zeros(1, 12)
        lorentz_action = s.Matrix(6, 6, lambda i, j: ETA[PAIRS[i][0], PAIRS[i][0]]*
            (-spatial*lorentz_basis[j]+lorentz_basis[j]*spatial)[PAIRS[i][0], PAIRS[i][1]])
        assert -spatial*e0+e0*spatial == s.zeros(4)
        assert spatial.T*a0+a0*color_action.T == s.zeros(4, 12)
        assert spatial.T*omega0+omega0*lorentz_action.T == s.zeros(4, 6)
        assert -spacetime_two*gravity_b0+gravity_b0*spacetime_two == s.zeros(6)
        assert -spacetime_two*multiplier0+multiplier0*spacetime_two == s.zeros(6)
        assert spacetime_two.T*gauge_b0+gauge_b0*color_action.T == s.zeros(6, 12)
        generator = s.MutableSparseMatrix(289, 289, {})

        def put(group, block):
            indices = list(groups[group].values())
            assert block.shape == (len(indices), len(indices))
            for (i, j), value in s.SparseMatrix(block).todok().items():
                generator[indices[i], indices[j]] = value

        put('scalar_J', scalar_small)
        put('gauge_A', s.kronecker_product(spatial.T, s.eye(12))+s.kronecker_product(s.eye(4), color_action))
        put('coframe', s.kronecker_product(-spatial, s.eye(4))+s.kronecker_product(s.eye(4), spatial.T))
        put('primal_H', active.realify(matter))
        put('dual_H', active.realify(-matter.T))
        put('Lorentz', s.kronecker_product(spatial.T, s.eye(6))+s.kronecker_product(s.eye(4), lorentz_action))
        gravity = s.kronecker_product(-spacetime_two, s.eye(6))+s.kronecker_product(s.eye(6), spacetime_two.T)
        put('gravity_B', gravity)
        put('multiplier', gravity)
        put('gauge_B', s.kronecker_product(spacetime_two.T, s.eye(12))+s.kronecker_product(s.eye(6), color_action))
        result.append((spatial, s.SparseMatrix(generator)))
    for i, j, k in [(0, 1, 2), (1, 2, 0), (2, 0, 1)]:
        assert result[i][1]*result[j][1]-result[j][1]*result[i][1] == result[k][1]
    return result


def lie_check(operator, spatial, generator):
    rows = defaultdict(list)
    for (i, j), value in generator.todok().items():
        rows[i].append((j, number(value)))
    total = {}

    def add(key, value):
        total[key] = total.get(key, ZERO)+value

    for (i, j, powers), value in operator.items():
        for row, entry in rows[i]:
            add((row, j, powers), entry*value)
        for column, entry in rows[j]:
            add((i, column, powers), value*entry)
        # Momentum transforms as p -> R^T p for the actual coordinate pullback.
        for differentiated, exponent in enumerate(powers):
            if exponent:
                for other in range(4):
                    if spatial[other, differentiated]:
                        new = list(powers)
                        new[differentiated] -= 1
                        new[other] += 1
                        add((i, j, tuple(new)), exponent*number(spatial[other, differentiated])*value)
    assert not any(total.values()), [(key, stringify(value)) for key, value in total.items() if value]
    return len(total)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    receipt = json.loads(args.receipt.read_text())
    generators = build_generators(args.root, receipt)
    operator = {(i, j, tuple(p)): number(s.sympify(value)) for i, j, p, value in receipt['Fourier_Jacobi_entries']}
    counts = [lie_check(operator, spatial, generator) for spatial, generator in generators]
    result = {'scope': 'ORIGINAL_289_FIELD_SIMULTANEOUS_SPATIAL_SPIN_COLOR_ROTATION_GENERATORS',
        'formula': 'Q_i^T H(p)+H(p)Q_i+(M_i^T p).d_p H(p)=0',
        'source_background_fixed': ['v', 'primal_H', 'independent_dual_H', 'coframe', 'gauge_connection',
                                    'Lorentz_connection', 'gravity_B', 'multiplier', 'gauge_B'],
        'source_spacetime_two_form_Hodge_commutes_spatial_rotation': True,
        'source_actual_chiral_phase_commutes_with_matter_rotation': True,
        'Lie_algebra_brackets_verified': True, 'whole_289_symbol_coefficients_zero': counts,
        'generators': [{'spatial_matrix': [[str(v) for v in row] for row in spatial.tolist()],
                        'field_generator': [[int(i), int(j), str(value)] for (i, j), value in generator.todok().items()]}
                       for spatial, generator in generators],
        'local_diffeomorphism_invariance_used': False, 'finite_rotation_verified_here': False}
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print('PASS: all three original simultaneous rotation generators preserve the actual background and the full 289-field symbol coefficientwise')
    print('PASS: Q_i^T H + H Q_i + (M_i^T p).d_p H = 0;', counts, 'coefficient slots checked')


if __name__ == '__main__':
    main()
