#!/usr/bin/env python3
"""Symbolic source-coordinate checks of the homogeneous initial-slice candidate.

Run with: uv run --with sympy==1.14.0 python slice_checks.py --output FILE
This checks finite normal forms; it is not a Lean proof of the differential
identification or a certificate of a spacetime solution.
"""
import argparse
import json
import re
from pathlib import Path

import sympy as s

R = s.Rational
PAIRS = [(0, 1), (0, 2), (0, 3), (2, 3), (3, 1), (1, 2)]
TRIPLES = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]
ETA = s.diag(-1, 1, 1, 1)
J = s.zeros(6)
W = s.zeros(6)
for j in range(3):
    J[j, j + 3], J[j + 3, j] = 1, -1
    W[j, j + 3] = W[j + 3, j] = 1
PAIR_SIGN = [-1, -1, -1, 1, 1, 1]
GAMMA = [
    s.Matrix([[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]]),
    s.Matrix([[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]]),
    s.Matrix([[0, 0, 0, -s.I], [0, 0, s.I, 0], [0, -s.I, 0, 0], [s.I, 0, 0, 0]]),
    s.Matrix([[0, 0, 1, 0], [0, 0, 0, -1], [1, 0, 0, 0], [0, -1, 0, 0]])]
COLOR = [s.Matrix([[0, s.I/2], [s.I/2, 0]]),
         s.Matrix([[0, R(1, 2)], [-R(1, 2), 0]]),
         s.diag(s.I/2, -s.I/2)]


def source_matrices(root):
    """Compare the independent coordinate transcription with current source literals."""
    core = root / 'Lean/SaturationMonoid/PhysicsCore'

    def parse(body):
        rows = []
        for row in body.split(';'):
            entries = []
            for value in row.split(','):
                value = value.strip().replace('Complex.I', 'I')
                if not re.fullmatch(r'[0-9I+*/()\s-]+', value):
                    raise ValueError('Unsupported source matrix entry: ' + value)
                entries.append(s.sympify(value, locals={'I': s.I}))
            rows.append(entries)
        return s.Matrix(rows)

    gamma_source = (core / 'DiracCliffordRepresentation.lean').read_text()
    for name, matrix in zip(['Zero', 'One', 'Two', 'Three'], GAMMA):
        match = re.search(r'def diracGamma' + name + r'\s*:.*?:=\s*!!\[(.*?)\]',
                          gamma_source, re.S)
        assert match and parse(match.group(1)) == matrix, 'Source Gamma changed: ' + name
    color_source = (core / 'Stage9C/Material/SpinPair/ColorDoublet.lean').read_text()
    block = color_source.split('def sourceColorPauli', 1)[1].split('theorem', 1)[0]
    matrices = [parse(body) for body in re.findall(r'!!\[(.*?)\]', block, re.S)]
    assert matrices == COLOR, 'Source Pauli action changed'


def wedge_matrix(e):
    return s.Matrix(6, 6, lambda i, j:
        e[PAIRS[i][0], PAIRS[j][0]] * e[PAIRS[i][1], PAIRS[j][1]] -
        e[PAIRS[i][0], PAIRS[j][1]] * e[PAIRS[i][1], PAIRS[j][0]])


def wedge_tangent(e, h):
    return s.Matrix(6, 6, lambda i, j:
        h[PAIRS[i][0], PAIRS[j][0]] * e[PAIRS[i][1], PAIRS[j][1]] +
        e[PAIRS[i][0], PAIRS[j][0]] * h[PAIRS[i][1], PAIRS[j][1]] -
        h[PAIRS[i][0], PAIRS[j][1]] * e[PAIRS[i][1], PAIRS[j][0]] -
        e[PAIRS[i][0], PAIRS[j][1]] * h[PAIRS[i][1], PAIRS[j][0]])


def gravity_wedge(a, b):
    return sum(PAIR_SIGN[i] * (a.row(i) * W * b.row(i).T)[0] for i in range(6))


def ordered(two_form, a, b):
    if a == b:
        return s.zeros(2)
    if (a, b) in PAIRS:
        return two_form[PAIRS.index((a, b))]
    return -two_form[PAIRS.index((b, a))]


def calculate(n, p, acceleration, gauge_acceleration, phase_sign=1):
    spin, gauge, coupling, weight = s.sqrt(2), 3*s.sqrt(2)/5, R(1, 2), 4
    e = s.diag(n, 1, 1, 1)
    inverse = e.inv()
    exterior = wedge_matrix(e)
    hodge = exterior.inv() * J * exterior
    metric_inverse = (e.T * ETA * e).inv()

    # Actual Levi--Civita derivative from the metric Hessian of exp(k t²/2).
    def metric_second(a, b, mu, nu):
        return 2*acceleration if a == b and a > 0 and mu == nu == 0 else 0

    def christoffel_derivative(mu, a, nu, b):
        return metric_inverse[a, a] * (metric_second(a, b, nu, mu) +
            metric_second(a, nu, b, mu) - metric_second(nu, b, a, mu)) / 2

    omega = [s.zeros(4) for _ in range(4)]
    for mu in range(1, 4):
        a, b = PAIRS[mu + 2]
        omega[mu][a, b], omega[mu][b, a] = spin, -spin
    curvature = s.zeros(6)
    for i, (a, b) in enumerate(PAIRS):
        for j, (mu, nu) in enumerate(PAIRS):
            lc = e[a, a] / e[b, b] * (christoffel_derivative(mu, a, nu, b) -
                christoffel_derivative(nu, a, mu, b))
            curvature[i, j] = s.simplify(ETA[a, a] *
                (lc + (omega[mu]*omega[nu] - omega[nu]*omega[mu])[a, b]))
    gravity_b = J * exterior
    multiplier = J * gravity_b - s.diag(*PAIR_SIGN) * curvature

    # Generated gauge auxiliary B = -star_e(F)/sigma; no mass inverse supplied.
    f = s.zeros(6, 3)
    for i in range(3):
        f[i + 3, i] = -gauge**2
    b = -hodge * f / coupling

    prepared = s.Matrix([0, 1, -1, 0, 0, 1, -1, 0])
    dual = spin * prepared.T
    chirality = s.diag(1, 1, -1, -1)
    phase_rate = phase_sign * 3*n*(spin - gauge)/2
    rate_operator = s.I*phase_rate*s.kronecker_product(chirality, s.eye(2))
    gamma = [s.kronecker_product(g, s.eye(2)) for g in GAMMA]
    rotations = [GAMMA[2]*GAMMA[3], GAMMA[3]*GAMMA[1], GAMMA[1]*GAMMA[2]]
    connection = [s.zeros(8)] + [spin/2*s.kronecker_product(rotations[i], s.eye(2)) +
        gauge*s.kronecker_product(s.eye(4), COLOR[i]) for i in range(3)]
    covariant = [rate_operator*prepared] + [connection[i]*prepared for i in range(1, 4)]
    load = s.Matrix(4, 4, lambda a, mu: s.simplify((dual*s.I*gamma[a]*covariant[mu])[0]))
    forward = sum((s.I*gamma[mu]*covariant[mu]/e[mu, mu] for mu in range(4)), s.zeros(8, 1))
    adjoint = sum((dual*s.I*gamma[mu]*connection[mu]/e[mu, mu] for mu in range(4)),
        s.zeros(1, 8)) - dual*rate_operator*s.I*gamma[0]/n
    scalar_load = weight*p**2
    forces = []
    for row in range(4):
        for col in range(4):
            h = s.zeros(4)
            h[row, col] = 1
            di = -inverse*h*inverse
            dv = n*s.trace(inverse*h)
            de = wedge_tangent(e, h)
            dh = -exterior.inv()*de*hodge + exterior.inv()*J*de
            dg = h.T*ETA*e + e.T*ETA*h
            dgi = -metric_inverse*dg*metric_inverse
            gravity = -gravity_wedge(multiplier, J*de)
            gauge_force = -coupling/4*sum((b.col(j).T*W*dh*b.col(j))[0] for j in range(3))
            matter = dv*s.trace(inverse*load) + n*s.trace(di*load)
            scalar = scalar_load/2*(dv*metric_inverse[0, 0] + n*dgi[0, 0])
            forces.append(s.factor(gravity + gauge_force + matter + scalar))

    # Full exterior d_A B in the source SU(2) sector, and its matter current.
    gauge_connection = [s.zeros(2)] + [gauge*x for x in COLOR]
    two_form = [sum((b[j, c]*COLOR[c] for c in range(3)), s.zeros(2)) for j in range(6)]
    # Apply the same inverse constitutive map to the curvature time jet.
    curvature_rate = s.zeros(6, 3)
    for i in range(3):
        curvature_rate[i, i] = gauge_acceleration
    auxiliary_rate = -hodge * curvature_rate / coupling
    derivative = [sum((auxiliary_rate[j, c]*COLOR[c] for c in range(3)), s.zeros(2))
                  for j in range(6)]
    current = [[s.simplify((n*dual*s.I*gamma[mu]/e[mu, mu] *
        s.kronecker_product(s.eye(4), COLOR[c])*prepared)[0]) for c in range(3)] for mu in range(4)]
    gauge_residual = []
    for triple in TRIPLES:
        value = s.zeros(2)
        for mu, nu, rho in [triple, triple[1:]+triple[:1], triple[2:]+triple[:2]]:
            leg = ordered(two_form, nu, rho)
            value += gauge_connection[mu]*leg - leg*gauge_connection[mu]
            if mu == 0:
                value += ordered(derivative, nu, rho)
        missing = next(i for i in range(4) if i not in triple)
        value += sum((2*(-1)**missing*current[missing][c]*COLOR[c] for c in range(3)), s.zeros(2))
        gauge_residual.extend(list(value))
    return curvature, forces, list(forward), list(adjoint), gauge_residual


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[4])
    args = parser.parse_args()
    source_matrices(args.root)
    n = s.Symbol('n', positive=True)
    p = s.Symbol('p', real=True)
    n_squared = R(54, 125) + R(10, 9)*p**2
    scale_acceleration = -R(2, 3)*p**2
    gauge_acceleration = 2*s.sqrt(2) - 2*(3*s.sqrt(2)/5)**3/n**2

    def reduced(value):
        numerator, denominator = s.cancel(value).as_numer_denom()
        return s.factor(s.rem(numerator, n**2 - n_squared, n)) / denominator

    data = calculate(n, p, scale_acceleration, gauge_acceleration)
    for name, values in zip(['coframe', 'primal', 'adjoint', 'gauge'], data[1:]):
        residual = [reduced(v) for v in values]
        assert all(v == 0 for v in residual), (name, residual)
    assert data[0] == s.diag(*([R(2, 3)*p**2/n]*3 + [-2]*3))
    controls = {}
    for name, k, ga, sign, block in [
        ('remove_scale_acceleration', 0, gauge_acceleration, 1, 1),
        ('remove_gauge_acceleration', scale_acceleration, 0, 1, 4),
        ('reverse_matter_phase', scale_acceleration, gauge_acceleration, -1, 2)]:
        failure = calculate(n, p, k, ga, sign)[block]
        controls[name] = any(s.simplify(reduced(v).subs(p, 1)) != 0 for v in failure)
        assert controls[name], name
    fixed_clock = [s.simplify(v.subs(n, s.sqrt(R(54, 125)))) for v in data[1]]
    controls['remove_clock_response'] = any(s.simplify(v.subs(p, 1)) != 0 for v in fixed_clock)
    assert controls['remove_clock_response']
    result = {
        'scope': 'SYMBOLIC_INITIAL_SLICE_NORMAL_FORMS_NOT_LEAN_DIFFERENTIAL_IDENTIFICATION_OR_PDE_SOLUTION',
        'sympy': s.__version__,
        'input': {'scalar_velocity': 'p', 'source_scalar_norm_squared': 4,
                  'clock_squared': str(n_squared), 'scale_acceleration': str(scale_acceleration),
                  'gauge_acceleration': str(gauge_acceleration)},
        'curvature': [[str(v) for v in data[0].row(i)] for i in range(6)],
        'verified_zero_counts': {'coframe_directions': 16, 'primal_components': 8,
                                 'independent_dual_components': 8, 'gauge_matrix_entries': 16},
        'negative_controls_rejected': controls,
        'analytic_identifications_required': ['Cartan jet from primitive coframe and spin data',
            'invariant source subspace and vanishing transverse/Yukawa components',
            'scalar Euler at zero scalar displacement and zero scalar acceleration'],
        'full_spacetime_solution': False}
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print('PASS: 36 curvature entries; 16 coframe, 8 primal, 8 dual, 16 gauge entries; four controls')


if __name__ == '__main__':
    main()
