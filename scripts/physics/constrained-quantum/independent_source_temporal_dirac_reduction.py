#!/usr/bin/env python3
"""Original-density and canonical-graph audit of temporal Dirac reduction.

The reduction producer is not imported. Raw BF, scalar, native Hodge and
full independent-dual matter densities regenerate its temporal equations.
The actual nonlinear update is reconstructed by the previously independent
raw Hamiltonian differential, not copied from the proposed reduction.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_homogeneous_canonical_flow import (
    RawSource, HERE, BASE, ROOT, ROOT_ID, KEYS, ETA, SIGMA, W,
    bindings, clean, rational, zero, eq, dot, decode, encode, hodge,
    source_rates, raw_H_first)


def raw_family(raw):
    n = s.Symbol('n', positive=True)
    shifts = s.Matrix(s.symbols('b1:4', real=True))
    u, alpha, beta, radial = s.symbols('u alpha beta radial', real=True)
    e = s.diag(n, 1, 1, 1); e[1:, 0] = shifts
    q = raw.P61[:, 23]
    phi, momentum = raw.v+u*q, radial*u*q
    psi, chi = raw.psi0.copy(), raw.chi0.copy()
    psi[135] += alpha; chi[126] += beta
    E = s.kronecker_product(raw.principals(e)[0], s.eye(63))
    p = clean(-s.I*chi*E)
    assert not E.diff(n).todok()
    for b in shifts: assert not E.diff(b).todok()
    H, G, inverse = raw.geometry(e)
    eq(H*inverse, s.eye(24))
    current = raw.current(e, psi, chi)
    omega = -inverse*current
    eq(G[:, :16].T*omega, s.zeros(16, 1))
    gravity = s.factor(3*n+dot(current, inverse*current)/2)
    metric = raw.metric(e)
    U = [raw.action(raw.A[i+1, :], raw.rho70)*phi for i in range(3)]
    shift = sum((metric[0, i+1]*U[i] for i in range(3)), s.zeros(70, 1))
    velocity = rational((momentum-shift)/metric[0, 0])
    covariant = [velocity, *U]
    scalar_L = sum(metric[i, j]*dot(covariant[i], covariant[j])/2 for i in range(4) for j in range(4))-n*dot(phi-raw.v, phi-raw.v)
    scalar_H = s.factor(dot(momentum, velocity)-scalar_L)
    magnetic = raw.curvature(raw.A)[3:, :]
    constitutive = rational(-W*hodge(e)/SIGMA)
    electric = rational(-constitutive[:3, :3].inv()*constitutive[:3, 3:]*magnetic)
    curvature = electric.col_join(magnetic)
    eq((constitutive*curvature*raw.Gram)[:3, :], s.zeros(3, 12))
    gauge = s.factor(-dot(curvature, constitutive*curvature*raw.Gram)/2)
    matter = s.factor(-s.re((chi*raw.lower(e, phi, raw.A)*psi)[0]))
    components = dict(gravity=gravity, scalar=scalar_H, gauge=gauge, matter=matter)
    total = s.factor(sum(components.values()))
    a = s.factor((gravity+scalar_H+matter)/n)
    c = s.factor(s.trace(magnetic*raw.Gram*magnetic.T)/(6*SIGMA))
    # Original fixed-velocity stresses independently match fixed-canonical
    # derivatives. In particular E is independent of all four temporal fields.
    coordinates = [n, *shifts]
    constraints = []
    for y in coordinates:
        force_gravity = -3*s.diff(n, y)+dot(omega, H.diff(y)*omega)/2+dot(omega, current.diff(y))
        force_scalar = sum(metric.diff(y)[i, j]*dot(covariant[i], covariant[j])/2 for i in range(4) for j in range(4))-s.diff(n, y)*dot(phi-raw.v, phi-raw.v)
        force_gauge = dot(curvature, constitutive.diff(y)*curvature*raw.Gram)/2
        force_matter = s.re((chi*raw.lower(e, phi, raw.A).diff(y)*psi)[0])
        force = s.cancel(force_gravity+force_scalar+force_gauge+force_matter)
        zero(force+s.diff(total, y))
        constraints.append(force)
    return dict(H=total, F=rational(s.Matrix(constraints)), a=a, c=c, ys=coordinates,
                n=n, shifts=shifts, u=u, alpha=alpha, beta=beta, radial=radial, p=p,
                components=components)


def graph_and_bracket():
    # Arbitrary retained symplectic dimension and arbitrary derivative of the
    # same implicit branch: this is an identity of the graph pullback.
    dimension = s.Symbol('retained_dimension', integer=True, positive=True)
    omega = s.MatrixSymbol('retained_symplectic_form', dimension, dimension)
    DY = s.MatrixSymbol('actual_branch_derivative', 4, dimension)
    Zdd, Zd4, Z4d, Z44 = s.ZeroMatrix(dimension, dimension), s.ZeroMatrix(dimension, 4), s.ZeroMatrix(4, dimension), s.ZeroMatrix(4, 4)
    full_form = s.BlockMatrix([[omega, Zd4, Zd4], [Z4d, Z44, s.Identity(4)], [Z4d, -s.Identity(4), Z44]])
    embedding = s.BlockMatrix([[s.Identity(dimension)], [DY], [Z4d]])
    assert s.block_collapse(embedding.T*full_form*embedding) == omega
    J, K = s.MatrixSymbol('actual_temporal_J', 4, 4), s.MatrixSymbol('actual_F_Poisson', 4, 4)
    # Eliminate the first four equations before the second four; K remains
    # arbitrary. This constructs the inverse's action on every right-hand side.
    top, bottom = s.MatrixSymbol('primary_rhs', 4, 1), s.MatrixSymbol('secondary_rhs', 4, 1)
    second = -J.T.I*top
    first = J.I*(bottom-K*second)
    assert s.expand(-J.T*second) == top
    assert s.expand(J*first+K*second) == bottom
    inverse = s.BlockMatrix([[J.I*K*J.T.I, J.I], [-J.T.I, Z44]])
    delta = s.BlockMatrix([[Z44, -J.T], [J, K]])
    identity = s.BlockMatrix([[s.Identity(4), Z44], [Z44, s.Identity(4)]])
    assert s.block_collapse(delta*inverse) == identity
    assert s.block_collapse(inverse*delta) == identity
    f, g = s.MatrixSymbol('f_secondary_bracket', 1, 4), s.MatrixSymbol('secondary_g_bracket', 4, 1)
    correction = s.BlockMatrix([[s.ZeroMatrix(1, 4), f]])*inverse*s.BlockMatrix([[s.ZeroMatrix(4, 1)], [g]])
    assert s.block_collapse(correction) == s.ZeroMatrix(1, 1)
    # The implicit derivative identity pays the same original temporal update.
    forcing = s.MatrixSymbol('whole_state_constraint_forcing', 4, 1)
    assert s.expand(J*(-J.I*forcing)+forcing) == s.ZeroMatrix(4, 1)
    return {'arbitrary_retained_dimension_pullback': True, 'arbitrary_actual_secondary_Poisson_K': True,
            'all_rhs_elimination_and_two_sided_inverse': True, 'remaining_Dirac_correction_exactly_zero': True,
            'original_one_form_pullback': 'theta_z+p_y dY(z) restricts exactly to theta_z on p_y=0',
            'reduced_derivative': 'd H(Y(z),z)=H_z dz+H_y dY=H_z dz because H_y=-F=0',
            'local_existence': 'The independently certified original analytic constraint map has det J=800/3 at the nonempty literal source; its analytic implicit branch is generated locally and retains the original positive coframe orientation.'}


def main():
    began = time.monotonic()
    path = HERE/'source_temporal_dirac_reduction.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ['independent_source_coframe_initial_constraints.json', 'independent_source_homogeneous_canonical_flow.json',
            'independent_source_scalar_gauss_reduction.json', 'independent_source_joint_local_quantum.json']
    for name in paid: count += bindings(json.loads((HERE/name).read_text()))
    raw = RawSource(); assert raw.hashes == candidate['source_sha256']
    family = raw_family(raw)
    H, F, a, c, ys = [family[k] for k in ('H', 'F', 'a', 'c', 'ys')]
    n, shifts, u, alpha, beta, radial = [family[k] for k in ('n', 'shifts', 'u', 'alpha', 'beta', 'radial')]
    N = s.sympify(raw.active['source_lapse'])
    at_source = {n: N, u: 0, alpha: 0, beta: 0, radial: 0, **dict.fromkeys(shifts, 0)}
    eq(F.subs(at_source), s.zeros(4, 1))
    J = rational(F.jacobian(ys).subs(at_source))
    eq(J, decode(candidate['source_J'])); zero(J.det()-s.Rational(800, 3))
    K = s.zeros(4)
    for value, (i, j) in zip(s.symbols('actual_F_bracket0:6', real=True), ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))):
        K[i, j], K[j, i] = value, -value
    delta = s.zeros(4).row_join(-J.T).col_join(J.row_join(K))
    inverse = rational(delta.inv(method='DM'))
    eq(delta*inverse, s.eye(8)); eq(inverse*delta, s.eye(8))
    eq(inverse[4:, 4:], s.zeros(4))
    eq(inverse, decode(candidate['actual_source_inverse'], {str(z): z for z in K.free_symbols}))
    zero(delta.det()-s.sympify(candidate['source_eight_constraint_determinant']))
    generic = graph_and_bracket()
    print('PASS raw four-density stresses, original temporal Jacobian and general canonical Dirac graph', flush=True)
    flow = json.loads((HERE/'source_homogeneous_canonical_flow.json').read_text())
    fields = {key: decode(flow['datum'][key]) for key in KEYS}
    rates, _, _, _, _, _ = source_rates(raw, fields)
    temporal = [s.Symbol('actual_n', positive=True), *s.symbols('actual_shift1:4', real=True)]
    varying = dict(fields); varying['e'] = fields['e'].copy(); varying['e'][:, 0] = s.Matrix(temporal)
    point = dict(zip(temporal, fields['e'][:, 0]))
    tangent = raw_H_first(raw, varying, rates)['value']
    actual_F = s.Matrix([-s.diff(tangent.v, y) for y in temporal])
    actual_J = rational(actual_F.jacobian(temporal).subs(point))
    forcing = rational(s.Matrix([-s.diff(tangent.d, y).subs(point) for y in temporal]))
    velocity, free = actual_J.gauss_jordan_solve(-forcing); assert free.rows == 0
    velocity = rational(velocity)
    expected = candidate['actual_nonlinear_update']
    eq(actual_J, decode(expected['Jacobian'])); eq(forcing, decode(expected['forcing']))
    eq(velocity, decode(expected['time_rate'])); assert velocity.todok()
    eq(actual_F.subs(point), s.zeros(4, 1)); eq(actual_J*velocity+forcing, s.zeros(4, 1))
    print('PASS actual nonlinear eight-field source tangent and generated temporal update from raw Hamiltonian', flush=True)
    solved = dict.fromkeys(shifts, 0)
    zero(H.subs(solved)-n*a-3*c/n)
    aa = s.Symbol('generated_a', positive=True)
    root = s.sqrt(3*c/aa)
    reduced = s.simplify((n*aa+3*c/n).subs(n, root))
    zero(reduced-s.sympify(candidate['explicit_source_family']['reduced_energy'], locals={'generated_a': aa}))
    zero(s.diff(reduced, aa)-root); assert s.simplify(s.diff(reduced, aa, 2)) != 0
    zero(s.diff(n*aa+3*c/n, n).subs(n, root))
    fixture = {u: s.Rational(1, 4), alpha: 1, beta: 1, radial: s.Rational(1, 3), **solved}
    actual_a = s.factor(a.subs(fixture)); assert actual_a > 0
    fixture[n] = s.sqrt(3*c/actual_a)
    eq(F.subs(fixture).applyfunc(s.simplify), s.zeros(4, 1))
    zero(H.subs(fixture)-reduced.subs(aa, actual_a))
    zero(actual_a-s.sympify(candidate['explicit_source_family']['nonzero_scalar_momentum_and_independent_matter_fixture']))
    print('PASS original positive nonlinear branch and reduced energy with nonzero scalar momentum and independent matter', flush=True)
    paths = [Path(__file__), path, HERE/'source_temporal_dirac_reduction.py',
             HERE/'independent_source_homogeneous_canonical_flow.py', HERE/'independent_source_joint_temporal_rates.py',
             HERE/'independent_source_gauge_legendre.py', HERE/'independent_source_lorentz_contact.py',
             HERE/'source_homogeneous_canonical_flow.json', BASE/'active-gauge/receipt.json', BASE/'occupied-response/receipt.json']+[HERE/name for name in paid]
    result = {'verdict': 'CERTIFIED_ORIGINAL_TEMPORAL_SECOND_CLASS_CANONICAL_REDUCTION', 'root': ROOT_ID,
        'source_sha256': raw.hashes, 'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'Original epsilon BF/Lorentz density, raw scalar Legendre map, original4x4 Hodge, full252 independent-dual matter; fixed-velocity stresses before canonical differentiation; raw whole-state tangent and direct8x8 inversion',
        'original_four_density_components': {key: str(value) for key, value in family['components'].items()},
        'source_temporal_Jacobian': encode(J), 'source_determinant': str(J.det()), 'canonical_graph': generic,
        'actual_nonlinear_update': {'Jacobian': encode(actual_J), 'forcing': encode(forcing), 'rate': encode(velocity)},
        'positive_source_branch': {'generated_a': str(a), 'c': str(c), 'reduced_energy': str(reduced), 'actual_a': str(actual_a)},
        'claim': 'The source-local homogeneous temporal primary/secondary pairs are second class. Their actual analytic branch preserves the retained canonical one-form and bracket and generates the original constrained flow.',
        'scope': 'Classical canonical reduction and its quantum input. The three stabilizer rows and ordering of the source-dependent reduced energy remain; no simultaneous first-class temporal physical-state kernel, Hilbert evolution or composite measure is installed.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_temporal_dirac_reduction.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent temporal Dirac reduction', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
