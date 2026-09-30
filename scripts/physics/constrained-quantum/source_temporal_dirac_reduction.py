#!/usr/bin/env python3
"""Eliminate the source temporal coframe second-class pairs canonically.

The original four temporal equations have a nonzero source Jacobian. Their
eight primary/secondary Poisson rows therefore remove the four temporal
coframe variables and their momenta without changing the remaining bracket.
The actual source branch, Hamiltonian and its time update are consumed below.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_coframe_initial_constraints import SourceCoframeInitialConstraints
from source_lorentz_contact import clean, equal, encode


def zero(value):
    assert s.simplify(value) == 0


def inverse_blocks(J, K):
    Ji = J.inv()
    delta = s.zeros(4).row_join(-J.T).col_join(J.row_join(K))
    inverse = (Ji*K*Ji.T).row_join(Ji).col_join((-Ji.T).row_join(s.zeros(4)))
    equal(clean(delta*inverse), s.eye(8)); equal(clean(inverse*delta), s.eye(8))
    equal(inverse[4:, 4:], s.zeros(4))
    return delta, clean(inverse)


def generic_identity():
    J, K = s.MatrixSymbol('J', 4, 4), s.MatrixSymbol('K', 4, 4)
    z = s.ZeroMatrix(4, 4)
    D = s.BlockMatrix([[z, -J.T], [J, K]])
    I = s.BlockMatrix([[J.I*K*J.T.I, J.I], [-J.T.I, z]])
    for product in (D*I, I*D):
        collapsed = s.block_collapse(product)
        assert collapsed == s.BlockMatrix([[s.Identity(4), z], [z, s.Identity(4)]])
    # K is the actual {F,F} remaining-variable bracket, not assumed zero.
    f, g = s.MatrixSymbol('f_F_bracket', 1, 4), s.MatrixSymbol('F_g_bracket', 4, 1)
    correction = s.BlockMatrix([[s.ZeroMatrix(1, 4), f]])*I*s.BlockMatrix([[s.ZeroMatrix(4, 1)], [g]])
    assert s.block_collapse(correction) == s.ZeroMatrix(1, 1)


def main():
    started = time.monotonic(); generic_identity()
    source = SourceCoframeInitialConstraints()
    n = s.Symbol('n', positive=True); shift = s.Matrix(s.symbols('b1:4', real=True))
    u, alpha, beta, radial = s.symbols('u alpha beta radial', real=True)
    fields = source.fields(n, shift, u, alpha, beta, radial)
    original = source.hamiltonian(fields)
    H = s.factor(original['value'])
    ys = [n, *shift]
    F = s.Matrix([-s.diff(H, y) for y in ys])
    at_source = {u: 0, alpha: 0, beta: 0, radial: 0, n: source.N, **dict.fromkeys(shift, 0)}
    Js = clean(F.jacobian(ys).subs(at_source))
    equal(F.subs(at_source), s.zeros(4, 1))
    equal(Js, s.diag(-s.sqrt(30), *[-2*s.sqrt(30)/3]*3))
    zero(Js.det()-s.Rational(800, 3))
    K = s.zeros(4)
    labels = s.symbols('actual_F_bracket0:6', real=True)
    for v, (i, j) in zip(labels, ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))):
        K[i, j], K[j, i] = v, -v
    delta, inverse = inverse_blocks(Js, K)
    zero(delta.det()-s.Rational(640000, 9))
    print('PASS actual original four temporal rows and eight second-class Poisson inverse for arbitrary retained bracket', flush=True)
    # The same finite-dimensional analytic source branch used by the original
    # homogeneous Cauchy producer supplies Y(z); it is not a new clock choice.
    homogeneous = json.loads((HERE/'source_homogeneous_canonical_flow.json').read_text())
    current_J = decode(homogeneous['temporal_Jacobian'])
    inverse_blocks(current_J, K)
    current_force = decode(homogeneous['temporal_forcing'])
    current_rate = decode(homogeneous['complete_rates']['e'])[:, 0]
    equal(clean(current_J*current_rate+current_force), s.zeros(4, 1))
    assert current_J.det() != 0 and current_rate.todok()
    # Explicit non-polynomial restriction of the actual branch, with the
    # original nonzero scalar momentum and independent matter data retained.
    a = source.clock_coefficient(u, alpha, beta, radial)
    avar = s.Symbol('generated_a', positive=True)
    independent_H = n*avar+3*source.c/n
    clock = s.sqrt(3*source.c/avar)
    reduced = s.simplify(independent_H.subs(n, clock))
    zero(reduced-2*s.sqrt(3*source.c*avar))
    zero(s.diff(independent_H, n).subs(n, clock))
    zero(s.diff(reduced, avar)-clock)
    zero(s.diff(reduced, avar, 2)+clock/(2*avar))
    equal(clean(F[1:, :].subs(dict.fromkeys(shift, 0))), s.zeros(3, 1))
    zero(H.subs(dict.fromkeys(shift, 0))-n*a-3*source.c/n)
    actual_a = s.factor(a.subs({u: s.Rational(1, 4), alpha: 1, beta: 1, radial: s.Rational(1, 3)}))
    actual_n = s.sqrt(3*source.c/actual_a)
    actual = {u: s.Rational(1, 4), alpha: 1, beta: 1, radial: s.Rational(1, 3), n: actual_n,
              **dict.fromkeys(shift, 0)}
    equal(F.subs(actual).applyfunc(s.simplify), s.zeros(4, 1))
    zero(H.subs(actual)-reduced.subs(avar, actual_a))
    print('PASS same-source analytic temporal branch, original multiplier update and reduced nonlinear energy', flush=True)
    inputs = [HERE/name for name in ('source_temporal_dirac_reduction.py', 'source_coframe_initial_constraints.py',
        'source_coframe_initial_constraints.json', 'independent_source_coframe_initial_constraints.json',
        'source_homogeneous_canonical_flow.py', 'source_homogeneous_canonical_flow.json',
        'independent_source_homogeneous_canonical_flow.json', 'source_scalar_gauss_reduction.py',
        'source_scalar_gauss_reduction.json', 'independent_source_scalar_gauss_reduction.json',
        'source_joint_local_quantum.json', 'independent_source_joint_local_quantum.json')]
    saved = json.loads((HERE/'source_coframe_initial_constraints.json').read_text())
    bindings = {}
    for receipt in (saved, homogeneous):
        for key in ('source_sha256', 'input_sha256'):
            for name, expected in receipt.get(key, {}).items():
                assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == expected, name
                bindings[name] = expected
    bindings.update({str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs})
    result = {'root': ROOT_ID, 'source_sha256': saved['source_sha256'], 'input_sha256': bindings,
        'scope': 'ORIGINAL_HOMOGENEOUS_TEMPORAL_SECOND_CLASS_REDUCTION_WITH_CANONICAL_REMAINING_BRACKET',
        'primary': 'p_y=Pi_e[:,0]=0, y=e[:,0]', 'secondary': 'F=-partial_y H_bulk=0 at fixed original remaining canonical coordinates',
        'source_J': encode(Js), 'source_J_determinant': str(s.simplify(Js.det())),
        'source_eight_constraint_determinant': str(s.Rational(640000, 9)),
        'Poisson_matrix': 'Delta=[[0,-J^T],[J,K]], J=partial_y F, K_ab={F_a,F_b}_z retained without setting it to zero',
        'Poisson_inverse': '[[J^-1 K J^-T,J^-1],[-J^-T,0]]',
        'generic_both_inverse_identities_and_remaining_bracket': True,
        'actual_source_inverse': encode(inverse),
        'canonical_reduction': [
            'The certified original temporal Jacobian is nonzero at the literal source. Its same-source analytic implicit-function branch y=Y(z) persists on an open neighborhood; the primary and scalar Gauss momentum sections are independent of y.',
            'Pull back the original canonical one-form theta_z+p_y.dy to p_y=0,y=Y(z). It is exactly theta_z. The retained six coframe coordinates, scalar61 and gauge36 therefore keep their already generated canonical form; the independent original matter pair is unchanged.',
            'For functions f(z),g(z), both brackets with p_y vanish. The lower-right block of Delta^-1 is zero, so the full Dirac correction vanishes for arbitrary K={F,F}_z: {f,g}_D={f,g}_z.',
            'H_red(z)=H(Y(z),z) has derivative d_z H_red=partial_z H because partial_y H=-F=0. Its canonical flow is the original constrained z-flow. Differentiating F(Y(z),z)=0 gives dot_y=-J^-1 {F,H}_z, precisely the original time-coframe update.'],
        'actual_nonlinear_update': {'Jacobian': encode(current_J), 'forcing': encode(current_force), 'time_rate': encode(current_rate),
            'same_original_J_times_rate_plus_forcing_zero': True},
        'explicit_source_family': {'generated_a': str(a), 'positive_branch': 'b=0, n=sqrt(3*c/a), c=162/625, a>0',
            'reduced_energy': str(reduced), 'source_energy': str(s.simplify(reduced.subs(avar, s.Rational(9, 5)))),
            'nonzero_scalar_momentum_and_independent_matter_fixture': str(actual_a),
            'source_clock_squared': str(source.N**2), 'source_branch_is_chosen_by_original_positive_coframe': True},
        'quantum_consumer_responsibility': 'The formal H(nu) pencil describes the unreduced parameter family. The temporal primary/secondary rows are second class on this source chart: their simultaneous first-class physical-state kernel is not installed. Quantization of the reduced H_red must consume its source branch and noncommuting ordering explicitly.',
        'all_remaining_stabilizer_constraints_eliminated': False,
        'quantum_reduced_Hilbert_evolution_or_spectrum_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_temporal_dirac_reduction.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS original temporal Dirac reduction', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
