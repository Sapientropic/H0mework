#!/usr/bin/env python3
"""Exact five-weight dilation pencil of the original common local quantum form.

Dilation acts on the coframe configuration, not on spacetime momentum. All
four energies, both Dirac branches and the original non-Hermitian Y remain.
"""
from __future__ import annotations
import hashlib
import json
import time
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID, decode
from source_common_temporal_form import SourceCommonTemporalForm
from source_joint_form_hamiltonian import read_bound
from source_scalar_form_hamiltonian import relocate_section
from source_coframe_legendre import rational
from source_lorentz_contact import equal, encode, ETA
from source_gauss_quantum_current import weighted_sum, encode_state

POWERS = (-3, -1, 0, 1, 3)


def generic_weights(model):
    family = model.family
    q = model.native.joint.coframe.q
    scale = s.Symbol('coframe_dilation', positive=True)
    substitution = dict(zip(q, (scale*x for x in q)))
    records = []
    def verify(name, matrix, power, derivative_order=0):
        matrix = s.Matrix(matrix)
        scaled = matrix.subs(substitution, simultaneous=True)
        equal(rational(scaled-scale**power*matrix), s.zeros(*matrix.shape))
        records.append({'coefficient': name, 'degree': power,
            'coframe_derivative_order': derivative_order,
            'operator_degree': power-derivative_order, 'nonzero_entries': len(matrix.todok())})
    cf = family.cf
    verify('coframe_principal', cf['K'], -1, 2)
    verify('coframe_live_drift', cf['drift'], -2, 1)
    for j, M in enumerate(cf['M']): verify('coframe_mixed_'+str(j), M, -2, 1)
    verify('coframe_onebody', cf['one_body'], -3)
    verify('coframe_live_correction', cf['correction'], -3)
    flat = s.Matrix.hstack(*(J.reshape(64, 1) for J in cf['J']))
    verify('coframe_ordered_two_current', rational(flat*cf['W']*flat.T), -3)
    verify('coframe_volume_potential', [[cf['constant']]], 3)
    e = family.e
    inv = rational(e.inv()); h = rational(e.det()*inv*ETA*inv.T)
    verify('scalar_nested_momentum_weight', [[1/(2*h[0, 0])]], -3)
    verify('scalar_ordered_shift_weights', rational(h[0, 1:]/h[0, 0]), -1)
    verify('scalar_spatial_weights', rational(h[1:, 0]*h[0, 1:]/h[0, 0]-h[1:, 1:]), 1)
    verify('scalar_vacuum_potential_weight', [[e.det()]], 3)
    raw = model.native.joint.gauge.source.constitutive(e)
    for key, weight in (('electric', -1), ('electric_inverse', 1), ('mixed', 0), ('magnetic', 1)):
        verify('original_BF_'+key, raw[key], weight)
    ports = model.native.joint.coframe.model.lorentz.raw_matter_ports(e)
    for j in range(1, 4):
        verify('matter_spatial_'+str(j), rational(ports['E'].inv()*ports['oriented_principals'][j]), -1)
    verify('original_Yukawa_weight', rational(-s.I*e.det()*ports['E'].inv()), 0)
    return scale, records


def laurent_state(state, scale):
    result = {p: {} for p in POWERS}
    for word, coefficient in state.items():
        polynomial = s.Poly(s.cancel(scale**3*coefficient), scale)
        assert set(k[0]-3 for k, _ in polynomial.terms() if _).issubset(POWERS)
        for (k,), value in polynomial.terms():
            if value: result[k-3][word] = s.factor(value)
    reconstructed = weighted_sum((scale**p, state) for p, state in result.items())
    assert not weighted_sum([(1, reconstructed), (-1, state)])
    return result


def actual_consumer(model, scale):
    saved = read_bound('source_common_temporal_form')['actual_consumer']
    q = tuple(map(s.sympify, saved['q'])); x, A = decode(saved['x61']), decode(saved['A36'])
    time_column = tuple(map(s.sympify, saved['time']))
    word = tuple(saved['input_CAR'])
    relocate_section(model.section, s.Matrix(q).col_join(x).col_join(A.reshape(36, 1)))
    base = model.section.extend_jet({word: 1}, {word: decode(saved['gradient100'])},
                                   {word: decode(saved['Hessian100'])})
    derivative = s.diag(*([1/scale]*6+[1]*97))
    jet = {w: {'value': row['value'], 'gradient': derivative*row['gradient'],
               'Hessian': derivative*row['Hessian']*derivative} for w, row in base.items()}
    gauss = model.section.verify_Gauss_jet(jet)
    data = model.coefficients(time_column, tuple(scale*x for x in q), x, A)
    action = model.action(data, jet)
    # The original coframe jet readout serializes its exact coefficients.
    # Restore this positive parameter after that string boundary.
    def restore(state):
        return {w: s.factor(c.xreplace({z: scale for z in c.free_symbols if str(z) == str(scale)}))
                for w, c in state.items()}
    action['pieces'] = {name: restore(state) for name, state in action['pieces'].items()}
    for name in ('H', 'H0', 'Hsharp', 'Y'): action[name] = restore(action[name])
    pieces = {**action['pieces'], 'original_Y': action['Y']}
    allowed = {'coframe': {-3, 3}, 'scalar_form': {-3, -1, 1, 3},
               'gauge': {1}, 'matter_noY': {-1}, 'original_Y': {0}}
    weights = {}
    for name, state in pieces.items():
        weights[name] = laurent_state(state, scale)
        assert all(not values or power in allowed[name] for power, values in weights[name].items()), (
            name, [power for power, values in weights[name].items() if values])
    total = {p: weighted_sum((1, weights[name][p]) for name in weights) for p in POWERS}
    assert all(total.values())
    assert not weighted_sum([(1, action['H']),
                            *[(-scale**p, total[p]) for p in POWERS]])
    assert not weighted_sum([(1, {w: s.factor(v.subs(scale, 1)) for w, v in action['H'].items()}),
                            (-1, {tuple(w): s.sympify(v) for w, v in saved['positive_H']})])
    # Differentiating a proved operator family retains every source coefficient.
    derivative_image = {w: s.diff(c, scale).subs(scale, 1) for w, c in action['H'].items()}
    virial = weighted_sum((p, total[p]) for p in POWERS)
    assert not weighted_sum([(1, derivative_image), (-1, virial)])
    assert virial
    print('PASS complete original Gauss/CAR action has all five nonzero dilation weights', flush=True)
    return {'time_column': list(map(str, time_column)), 'q': list(map(str, q)),
        'x61': encode(x), 'A36': encode(A), 'input_CAR': list(word), 'Gauss': gauss,
        'original_component_weights': {name: {str(p): encode_state(st) for p, st in row.items()}
                                      for name, row in weights.items()},
        'full_H_weights': {str(p): encode_state(state) for p, state in total.items()},
        'original_Y': encode_state(action['Y']), 'exact_dilation_derivative': encode_state(virial),
        'all_original_components_and_all_five_weights_nonzero': True,
        'source_scale_one_readback': True}


def main():
    started = time.monotonic()
    deps = ('source_common_temporal_form', 'independent_source_common_temporal_form',
            'source_temporal_coframe_pairing', 'independent_source_temporal_coframe_pairing')
    for name in deps: read_bound(name)
    model = SourceCommonTemporalForm()
    scale, generic = generic_weights(model)
    print('PASS original all-q/all-time coframe, scalar, BF and Dirac dilation identities', flush=True)
    actual = actual_consumer(model, scale)
    m = s.Symbol('occupation_number', integer=True, nonnegative=True)
    alpha = 3*m/2+6
    assert s.expand(2*alpha-6-3*(m+2)) == 0
    assert s.expand(alpha-s.Rational(3, 2)*(m+s.Rational(7, 2))-s.Rational(3, 4)) == 0
    files = [HERE/(name+'.json') for name in deps]+[HERE/name for name in (
        'source_common_volume_pencil.py', 'source_common_temporal_form.py', 'source_scalar_temporal_form.py',
        'source_quantum_ordered_temporal.py', 'source_gauge_legendre.py', 'source_gauge_quantum_energy.py',
        'source_scalar_shift_quantum.py', 'source_scalar_form_hamiltonian.py', 'source_full_quantum_adjoint.py')]
    out = {'root': ROOT_ID, 'scope': 'ORIGINAL_COMMON_LOCAL_QUANTUM_FIVE_WEIGHT_UNITARY_COFRAME_DILATION_PENCIL',
        'source_sha256': model.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'generic_source_coefficient_laws': generic,
        'source_Hilbert_unitary': 'U_lambda f(q,x,A)=lambda^(3m/2+6) f(lambda*q,x,A). The actual measure dq6*v^(m+2)*rho3(x,A) and the open source chart are preserved by change of variables, for every lambda>0 and every original occupation.',
        'volume_half_density_representation': 'U_lambda f(r,theta,x,A)=lambda^(3/4) f(lambda^(3/2)*r,theta,x,A). Thus D=-i*(3/2*r*partial_r+3/4) on the actual compact core.',
        'exact_family': 'U_lambda H(n,b) U_lambda^-1=lambda^-3 H_-3+lambda^-1 H_-1+H_0+lambda H_1+lambda^3 H_3.',
        'weights': {'-3': 'Complete coframe kinetic/CAR form and scalar Pi-dagger Pi, including every live inverse and density derivative.',
            '-1': 'Original ordered scalar shift and full non-Y Dirac spatial operator.',
            '0': 'Original non-Hermitian full504 Yukawa operator; no adjoint added.',
            '1': 'Entire original BF gauge operator, electric/magnetic/mixed ordering included, and scalar spatial potential after its exact shift-square combination.',
            '3': 'Original coframe volume and scalar vacuum potential.'},
        'actual_consumer': actual,
        'exact_weak_virial': 'i[D,H]=sum_p p*H_p on the common smooth compact domain; no expectation or spectral eigenstate is supplied.',
        'time_constraints': 'The same unitary is independent of all four time parameters, so it preserves the exact five weights of each original F_a=-partial_y_a H.',
        'direct_consumer': 'The full grade-zero clock and spectral operator now have a finite exact coframe-volume pencil, rather than a formal expansion in this configuration coordinate.',
        'spacetime_dilation_or_full_spatial_quantum_completion_claimed': False,
        'clock_solution_spectral_measure_or_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_common_volume_pencil.json').write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print('PASS exact source common volume pencil', out['elapsed_seconds'], 'seconds', flush=True)

if __name__ == '__main__': main()
