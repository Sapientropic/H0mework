#!/usr/bin/env python3
"""Independent density, implicit-section and divergence-form time-family audit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_form_hamiltonian import (
    RawGaussSection, RawLiveCoefficients, HERE, ROOT, ROOT_ID, bindings, rational, eq,
    decode, encode, terms, current, state_encode, decoded_state, zero, state_equal,
    raw_gauge_coefficients, whole_action)
from independent_source_scalar_temporal_form import at, reclock_scalar
from independent_source_scalar_form_hamiltonian import raw_coefficients
from independent_source_quantum_ordered_temporal import raw_coframe_family
from independent_source_common_hamiltonian import raw_matter, original_inventory
from independent_source_quantum_antiunitary import RawAntiunitary
from independent_source_full_quantum_adjoint import sparse, dual_pair
from independent_source_gauge_legendre import ETA


def main():
    started = time.monotonic(); path = HERE/'source_common_temporal_form.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ('independent_source_scalar_temporal_form', 'independent_source_temporal_coframe_pairing',
        'independent_source_temporal_gauss_relations', 'independent_source_quantum_antiunitary')
    for name in paid:
        receipt = json.loads((HERE/(name+'.json')).read_text()); count += bindings(receipt)
        assert receipt['verdict'].startswith('CERTIFIED_') and receipt['root'] == ROOT_ID
    section, raw = RawGaussSection(), RawLiveCoefficients(); inventory = original_inventory()
    assert section.native.hashes == candidate['source_sha256']
    C = RawAntiunitary(inventory['gamma'][0])
    ys = (s.Symbol('quantum_n', positive=True), *s.symbols('quantum_b1:4', real=True))
    e, cf = raw_coframe_family(raw, ys)
    reflection = dict(zip(ys, (ys[0], *[-b for b in ys[1:]])))
    fields = s.Matrix(3, 12, s.symbols('reflection_A0:36', real=True))
    gauge = raw_gauge_coefficients(e, fields, section.native)
    eq(gauge['weight'].H, gauge['weight']); eq(gauge['weight'].conjugate(), gauge['weight'])
    eq(gauge['weight'].xreplace(reflection), gauge['weight'])
    eq(gauge['shift'].conjugate(), gauge['shift'])
    eq(gauge['shift'].xreplace(reflection), -gauge['shift'])
    zero(gauge['potential'].xreplace(reflection)-gauge['potential'])
    zero(s.im(gauge['potential'])); zero(s.trace(gauge['weight']*gauge['ds']))
    metric = rational(e.det()*(e.T*ETA*e).inv())
    zero(metric[0, 0].xreplace(reflection)-metric[0, 0])
    eq(metric[0, 1:].xreplace(reflection), -metric[0, 1:])
    eq(metric[1:, 1:].xreplace(reflection), metric[1:, 1:])
    inv = rational(e.inv()); gamma = inventory['gamma']
    principal = [rational(s.I*e.det()*sum((inv[mu, a]*gamma[a] for a in range(4)), s.zeros(4))) for mu in range(4)]
    Ei, free = principal[0].gauss_jordan_solve(s.eye(4)); assert free.rows == 0
    for i in range(1, 4):
        S = rational(-s.I*Ei*principal[i]); eq(S.H, -S)
        eq(-gamma[0]*S*gamma[0].H, S.xreplace(reflection))
        eq(S, decode(candidate['generic_laws']['all3_matter_spin_anti_Hermitian_at_all4time'][i-1],
                     {str(q): q for q in (*raw.q, *ys)}))
    for Q in section.native.Qb+section.native.Qs: eq(C.U*Q.conjugate()*C.U.H, -Q)
    print('PASS independent full four-time gauge Hodge, Dirac matter and scalar reflection coefficients', flush=True)

    saved = candidate['actual_consumer']; q = tuple(map(s.sympify, saved['q']))
    clock = tuple(map(s.sympify, saved['time'])); opposite = tuple(map(s.sympify, saved['reflected_time']))
    assert opposite == (clock[0], *[-b for b in clock[1:]]) and all(clock[1:])
    x, A = decode(saved['x61']), decode(saved['A36']); point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    word = tuple(saved['input_CAR']); gradient, Hessian = decode(saved['gradient100']), decode(saved['Hessian100'])
    _, jets = section.extension_jet(point, {word: 1}, {word: gradient}, {word: Hessian})
    Gauss = section.Gauss_checks(point, jets); Cjets = C.jet(jets)
    section.Gauss_checks(point, Cjets)
    ee = at(e, {**dict(zip(raw.q, q)), **dict(zip(ys, clock))})
    initial_scalar = raw_coefficients(section.native, ee, x, A)
    def actual_at(clock_value, jet):
        sub = {**dict(zip(raw.q, q)), **dict(zip(ys, clock_value))}
        coframe = {key: at(value, sub) for key, value in cf.items()}; ee = at(e, sub)
        scalar = reclock_scalar(section.native, initial_scalar, ee, A)
        gauge = raw_gauge_coefficients(ee, A, section.native)
        connection = s.zeros(4, 12); connection[1:, :] = A
        matter = raw_matter(ee, scalar['phi'], connection)
        M = dual_pair(rational(-s.I*matter['E_inverse']*matter['lower']))
        rawY = sum(((scalar['phi'][j]+s.I*scalar['phi'][j+35])*inventory['scalar'][j]
                    for j in range(35)), s.zeros(252))
        Y = dual_pair(sparse(s.kronecker_product(clock_value[0]*gamma[0], s.eye(63)))*sparse(rawY))
        M0 = sparse(M-Y); eq(M0.H, M0)
        pieces, H0 = whole_action(dict(coframe=coframe, scalar=scalar, gauge=gauge, matter=M0), jet)
        pieces['matter_noY'] = pieces.pop('matter_without_Lorentz')
        values = {w: row[0] for w, row in jet.items() if row[0]}
        return pieces, H0, terms([(1, H0), (1, current(Y, values))]), terms([(1, H0), (1, current(Y.H, values))])
    pieces, H0, H, Hsharp = actual_at(clock, jets)
    for key, image in pieces.items():
        assert image; state_equal(image, decoded_state(saved['positive_components'][key]))
    for name, image in [('positive_H0', H0), ('positive_H', H), ('positive_Hsharp', Hsharp)]:
        state_equal(image, decoded_state(saved[name]))
    reflected, RH0, RH, _ = actual_at(opposite, Cjets)
    for key, image in reflected.items():
        assert image; state_equal(image, C.state(pieces[key]))
        state_equal(image, decoded_state(saved['reflected_components'][key]))
    state_equal(RH0, C.state(H0)); state_equal(RH0, decoded_state(saved['reflected_H0_C']))
    full_defect = terms([(1, RH), (-1, C.state(H))]); assert full_defect
    state_equal(full_defect, decoded_state(saved['original_Y_reflection_defect']))
    _, sameH0, _, _ = actual_at(clock, Cjets)
    same_defect = terms([(1, sameH0), (-1, C.state(H0))]); assert same_defect
    state_equal(same_defect, decoded_state(saved['unreflected_H0_defect']))
    print('PASS independent implicit Gauss jets, complete four-energy actions and both nonzero reflection controls', flush=True)
    paths = [Path(__file__), path, HERE/'source_common_temporal_form.py',
        HERE/'independent_source_joint_form_hamiltonian.py', HERE/'independent_source_scalar_temporal_form.py',
        HERE/'independent_source_quantum_ordered_temporal.py', HERE/'independent_source_common_hamiltonian.py',
        HERE/'independent_source_quantum_antiunitary.py']+[HERE/(name+'.json') for name in paid]
    out = {'verdict': 'CERTIFIED_FULL504_FOUR_TIME_FORM_AND_OPPOSITE_SHIFT_ANTIUNITARY',
        'root': ROOT_ID, 'source_sha256': section.native.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'Original epsilon/Hodge and Dirac principals; raw scalar97 divergence form; native implicit Gauss second jets; exterior determinant antiunitary; each full four-energy image recomputed.',
        'generic_original_four_time_formal_adjoint_coefficients': True,
        'opposite_shift_laws': 'Gauge W and scalar h00/hij are even, original gauge/scalar shifts odd; full Dirac spin factors obey the reflected dual-pair identity. Coframe n-only and common positive number weight are consumed from the independent whole-coefficient proof.',
        'actual_consumer': {'input_CAR': list(word), 'time': list(map(str, clock)), 'reflected_time': list(map(str, opposite)),
            'Gauss': Gauss, 'positive_components': {k: state_encode(v) for k, v in pieces.items()},
            'positive_H0': state_encode(H0), 'positive_H': state_encode(H), 'positive_Hsharp': state_encode(Hsharp),
            'reflected_components': {k: state_encode(v) for k, v in reflected.items()}, 'reflected_H0_C': state_encode(RH0),
            'unreflected_H0_defect': state_encode(same_defect), 'original_Y_reflection_defect': state_encode(full_defect)},
        'pairing_and_constraint_scope': 'One real positive pairing and compact smooth domain for all admitted time parameters. The original smooth coefficient derivative -partial_y H has the derivative formal adjoint. The time parameters remain parameters, not solved noncommuting operators.',
        'original_Y_preserved_and_generic_fixed_shift_symmetry_not_claimed': True,
        'temporal_secondary_operator_solution_or_spectrum_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_common_temporal_form.json').write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print('PASS independent source common temporal form', out['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
