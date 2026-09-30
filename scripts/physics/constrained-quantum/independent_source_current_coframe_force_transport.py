#!/usr/bin/env python3
"""Current coframe-force transport checked through independent raw energies.

The positive density is differentiated as a literal product, the native
inverse comes from implicit raw constraints, and every current-force column
is obtained from the independent four-energy action before differentiation.
"""
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import time

import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from source_current_coframe_force_transport import SourceCurrentCoframeForceTransport
from independent_source_joint_form_hamiltonian import (
    RawGaussSection, RawLiveCoefficients, build_operators, whole_action,
)
from independent_source_temporal_lorentz_balance import inverse_density
from independent_source_lorentz_quantum_section import clean, total, equal

RAW = None
COFRAME = None
VALUES = None
GRADIENTS = None
HESSIANS = None
EXPECTED = None


def same(left, right):
    difference = total((1, left), (-1, right))
    assert not difference, list(difference.items())[:3]


def check_column(axis):
    variable = s.Symbol('audit_source_q_'+str(axis), positive=True) if axis in (0, 2, 5) else s.Symbol('audit_source_q_'+str(axis), real=True)
    point = RAW.free_reader*RAW.source
    source_value = point[axis]
    point[axis] = variable
    germ = inverse_density(point, RAW.free, VALUES, GRADIENTS, HESSIANS)
    _, jets = RAW.extension_jet(RAW.source, *germ)
    q = tuple(point[:6, :])
    x, A = RAW.source[6:67, :], RAW.source[67:, :].reshape(3, 12)
    data = build_operators(RAW, COFRAME, q, x, A)
    _, family = whole_action(data, jets)
    force = clean({w: -s.diff(c, variable).subs(variable, source_value)
                   for w, c in family.items()})
    row = EXPECTED[axis]
    same(force, row['current_q_force'])
    same(force, row['transported_current_q_force'])
    without_chain = total((1, row['fixed_Pi_force']), (1, row['source_ordering_gap_derivative']))
    defect = total((1, without_chain), (-1, force))
    same(defect, row['inverse_jet_and_half_density_chain'])
    print('PASS independent full current coframe-force column', axis, len(force), flush=True)
    return {'axis': axis, 'output_words': len(force),
            'output_particle_numbers': sorted({len(w) for w in force}),
            'without_inverse_jet_pairing_chain_defect_words': len(defect)}


def main():
    began = time.monotonic()
    path = HERE/'source_current_coframe_force_transport.json'
    receipt = json.loads(path.read_text())
    assert receipt['root'] == ROOT_ID
    bindings = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in receipt.get(key, {}).items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            bindings += 1
    model = SourceCurrentCoframeForceTransport()
    global RAW, COFRAME, VALUES, GRADIENTS, HESSIANS, EXPECTED
    RAW, COFRAME = RawGaussSection(), RawLiveCoefficients()
    equal(RAW.free_reader*RAW.source, model.current.point)
    for matrix in RAW.T:
        equal(matrix[:, :6], s.zeros(103, 6))
        equal(matrix[:6, :], s.zeros(6, 103))
    VALUES = {(): s.Rational(3, 11), (17, 271): s.Rational(5, 13), (83,): s.S.Zero}
    GRADIENTS, HESSIANS = {}, {}
    for k, word in enumerate(VALUES):
        GRADIENTS[word] = s.Matrix([s.Rational((j+2*k) % 7-3, 59)+
            s.I*s.Rational((3*j+k) % 5-2, 61) for j in range(100)])
        u = s.Matrix([s.Rational((j+3*k) % 6-2, 67) for j in range(100)])
        HESSIANS[word] = u*u.T-s.eye(100)/71
    generated = model.generate(VALUES, GRADIENTS, HESSIANS)
    EXPECTED = generated['q_forces']
    assert {len(w) for row in EXPECTED for w in row['current_q_force']} == {0, 1, 2}
    with ProcessPoolExecutor(max_workers=4, mp_context=mp.get_context('fork')) as pool:
        columns = list(pool.map(check_column, range(6)))
    assert any(row['without_inverse_jet_pairing_chain_defect_words'] for row in columns)
    zero = model.generate({}, {}, {})
    assert not zero['source122_jet']
    for row in zero['q_forces']:
        for key in ('fixed_Pi_force', 'inverse_jet_and_half_density_chain',
                    'source_ordering_gap_derivative', 'current_q_force', 'transported_current_q_force'):
            assert not row[key], (row['q_axis'], key)
    files = [Path(__file__), HERE/'source_current_coframe_force_transport.py', path,
        HERE/'independent_source_joint_form_hamiltonian.py',
        HERE/'independent_source_scalar_form_hamiltonian.py',
        HERE/'independent_source_temporal_lorentz_balance.py']
    result = {'root': ROOT_ID,
        'scope': 'INDEPENDENT_CURRENT_ALL6_COFORCE_TRANSPORT_AND_ZERO_MIXED_GERM_CONSUMERS',
        'source_sha256': receipt['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'candidate_source_binding_checks': bindings,
        'fresh_germ': 'vacuum + cross-internal Number2 + zero-value Number1 with nonzero derivatives',
        'native_implicit_inverse_independent_of_coframe': True,
        'literal_original_positive_density_differentiated': True,
        'all_six_independent_current_force_columns': columns,
        'empty_germ_all_six_transports_zero': True,
        'caller_supplied_force_or_output_H_jet': False,
        'seconds': round(time.monotonic()-began, 3)}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent current coframe-force transport', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
