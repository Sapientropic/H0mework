#!/usr/bin/env python3
"""Source-time native G/V, with original BF and direct seven-matrix curvature."""
from pathlib import Path
import hashlib
import json
import time
import sympy as s
from source_live_differential_hamiltonian import SourceLiveDifferentialHamiltonian, clean
from source_joint_form_hamiltonian import read_bound
from independent_source_gauge_slice_coordinates import pair
from dynamic import HERE, ROOT, ROOT_ID


def audit_point(raw, configuration):
    base = clean(raw.full.offset + raw.full.embedding*s.Matrix(configuration))
    q = tuple(base[:6, :]); phi = base[6:76, :]; A = base[76:, :].reshape(3, 12)
    n = raw.source_time[0]; original = raw.full.native.joint.gauge.source
    sigma = original.sigma; v = q[0]*q[2]*q[5]
    Q = s.Matrix([[q[0], 0, 0], [q[1], q[2], 0], [q[3], q[4], q[5]]])
    Qi = s.Matrix([[1/q[0], 0, 0], [-q[1]/(q[0]*q[2]), 1/q[2], 0],
        [(q[1]*q[4]-q[2]*q[3])/(q[0]*q[2]*q[5]), -q[4]/(q[2]*q[5]), 1/q[5]]])
    assert clean(Q*Qi-s.eye(3)) == s.zeros(3)
    inverse_spatial = clean(Qi*Qi.T)
    fund = original.fundamental
    gram = s.Matrix(12, 12, lambda a, b: pair(fund[a], fund[b]))
    assert clean(gram-original.gram) == s.zeros(12)
    matrices = [clean(sum((A[i, a]*fund[a] for a in range(12)), s.zeros(7))) for i in range(3)]
    B = [clean(matrices[j]*matrices[k]-matrices[k]*matrices[j]) for j, k in ((1, 2), (2, 0), (0, 1))]
    common = raw.full.native.joint.common.scalar
    U = [clean(sum((A[i, a]*common.rho[a]*phi for a in range(12)), s.zeros(70, 1))) for i in range(3)]
    potential = s.cancel(n*v*((phi-common.vacuum).T*(phi-common.vacuum))[0]
        - n*v*sum(inverse_spatial[i, j]*(U[i].T*U[j])[0] for i in range(3) for j in range(3))/2
        + v*sum(inverse_spatial[i, j]*pair(B[i], B[j]) for i in range(3) for j in range(3))/(2*sigma*n))
    weight = s.diag(-n/v*s.eye(70), s.kronecker_product(sigma*v/n*inverse_spatial, gram.inv(method='DM')))
    actual = raw._four_energies(base, q, A, raw.source_time)
    assert clean(weight-actual['weight']) == s.zeros(106)
    assert s.cancel(potential-actual['potential']) == 0
    assert actual['shift'] == s.zeros(106, 1)
    assert actual['shift_derivative'] == s.zeros(106, 94)
    print('PASS original native106 G/V; direct7x7 magnetic bracket; source-time zero shifts', flush=True)
    return {'configuration100': list(map(str, configuration)), 'potential': str(potential),
        'weight106_complete_return': True, 'original_shift_and_derivative_zero': True}


def generic_coframe(raw):
    q = tuple(s.Symbol('q'+str(j), positive=True) if j in (0, 2, 5) else
        s.Symbol('q'+str(j), real=True) for j in range(6)); n = s.Symbol('n', positive=True)
    Q = s.Matrix([[q[0], 0, 0], [q[1], q[2], 0], [q[3], q[4], q[5]]])
    e = s.diag(n, Q); v = q[0]*q[2]*q[5]
    original = raw.full.native.joint.gauge.source
    kernel = clean(original.at(original.kernel_numerator, e)/(n*v))
    R = clean(Q.inv(method='DM')*Q.inv(method='DM').T)
    expected = s.diag(n/(original.sigma*v)*Q.T*Q, -v/(original.sigma*n)*R)
    assert clean(kernel-expected) == s.zeros(6)
    # A nonzero time-space column is an explicit override, not this specialization.
    shifted = e.copy(); shifted[1, 0] = s.Rational(1, 11)
    mixed = clean(original.at(original.kernel_numerator, shifted)/(n*v))[:3, 3:]
    assert mixed != s.zeros(3)
    print('PASS symbolic6-coframe BF kernel and nonzero-time-shift counterexample', flush=True)
    return {'all6_coframe_symbols': True, 'cyclic_magnetic_order': ['23', '31', '12'],
        'nonzero_time_shift_is_not_zero_shift_specialization': True}


def main(raw=None):
    began = time.monotonic(); raw = SourceLiveDifferentialHamiltonian() if raw is None else raw
    generic = generic_coframe(raw)
    off = read_bound('source_live_differential_hamiltonian')['off_source']
    points = [audit_point(raw, raw.source_configuration),
        audit_point(raw, tuple(map(s.sympify, off['configuration100'])))]
    deps = ('source_native_second_form', 'source_live_differential_hamiltonian',
        'source_common_temporal_form', 'source_gauss_history_domain')
    for name in deps: read_bound(name)
    paths = [Path(__file__)] + [HERE/(name+'.json') for name in deps]
    paths += [HERE/name for name in ('source_live_differential_hamiltonian.py',
        'independent_source_gauge_slice_coordinates.py', 'GaussNativeEnergy.lean',
        'GaussNativePotential.lean', 'GaussNativeForm.lean')]
    report = {'root': ROOT_ID, 'scope': 'ORIGINAL_SOURCE_TIME_NATIVE_QUADRATIC_FORM',
        'source_sha256': raw.full.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'generic_coframe': generic, 'points': points,
        'algorithm': 'Native G is returned to the original BF electric inverse and Lorentzian scalar metric; magnetic potential is independently contracted from original7x7 brackets and native trace pairing. Both nonzero source configurations use the original time column after the full action variation.',
        'controller': 'Original source/root/current and whole ledger unchanged; subordinate producer.',
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_native_energy.json').write_text(json.dumps(report, separators=(',', ':'))+'\n')
    print('PASS original native energy and quadratic form', report['seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
