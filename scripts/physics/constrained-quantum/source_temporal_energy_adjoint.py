#!/usr/bin/env python3
"""Actual third ordered time-energy coefficient on a source Gauss germ.

This consumes the specified coefficient-left temporal recursion, with the
new scalar form atoms and their actual live-coframe Gauss relations. It
neither changes that ordering nor identifies a formal series with its sum.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_scalar_temporal_form import SourceScalarTemporalForm
from source_scalar_form_hamiltonian import relocate_section
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode
from source_quantum_ordered_temporal import OrderedTemporalCoefficients, DOMAIN, add, scale
from source_quantum_temporal_symbol import N


def bound(name):
    data = json.loads((HERE/(name+'.json')).read_text())
    assert data['root'] == ROOT_ID
    for key in ('source_sha256', 'input_sha256'):
        for path, digest in data[key].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    return data


def reverse(polynomial):
    return {tuple(reversed(word)): value for word, value in polynomial.items()}


def energy_difference():
    ordered = OrderedTemporalCoefficients()
    # The full original Yukawa annihilates the vacuum, as do all native
    # currents. Every remaining atom preserves it. This is a restriction of
    # the original CAR504 family, with no replacement or added adjoint force.
    ordered.atoms[0] = {(0,): DOMAIN.one}
    _, energy, stages = ordered.generate(3)
    defects = [add(p, scale(-1, reverse(p))) for p in energy]
    assert [len(p) for p in defects] == [0, 0, 0, 168]
    assert all(s.im(DOMAIN.to_sympy(c)) == 0 for p in energy for c in p.values())
    mixed = {word: DOMAIN.to_sympy(c) for word, c in defects[3].items() if 0 in word}
    assert len(mixed) == 30
    for word in mixed:
        assert word.count(0) == 1
        letters = [v for v in word if v != 0]
        assert all(1 <= v <= 3 or 10 <= v <= 12 for v in letters)
        assert (letters[0]-1) % 9 == (letters[1]-1) % 9
    return mixed, stages


def mixed_symbol(q, K, L, mixed):
    """Exact coefficient of one q derivative and two gauge derivatives.

    c is the principal symbol of the original coordinate cross vector. Its
    gauge variables are independent of q. Differentiating these coefficients
    in a gauge direction instead produces q-q-gauge or lower terms; the
    displayed cubic germ kills all of those terms.
    """
    c = s.Matrix(s.symbols('coordinate_cross0:3'))
    a, d = rational(L.inv().T*c), L*c
    atoms = {**{j+1: a[j] for j in range(3)}, **{j+10: d[j] for j in range(3)}}
    principal4 = s.S.Zero
    differentiated = s.zeros(6, 1)
    for word, coefficient in mixed.items():
        left, right = [j for j in word if j]
        x, y = atoms[left], atoms[right]
        principal4 += coefficient*x*y
        if word[0] == 0:
            differentiated += coefficient*s.Matrix([s.diff(x*y, v) for v in q])
        elif word[1] == 0:
            differentiated += coefficient*x*s.Matrix([s.diff(y, v) for v in q])
    assert s.cancel(principal4) == 0
    # atom0 has coframe component Hcf/N; the original scalar, matter and
    # constant subtraction in atom0 have no q derivatives.
    answer = rational(-2*K*differentiated/N)
    assert answer.todok()
    return c, atoms, answer


def original_cross(native, A):
    connection = s.zeros(4, 12); connection[1:, :] = A
    B, _ = native.gauge.spatial_data(connection, s.zeros(3, 48))
    p = s.Matrix(s.symbols('derivative_A0:36'))
    C = s.Matrix(3, 3, lambda i, j: -s.I*(B[j, :]*p[12*i:12*(i+1), :])[0])
    cross = s.Matrix([C[2, 1]-C[1, 2], C[0, 2]-C[2, 0], C[1, 0]-C[0, 1]])
    return clean(cross.jacobian(p)), B


def nested_germ(cf, mixed, atoms, c, cross_value, direction, source_q):
    """Direct original coframe action in every one of the thirty words.

    This is the exact jet restriction, not a coefficient-frozen Hamiltonian:
    all six q coefficients and their derivatives are kept. Gauge coefficient
    derivatives multiply the vanished first gauge jet of the quadratic germ.
    """
    q = cf.q; z = s.Symbol('test_slice_coordinate', real=True)
    at = {**dict(zip(q, source_q)), z: 0}
    sub = dict(zip(c, cross_value))
    U = {a: s.cancel(value.subs(sub)) for a, value in atoms.items()}
    f = (q[direction]-source_q[direction])*z*z/2

    def H(value):
        result = -sum(coefficient*s.diff(value, q[r], q[t])
                      for (r, t), coefficient in cf.K.todok().items())
        result -= s.I*sum(cf.drift[r]*s.diff(value, q[r]) for r in range(6))
        result += 3*cf.det*value
        return s.cancel(result/N)

    @lru_cache(maxsize=None)
    def apply(word):
        if not word: return f
        inner = apply(word[1:])
        return H(inner) if word[0] == 0 else s.cancel(U[word[0]]*s.diff(inner, z))

    values = {word: s.cancel(apply(word).subs(at)) for word in mixed}
    answer = s.cancel(sum(mixed[word]*value for word, value in values.items()))
    return answer, values


def main():
    started = time.monotonic()
    bound('source_scalar_temporal_form'); bound('source_temporal_coframe_pairing')
    bound('source_temporal_gauss_relations')
    m = SourceScalarTemporalForm(); cf = m.native.joint.coframe
    mixed, stages = energy_difference()
    q, L = cf.q, m.e[1:, 1:]
    c, atoms, symbol = mixed_symbol(q, cf.K, L, mixed)
    source_q = tuple(m.section.b0[:6, 0]); at_q = dict(zip(q, source_q))
    source_symbol = rational(symbol.subs(at_q))
    print('PASS actual temporal atom relation and exact all-six-q mixed third-order coefficient', flush=True)

    # At the literal background the cross vector is vertical: that vanishing
    # readout is not promoted to an operator identity. Use an allowed point of
    # the same open chart with the same gauge pivots and source q, x=0.
    baseline_cross, _ = original_cross(m.native, m.section.A0)
    equal(clean(baseline_cross*m.section.z[:, 67:].T), s.zeros(3, 100))
    A = m.section.A0.copy(); A[0, 2] += s.Rational(1, 31); A[1, 7] += s.Rational(1, 19)
    point = m.section.b0.copy(); point[67:, :] = A.reshape(36, 1)
    relocate_section(m.section, point)
    cross, B = original_cross(m.native, A)
    slice_cross = clean(cross*m.section.z[:, 67:].T)
    # This actual coordinate of the original chart has one nonzero cross
    # component, so its cubic germ isolates the q-dependent mechanism.
    coordinate = 80
    assert sum(v != 0 for v in slice_cross[:, coordinate]) == 1
    lam = m.section.z[coordinate, :].T
    equal(lam[:67, :], s.zeros(67, 1)); equal(m.section.V.T*lam, s.zeros(3, 1))
    cvalue = clean(cross*lam[67:, :])
    actual = rational(source_symbol.subs(dict(zip(c, cvalue))))
    direction = next(j for j, value in enumerate(actual) if value != 0)
    expected = actual[direction]
    # The true vacuum Gauss germ is q_delta*z_delta^2/2 on the original100
    # slice, extended by the actual residual3 group, with a compact cutoff
    # equal1 nearby. Its lower two jets vanish. At third order the inverse
    # chart curvature drops out and only its actual first derivative remains.
    dq = s.eye(103)[:, direction]
    for generator in range(3):
        equal(m.section.V[:, generator].T*dq, s.zeros(1, 1))
        equal(m.section.V[:, generator].T*lam, s.zeros(1, 1))
    for R in m.section.R:
        assert R.shape == (504, 504)
    nested, words = nested_germ(cf, mixed, atoms, c, cvalue, direction, source_q)
    assert s.cancel(nested-expected) == 0 and expected != 0
    assert coordinate == 80 and direction == 0
    assert s.cancel(expected-6623*s.sqrt(30)/145673515584) == 0
    print('PASS all30 original nested words on an actual vacuum Gauss cubic germ:', expected, flush=True)

    # An explicit q-constant treatment would discard exactly the mechanism
    # used by this consumer; preserve that changed-operation contrast.
    constant_atoms = {a: s.cancel(value.subs(at_q)) for a, value in atoms.items()}
    frozen, _ = nested_germ(cf, mixed, constant_atoms, c, cvalue, direction, source_q)
    assert frozen == 0
    print('PASS same germ with incorrectly frozen coframe coefficients gives0, whereas original gives nonzero', flush=True)

    paths = [HERE/name for name in (
        'source_temporal_energy_adjoint.py', 'source_quantum_ordered_temporal.py',
        'source_quantum_ordered_temporal.json', 'source_scalar_temporal_form.py',
        'source_scalar_temporal_form.json', 'source_temporal_coframe_pairing.py',
        'source_temporal_coframe_pairing.json', 'source_temporal_gauss_relations.py',
        'source_temporal_gauss_relations.json', 'source_coframe_live_ordering.py',
        'source_quantum_gauss_section.py', 'source_scalar_form_hamiltonian.py')]
    result = {'root': ROOT_ID,
        'source_sha256': m.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'ACTUAL_THIRD_COEFFICIENT_OF_SPECIFIED_ORDERED_TEMPORAL_ENERGY_ON_ORIGINAL_VACUUM_GAUSS_DOMAIN',
        'formal_calculation': {'recursion': stages, 'free_difference_word_count': 168,
            'actual_coframe_containing_terms': [{'word': list(w), 'coefficient': str(v)} for w, v in mixed.items()],
            'every_coframe_word_has_exactly_one_atom0_and_two_corresponding_shift_atoms': True},
        'source_operator_identity': 'On actual residual3 sections, a=L^-T c=Gd, d=Lc, G=(L L^T)^-1. All coefficients stay on the left and all their q derivatives are retained.',
        'vacuum_restriction': 'Every native current and the original Y annihilate the vacuum; all14 actual atoms preserve that vacuum domain. Atom0 coframe part is Hcf/N_source. No Y-adjoint is inserted and no full-theory self-adjointness is inferred.',
        'adjoint_input': 'The form-native vacuum atoms are individually formally symmetric for rho3*v^2, with the same pairing for all four time parameters; finite-word adjoints therefore reverse actual differential compositions.',
        'generic_mixed_symbol': {'coordinate_cross_covector': list(map(str, c)),
            'source_spatial_coframe': encode(L), 'six_q_coefficient': encode(symbol),
            'source_q_coefficient': encode(source_symbol),
            'order4_q_q_A_A_and_order3_from_coframe_first_order_cancel_exactly': True,
            'all_terms_without_atom0_have_no_q_derivatives': True},
        'actual_consumer': {'q': list(map(str, source_q)), 'base103': encode(point), 'gauge36': encode(A),
            'native_B': encode(B), 'slice_coordinate': coordinate, 'q_direction': direction,
            'actual_gauge_covector103': encode(lam), 'coordinate_cross_value': encode(cvalue),
            'source_A_cross_vanishes_on_actual_slice': True,
            'original_residual_Gauss_horizontal_covectors_checked': True,
            'input': 'Vacuum multiplied by (q0-1)*(z80-z80_base)^2/2 and a smooth compact cutoff equal1 nearby, then extended through the original residual3 group chart.',
            'vanishing_lower_jets': 'value, all103 first and all103x103 second derivatives vanish. Third derivative is sym(dq0 tensor lambda tensor lambda). Since q is invariant under the original group, every q-q derivative vanishes near the base.',
            'full_germ_reduction': 'Terms without q derivatives vanish from the q0-1 factor. The only q-dependent atom is atom0; its nongauge scalar and matter parts have no q derivatives. Its coframe lower coefficients multiply the common commuting principal product, whose sum is0. Gauge derivatives of inner vector coefficients multiply the vanished first gauge jet. Full inverse-chart curvature can contribute q-A-A-A, but there is no such fourth-order term; q-q-A-A is killed by the germ linear in q. Thus the displayed thirty nested values give the complete actual K3-K3-adjoint value.',
            'individual_nested_word_values': [{'word': list(w), 'value': str(v)} for w, v in words.items()],
            'actual_K3_minus_K3_adjoint': str(expected),
            'wrong_q_constant_coefficient_result': str(frozen)},
        'conclusion': 'The specified coefficient-left ordered formal temporal energy has a nonzero actual third-order formal-adjoint defect on the original vacuum Gauss domain, after using the true nonconstant a=G(q)d relation. This rejects formal symmetry of that particular K3, not the source action, a different action-derived quantum reduction, or existence of a proton.',
        'averaged_or_reordered_energy_installed': False,
        'summed_series_at_epsilon1_or_spectrum_or_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_temporal_energy_adjoint.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source temporal energy actual adjoint', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
