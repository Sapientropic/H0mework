#!/usr/bin/env python3
"""Full native odd source velocities and their ordered independent-chi chain.

The reference remainder uses the existing zero-spatial-momentum1208 action.
It stays distinct from the nonlinear original Euler rows; the quantum chi
in the cotangent contraction is never replaced by its background value.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from scalar_dyson_peierls import annihilate_basis, create_basis
from source_canonical_euler_feedback import (
    SourceCanonicalEulerFeedback, SourceGerm, add_states)
from source_joint_ccr_car_ports import same, simplified
from source_gauss_quantum_current import apply_superposition, encode_state
from source_joint_form_hamiltonian import read_bound
from source_lorentz_contact import clean, equal, encode


def bundle(*terms):
    result = defaultdict(lambda: defaultdict(lambda: s.S.Zero))
    for coefficient, rows in terms:
        if not coefficient:
            continue
        for row, state in rows.items():
            for word, value in state.items():
                result[row][word] += coefficient*value
    return {row: state for row, value in result.items() if (state := simplified(value))}


def linear(M, rows):
    result = defaultdict(lambda: defaultdict(lambda: s.S.Zero))
    for (i, j), coefficient in M.todok().items():
        for word, value in rows.get(j, {}).items():
            result[i][word] += coefficient*value
    return {row: state for row, value in result.items() if (state := simplified(value))}


def car_bundle(state, creation):
    result = defaultdict(lambda: defaultdict(lambda: s.S.Zero))
    operation = create_basis if creation else annihilate_basis
    for word, value in state.items():
        for mode in range(504) if creation else word:
            output, sign = operation(mode, word)
            if sign:
                result[mode][output] += sign*value
    return {row: state for row, value in result.items() if (state := simplified(value))}


def current_bundle(M, rows):
    return {row: image for row, state in rows.items()
            if (image := simplified(apply_superposition(M, state)))}


def equal_bundle(left, right):
    for row in set(left)|set(right):
        same(left.get(row, {}), right.get(row, {}))


def encode_bundle(rows, dimension):
    return {'dimension': dimension,
            'nonzero_rows': [[row, encode_state(state)] for row, state in sorted(rows.items())]}


def matrix_key(M):
    return tuple(sorted(M.todok().items()))


def joint_source_germ():
    row = read_bound('source_joint_current_hilbert_section')['actual_consumer']
    word = tuple(row['input_CAR'])
    vector = decode(row['Hessian100']['rank_one_vector'])
    Hessian = vector*vector.T+s.sympify(row['Hessian100']['identity_coefficient'])*s.eye(100)
    return SourceGerm({word: s.S.One}, {word: decode(row['gradient100'])}, {word: Hessian})


class SourceNativeChiEulerForcing:
    def __init__(self):
        self.odd = SourceCanonicalEulerFeedback()
        self._reference = None

    def unit_velocities(self, germ, creation):
        """Every original504 CAR commutator, before the U-sector factors.

        The two ordered cubic terms of each original normal pair are applied
        separately. Scalar differential terms commute with constant CAR;
        the complete coefficient-left one-body/divM term remains.
        """
        model = self.odd
        sign = 1 if creation else -1
        values = car_bundle(germ.value, creation)
        matrix = model.differential_zero.one_body
        terms = [(sign*s.I, linear(matrix.T if creation else matrix, values))]
        for j, M in enumerate(model.data['linear_current']):
            gradient = {word: g[j] for word, g in germ.gradient.items() if g[j]}
            if gradient and M.todok():
                terms.append((sign, linear(M.T if creation else M,
                                          car_bundle(gradient, creation))))
        car_current_images = {}
        for coefficient, A, B in model.differential_zero.pairs:
            if creation:
                for left, right in ((A, B), (B, A)):
                    key = matrix_key(right)
                    if key not in car_current_images:
                        car_current_images[key] = car_bundle(
                            apply_superposition(right, germ.value), True)
                    terms.append((s.I*coefficient, linear(left.T, car_current_images[key])))
            else:
                terms.append((-s.I*coefficient, current_bundle(B, linear(A, values))))
                terms.append((-s.I*coefficient, current_bundle(A, linear(B, values))))
        return bundle(*terms)

    def density_velocity(self, germ, creation, power):
        """i[H,v^power] on a constant original CAR field times the germ."""
        model = self.odd
        _, g, H = model.volume_weight_jet(power)
        K = model.data['principal']
        direction = clean(g.T*K)
        scalar_state = {}
        for word in germ.words():
            scalar_state[word] = -2*s.I*(direction*germ.gradient.get(word, s.zeros(100, 1)))[0]
        c = (g.T*(model.data['linear_identity']-s.I*model.divergence))[0]
        c -= s.I*sum(value*H[i, j] for (i, j), value in K.todok().items())
        scalar_state = add_states((1, scalar_state), (c, germ.value))
        M = clean(sum((g[j]*model.data['linear_current'][j]
                       for j in (0, 2, 5)), s.zeros(504)))
        return bundle((1, car_bundle(scalar_state, creation)),
                      (1, current_bundle(M, car_bundle(germ.value, creation))))

    def velocities(self, germ):
        """Generate all three original real504 odd velocities from the same H."""
        model = self.odd
        unit_ann = self.unit_velocities(germ, False)
        unit_eta = self.unit_velocities(germ, True)
        ann_half = self.density_velocity(germ, False, -s.Rational(1, 2))
        eta_half = self.density_velocity(germ, True, s.Rational(1, 2))
        eta_inverse_half = self.density_velocity(germ, True, -s.Rational(1, 2))
        unit = {'primal': linear(model.psi_matrix, unit_ann),
                'momentum': linear(model.P_matrix, unit_eta),
                'chi': linear(model.chi_matrix, unit_eta)}
        density = {'primal': linear(model.psi_matrix, ann_half),
                   'momentum': linear(model.P_matrix, eta_half),
                   'chi': linear(model.chi_matrix, eta_inverse_half)}
        value = {'primal': linear(model.psi_matrix, car_bundle(germ.value, False)),
                 'momentum': linear(model.P_matrix, car_bundle(germ.value, True)),
                 'chi': linear(model.chi_matrix, car_bundle(germ.value, True))}
        velocity = {kind: bundle((1, unit[kind]), (1, density[kind])) for kind in unit}
        stationary = {kind: bundle((1, velocity[kind]),
            (-1, linear(model.phase_generators[kind], value[kind]))) for kind in unit}
        return {'values': value, 'unit_CAR_velocity': unit, 'density_velocity': density,
                'original_velocity': velocity, 'stationary_velocity': stationary}

    def ordered_chi_chain(self, germ, generated):
        """Differentiate the actual P=v Cchi0 chi; keep the operator order."""
        model = self.odd
        bare = self.density_velocity(germ, True, s.S.One)
        _, gv, _ = model.volume_weight_jet(1)
        _, gc, _ = model.volume_weight_jet(-s.Rational(1, 2))
        cross = -2*s.I*(gv.T*model.data['principal']*gc)[0]
        # Dv acts on the entire v^-1/2 chi germ, including its first jet.
        left = linear(model.chi_matrix, bundle((1, bare),
            (cross, car_bundle(germ.value, True))))
        right = linear(model.chi_matrix,
                       car_bundle(model.weight_derivation(1, germ), True))
        actual = generated['original_velocity']
        equal_bundle(actual['momentum'], linear(model.Cchi,
            bundle((1, actual['chi']), (1, left))))
        stationary = generated['stationary_velocity']
        equal_bundle(stationary['momentum'], linear(model.Cchi,
            bundle((1, stationary['chi']), (1, left))))
        Dv = model.weight_derivation(1, germ)
        background = {j: add_states((model.chi0_real[j], Dv))
                      for j in range(504) if model.chi0_real[j]}
        remainder = bundle((1, left), (-1, background))
        ordering = bundle((1, left), (-1, right))
        nonlinear = bundle((1, right), (-1, background))
        equal_bundle(remainder, bundle((1, nonlinear), (1, ordering)))
        return {'Dv_times_full_chi': left, 'chi_times_Dv': right,
                'ordering_remainder': ordering, 'background_Cchi_derivative': background,
                'chi_minus_chi0_part': nonlinear, 'complete_nonlinear_remainder': remainder}

    def reference(self):
        if self._reference is not None:
            return self._reference
        active = read_bound('source_active_phase_splice')
        physical = read_bound('source_physical_phase_splice')
        full = read_bound('source_full_linear_split')
        retained = read_bound('retained_hamiltonian_reduction')
        old = next(row for row in retained['source_momenta'] if row['momentum'] == ['0', '0', '0'])
        Xa, Ra = (decode(active[key]) for key in ('actual_active126_embedding', 'actual_active126_reader'))
        Xt, Rt = (decode(physical[key]) for key in ('tail_embedding_into_actual1208', 'tail_reader_from_actual1208'))
        tangent = decode(physical['original_nonlinear_chart_tangent'])
        leaf = self.odd.model.leaf
        expected = s.SparseMatrix(607, 604,
            {(row, col): 1 for col, row in enumerate(tuple(leaf.free)+tuple(range(103, 607)))})
        equal(tangent[:607, :604], expected)
        equal(tangent[:607, 604:], s.zeros(607, 604))
        tail = {key: decode(value) for key, value in full['triangular_tail'].items()}
        for key, value in tail.items():
            assert all(str(x) in ('k1', 'k2', 'k3') for x in value.free_symbols)
            tail[key] = clean(value.subs(dict.fromkeys(value.free_symbols, 0)))
        At = s.zeros(1082)
        for start, end, key in ((0, 480, 'dual'), (480, 602, 'scalar'), (602, 1082, 'primal')):
            At[start:end, start:end] = tail[key]
        At[480:602, :480] = tail['dual_to_scalar']
        At[602:, 480:602] = tail['scalar_to_primal']
        A = decode(old['Hamiltonian_generator'])
        equal(Ra*Xa, s.eye(126)); equal(Rt*Xt, s.eye(1082))
        equal(Ra*Xt, s.zeros(126, 1082)); equal(Rt*Xa, s.zeros(1082, 126))
        self._reference = {'Xa': Xa, 'Ra': Ra, 'Xt': Xt, 'Rt': Rt, 'Aa': A, 'At': At,
                           'chart_tangent': tangent}
        return self._reference

    def native_canonical_values(self, germ, generated):
        """Actual free canonical values, including U(-i partial)U^-1."""
        model = self.odd
        point = s.Matrix(model.z)
        values, source = {}, s.zeros(1208, 1)
        source[:100, :] = point
        psi0 = model.phase.psi0
        source[100:604, :] = psi0.applyfunc(s.re).col_join(psi0.applyfunc(s.im))
        p0 = model.phase.p0.T
        source[704:, :] = (-p0.applyfunc(s.im)).col_join(-p0.applyfunc(s.re))
        rho = s.zeros(100, 1)
        rho[6:, :] = model.model.at_time(model.data['scalar']['ell'])
        for j in range(100):
            values[j] = add_states((point[j], germ.value))
            native = {}
            for word in germ.words():
                ell = rho[j]+(s.Rational(len(word)+2, 2)/point[j] if j in (0, 2, 5) else 0)
                native[word] = -s.I*germ.gradient.get(word, s.zeros(100, 1))[j]+s.I*ell*germ.value.get(word, 0)
            values[604+j] = simplified(native)
        for j, state in generated['values']['primal'].items(): values[100+j] = state
        for j, state in generated['values']['momentum'].items(): values[704+j] = state
        background = {j: add_states((value, germ.value)) for (j, _), value in source.todok().items()}
        delta = bundle((1, values), (-1, background))
        return {'values': values, 'source': source, 'delta': delta, 'rho_half_gradient': rho}

    def source_reference_remainder(self, germ, generated):
        ref = self.reference()
        canonical = self.native_canonical_values(germ, generated)
        a, t = linear(ref['Ra'], canonical['delta']), linear(ref['Rt'], canonical['delta'])
        equal_bundle(canonical['delta'], bundle((1, linear(ref['Xa'], a)), (1, linear(ref['Xt'], t))))
        derivative = bundle((1, linear(ref['Xa'], linear(ref['Aa'], a))),
                            (1, linear(ref['Xt'], linear(ref['At'], t))))
        rpsi = bundle((1, generated['stationary_velocity']['primal']),
                      (-1, {j-100: state for j, state in derivative.items() if 100 <= j < 604}))
        corrections = [self.odd._full_chi_coframe_product(axis, rpsi) for axis in range(16)]
        return {'canonical': canonical, 'active126': a, 'tail1082': t,
                'reference_derivative': derivative, 'primal_reference_remainder': rpsi,
                'coframe_cotangent_contractions': corrections}


def main():
    started = time.monotonic()
    for name in ('source_canonical_euler_feedback', 'source_joint_current_hilbert_section'):
        read_bound(name)
    source = SourceNativeChiEulerForcing()
    germ = joint_source_germ()
    result = source.velocities(germ)
    print('PASS full504 primal, canonical dual and independent chi generated by the original H', flush=True)
    for kind in ('primal', 'momentum', 'chi'):
        for j in (5, 144, 257, 396):
            same(result['original_velocity'][kind].get(j, {}), source.odd.heisenberg(kind, j, germ))
    chain = source.ordered_chi_chain(germ, result)
    assert chain['ordering_remainder'] and chain['chi_minus_chi0_part']
    print('PASS exact full-chi time chain, nonzero ordering and chi-minus-chi0 remainders', flush=True)
    reference = source.source_reference_remainder(germ, result)
    assert reference['primal_reference_remainder']
    for a in (0, 4, 8, 12):
        assert not reference['coframe_cotangent_contractions'][a]['full_fixed_p_minus_fixed_chi_correction']
    assert any(row['nonlinear_chi_minus_chi0_remainder'] for row in reference['coframe_cotangent_contractions'])
    print('PASS same1208 original phase, active126+tail1082 and full-chi reference contraction', flush=True)
    paths = ['source_native_chi_euler_forcing.py', 'source_canonical_euler_feedback.py',
        'source_canonical_euler_feedback.json', 'source_joint_ccr_car_ports.py',
        'source_joint_current_hilbert_section.py', 'source_joint_current_hilbert_section.json',
        'source_active_phase_splice.py', 'source_active_phase_splice.json',
        'source_physical_phase_splice.py', 'source_physical_phase_splice.json',
        'source_full_linear_split.py', 'source_full_linear_split.json',
        'retained_hamiltonian_reduction.json', 'source_common_phase_time.py',
        'source_common_hamiltonian.py']
    out = {'root': ROOT_ID, 'scope': 'FULL_NATIVE_ODD_HEISENBERG_AND_ORDERED_CHI_REFERENCE_REMAINDER',
        'source_sha256': read_bound('source_canonical_euler_feedback')['source_sha256'],
        'input_sha256': {str((HERE/name).relative_to(ROOT)): hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in paths},
        'public_mouth': 'velocities(source100_germ) generates all original504 real primal, canonical momentum and independent-chi fields and Heisenberg velocities from the fixed current H; source_reference_remainder uses the original zero-k1208 carrier.',
        'source': {'values': encode_state(germ.value),
            'gradient100': [[list(w), encode(g)] for w, g in germ.gradient.items()],
            'Hessian100': [[list(w), encode(H)] for w, H in germ.Hessian.items()]},
        'complete_odd_outputs': {key: {kind: encode_bundle(rows, 504) for kind, rows in value.items()}
                                 for key, value in result.items()},
        'ordered_chi_time_chain': {key: encode_bundle(rows, 504) for key, rows in chain.items()},
        'canonical_reference': {'actual1208_values': encode_bundle(reference['canonical']['values'], 1208),
            'original_source1208': encode(reference['canonical']['source']),
            'actual1208_displacement': encode_bundle(reference['canonical']['delta'], 1208),
            'active126': encode_bundle(reference['active126'], 126),
            'tail1082': encode_bundle(reference['tail1082'], 1082),
            'original_reference_derivative': encode_bundle(reference['reference_derivative'], 1208),
            'primal504_reference_remainder': encode_bundle(reference['primal_reference_remainder'], 504),
            'full_chi_all16_cotangent_contractions': [{key: encode_state(value) for key, value in row.items()}
                for row in reference['coframe_cotangent_contractions']]},
        'source_time': 'The old co-rotating K is subtracted after generating i[H,O]; tau=N*t is unchanged.',
        'classification': {'ordered_full_chi_and_odd_velocity': 'source producer',
            'zero_k1208_active126_tail1082_split': 'existing reference transporter consumed on generated source fields',
            'nonlinear_original_Euler_and289_ambient_momentum_velocity_feed': 'separate downstream consumer of the actual ambient update and original auxiliary/constraint reactions'},
        'seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_native_chi_euler_forcing.json').write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print('PASS native chi source and full original reference remainder', out['seconds'], flush=True)


if __name__ == '__main__': main()
