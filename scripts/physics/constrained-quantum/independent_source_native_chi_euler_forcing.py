#!/usr/bin/env python3
"""All504 odd fields from exact-field bit-CAR Hamiltonian action.

This audit composes the paid differential Hamiltonian with each original
creation/annihilation operator. It does not use the candidate's batched CAR
commutator or density-velocity assembler. The ordered chi chain is checked by
literal products, and the zero-k reference is applied as one1208 matrix.
"""
from collections import defaultdict
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import time

import sympy as s

import source_native_chi_euler_forcing as candidate
from source_canonical_euler_feedback import SourceGerm
from source_spatial_active_phase_splice import DOMAIN as D, field_element as field, dm
from independent_source_gauge_legendre import bindings, decode
from independent_source_canonical_euler_feedback import bit_linear

HERE, ROOT = candidate.HERE, candidate.ROOT


def mask(word): return sum(1 << j for j in word)


def bits(value):
    while value:
        low = value & -value
        yield low.bit_length()-1
        value -= low


def step(value, mode, creation):
    if bool(value & (1 << mode)) == creation:
        return None, 0
    return value ^ (1 << mode), (-1)**((value & ((1 << mode)-1)).bit_count())


def add(*terms):
    out = defaultdict(lambda: D.zero)
    for coefficient, values in terms:
        if coefficient:
            for word, value in values.items(): out[word] += coefficient*value
    return {word: value for word, value in out.items() if value}


def car(values, mode, creation):
    out = {}
    for word, value in values.items():
        changed, sign = step(word, mode, creation)
        if sign: out[changed] = out.get(changed, D.zero)+sign*value
    return {word: value for word, value in out.items() if value}


def exact_state(values):
    return {mask(word): field(value) for word, value in values.items() if value}


def columns(matrix):
    out = defaultdict(list)
    for (i, j), value in s.SparseMatrix(matrix).todok().items():
        if value: out[int(j)].append((int(i), field(value)))
    return out


def current(matrix, values):
    out = defaultdict(lambda: D.zero)
    for word, value in values.items():
        for j in bits(word):
            first, a = step(word, j, False)
            for i, coefficient in matrix[j]:
                second, b = step(first, i, True)
                if b: out[second] += a*b*coefficient*value
    return {word: value for word, value in out.items() if value}


def normal(left, right, values):
    out = defaultdict(lambda: D.zero)
    for word, value in values.items():
        for j in bits(word):
            first, a = step(word, j, False)
            for l in bits(first):
                second, b = step(first, l, False)
                for k, rk in right[l]:
                    third, c = step(second, k, True)
                    if not c: continue
                    for i, li in left[j]:
                        last, d = step(third, i, True)
                        if d: out[last] += a*b*c*d*li*rk*value
    return {word: value for word, value in out.items() if value}


def row_linear(matrix, rows):
    out = defaultdict(lambda: defaultdict(lambda: D.zero))
    for (i, j), coefficient in s.SparseMatrix(matrix).todok().items():
        coefficient = field(coefficient)
        for word, value in rows.get(j, {}).items(): out[i][word] += coefficient*value
    return {i: row for i, values in out.items() if (row := {w: v for w, v in values.items() if v})}


def row_add(*terms):
    keys = set().union(*(rows for _, rows in terms))
    return {i: row for i in keys if (row := add(*[(c, rows.get(i, {})) for c, rows in terms]))}


def compare_rows(actual, expected, dimension):
    assert all(0 <= i < dimension for i in actual)
    assert all(0 <= i < dimension for i in expected)
    for i in range(dimension):
        expected_row = exact_state(expected.get(i, {}))
        assert actual.get(i, {}) == expected_row, (i, len(actual.get(i, {})), len(expected_row))


def unpack_germ(record):
    return SourceGerm({tuple(w): s.sympify(v) for w, v in record['values']},
        {tuple(w): decode(g) for w, g in record['gradient100']},
        {tuple(w): decode(h) for w, h in record['Hessian100']})


class LiteralOdd:
    def __init__(self, odd, germ):
        self.odd, self.germ = odd, germ
        self.imaginary = field(s.I)
        zero = odd.differential_zero
        self.constant, self.matrix = field(zero.scalar), columns(zero.one_body)
        unique = {}
        def get(M):
            key = tuple(sorted(M.todok().items()))
            if key not in unique: unique[key] = columns(M)
            return unique[key]
        self.pairs = [(field(c), get(A), get(B)) for c, A, B in zero.pairs]
        self.words = sorted(germ.words())
        self.value = exact_state(germ.value)
        self.prepared = {}
        self.base = self.H(0)

    @lru_cache(None)
    def H0(self, word):
        state = {word: D.one}
        return add((self.constant, state), (D.one, current(self.matrix, state)),
                   *[(c, normal(A, B, state)) for c, A, B in self.pairs])

    def jet_coefficients(self, power):
        if power in self.prepared: return self.prepared[power]
        q = s.symbols('literal_volume_q0:3', positive=True)
        v = s.prod(q)**power
        point = dict.fromkeys(q, 1)
        axes = (0, 2, 5)
        dv, ddv = s.zeros(100, 1), s.zeros(100)
        for i, a in enumerate(axes):
            dv[a] = s.diff(v, q[i]).subs(point)
            for j, b in enumerate(axes): ddv[a, b] = s.diff(v, q[i], q[j]).subs(point)
        output = []
        data = self.odd.data
        for word in self.words:
            f = self.germ.value.get(word, 0)
            g = self.germ.gradient.get(word, s.zeros(100, 1))
            h = self.germ.Hessian.get(word, s.zeros(100))
            changed_g = g+dv*f
            changed_h = h+dv*g.T+g*dv.T+ddv*f
            central = -sum(c*changed_h[i, j] for (i, j), c in data['principal'].todok().items())
            central -= ((self.odd.divergence+s.I*data['linear_identity']).T*changed_g)[0]
            entries = defaultdict(lambda: s.S.Zero)
            for j, M in enumerate(data['linear_current']):
                if changed_g[j]:
                    for index, value in M.todok().items():
                        entries[index] -= s.I*changed_g[j]*value
            differential = s.SparseMatrix(504, 504, dict(entries))
            output.append((mask(word), field(f), field(central), columns(differential)))
        self.prepared[power] = output
        return output

    def H(self, power, mode=None, creation=False):
        terms = []
        for word, value, central, differential in self.jet_coefficients(power):
            output, sign = (word, 1) if mode is None else step(word, mode, creation)
            if not sign: continue
            state = {output: D.one}
            if value: terms.append((sign*value, self.H0(output)))
            if central: terms.append((sign*central, state))
            terms.append((D.convert(sign), current(differential, state)))
        return add(*terms)

    def generate(self):
        raw_values = {creation: {j: image for j in range(504)
            if (image := car(self.value, j, creation))} for creation in (False, True)}
        raw_unit, raw_weighted, H_weighted = {}, {}, {}
        for creation in (False, True):
            unit = {}
            for j in range(504):
                image = add((self.imaginary, self.H(0, j, creation)),
                            (-self.imaginary, car(self.base, j, creation)))
                if image: unit[j] = image
            raw_unit[creation] = unit
            powers = (-s.Rational(1, 2), s.Rational(1, 2)) if creation else (-s.Rational(1, 2),)
            for power in powers:
                weighted, Hrows = {}, {}
                for j in range(504):
                    Hrows[j] = self.H(power, j, creation)
                    image = add((self.imaginary, Hrows[j]),
                                (-self.imaginary, car(self.base, j, creation)))
                    if image: weighted[j] = image
                raw_weighted[creation, power] = weighted
                H_weighted[creation, power] = Hrows
            print('PASS all504 independently composed bit-CAR fields', 'creation' if creation else 'annihilation', flush=True)
        values, unit, density, velocity, stationary = {}, {}, {}, {}, {}
        for kind in ('primal', 'momentum', 'chi'):
            M, creation, power = self.odd.specification(kind)
            values[kind] = row_linear(M, raw_values[creation])
            unit[kind] = row_linear(M, raw_unit[creation])
            velocity[kind] = row_linear(M, raw_weighted[creation, power])
            density[kind] = row_add((D.one, velocity[kind]), (-D.one, unit[kind]))
            stationary[kind] = row_add((D.one, velocity[kind]),
                (-D.one, row_linear(self.odd.phase_generators[kind], values[kind])))
        self.H_weighted = H_weighted
        return {'values': values, 'unit_CAR_velocity': unit, 'density_velocity': density,
                'original_velocity': velocity, 'stationary_velocity': stationary}

    def chi_chain(self, generated):
        plus, minus = (self.H_weighted[True, power] for power in (s.Rational(1, 2), -s.Rational(1, 2)))
        left = row_linear(self.odd.chi_matrix, row_add((self.imaginary, plus), (-self.imaginary, minus)))
        Dv = add((self.imaginary, self.H(1)), (-self.imaginary, self.base))
        right = row_linear(self.odd.chi_matrix, {j: car(Dv, j, True) for j in range(504)})
        background = {j: add((field(c), Dv)) for j, c in enumerate(self.odd.chi0_real) if c}
        ordering = row_add((D.one, left), (-D.one, right))
        nonlinear = row_add((D.one, right), (-D.one, background))
        remainder = row_add((D.one, left), (-D.one, background))
        assert ordering and nonlinear
        for key in ('original_velocity', 'stationary_velocity'):
            expected = row_linear(self.odd.Cchi, row_add((D.one, generated[key]['chi']), (D.one, left)))
            assert expected == generated[key]['momentum']
        return {'Dv_times_full_chi': left, 'chi_times_Dv': right, 'ordering_remainder': ordering,
            'background_Cchi_derivative': background, 'chi_minus_chi0_part': nonlinear,
            'complete_nonlinear_remainder': remainder}


def reference_consumer(source, germ, generated):
    odd = source.odd
    active = json.loads((HERE/'source_active_phase_splice.json').read_text())
    physical = json.loads((HERE/'source_physical_phase_splice.json').read_text())
    full = json.loads((HERE/'source_full_linear_split.json').read_text())
    retained = json.loads((HERE/'retained_hamiltonian_reduction.json').read_text())
    row = next(r for r in retained['source_momenta'] if r['momentum'] == ['0', '0', '0'])
    Xa, Ra = (decode(active[k]) for k in ('actual_active126_embedding', 'actual_active126_reader'))
    Xt, Rt = (decode(physical[k]) for k in ('tail_embedding_into_actual1208', 'tail_reader_from_actual1208'))
    Aa = decode(row['Hamiltonian_generator'])
    tail = {k: decode(v) for k, v in full['triangular_tail'].items()}
    tail = {k: A.subs(dict.fromkeys(A.free_symbols, 0)) for k, A in tail.items()}
    At = s.zeros(1082)
    for left, right, key in ((0, 480, 'dual'), (480, 602, 'scalar'), (602, 1082, 'primal')):
        At[left:right, left:right] = tail[key]
    At[480:602, :480], At[602:, 480:602] = tail['dual_to_scalar'], tail['scalar_to_primal']
    decomposition = dm(Xa)*dm(Ra)+dm(Xt)*dm(Rt)
    assert (decomposition-dm(s.eye(1208))).is_zero_matrix
    reference = dm(Xa)*dm(Aa)*dm(Ra)+dm(Xt)*dm(At)*dm(Rt)
    assert (reference*dm(Xa)-dm(Xa)*dm(Aa)).is_zero_matrix
    assert (reference*dm(Xt)-dm(Xt)*dm(At)).is_zero_matrix
    values, background = {}, {}
    f = exact_state(germ.value)
    z = odd.z
    # Consume the independently generated rho3 density of the previous
    # signed odd producer; differentiate its literal U_m for each sector.
    signed = json.loads((HERE/'independent_source_canonical_euler_feedback.json').read_text())
    assert signed['original_primitives']['original_residual_orbit_density'] == '8*u3**2*u4'
    axes = tuple(signed['original_primitives']['rho_coordinates_generated_from_original_orbit'])
    q = s.symbols('reference_U0:5', positive=True)
    coords = (0, 2, 5, *axes)
    point = dict(zip(q, [z[j] for j in coords]))
    for j in range(100):
        values[j] = add((field(z[j]), f))
        background[j] = values[j]
        state = {}
        for word in germ.words():
            U = s.sqrt(8*q[3]**2*q[4])*s.prod(q[:3])**s.Rational(len(word)+2, 2)
            ell = (s.diff(U, q[coords.index(j)])/U).subs(point) if j in coords else 0
            value = -s.I*germ.gradient.get(word, s.zeros(100, 1))[j]+s.I*ell*germ.value.get(word, 0)
            if value: state[mask(word)] = field(value)
        if state: values[604+j] = state
    psi0, p0 = odd.phase.psi0, odd.phase.p0.T
    q0 = psi0.applyfunc(s.re).col_join(psi0.applyfunc(s.im))
    P0 = (-p0.applyfunc(s.im)).col_join(-p0.applyfunc(s.re))
    for j in range(504):
        if j in generated['values']['primal']: values[100+j] = generated['values']['primal'][j]
        if j in generated['values']['momentum']: values[704+j] = generated['values']['momentum'][j]
        if q0[j]: background[100+j] = add((field(q0[j]), f))
        if P0[j]: background[704+j] = add((field(P0[j]), f))
    delta = row_add((D.one, values), (-D.one, background))
    derivative = row_linear(reference.to_Matrix(), delta)
    rpsi = row_add((D.one, generated['stationary_velocity']['primal']),
        (-D.one, {j-100: value for j, value in derivative.items() if 100 <= j < 604}))
    assert rpsi
    corrections = []
    for variation in odd.phase.dE:
        A, B = variation.applyfunc(s.re), variation.applyfunc(s.im)
        coefficient = A.row_join(-B).col_join((-B).row_join(-A))
        whole, linear = [], []
        for (i, j), c in coefficient.todok().items():
            if j not in rpsi: continue
            chi = {}
            for mode, scalar in enumerate(odd.chi_matrix[i, :]):
                if scalar: chi = add((D.one, chi), (field(scalar), car(rpsi[j], mode, True)))
            whole.append((-field(c), chi))
            linear.append((-field(c*odd.chi0_real[i]), rpsi[j]))
        full_chi, background_chi = add(*whole), add(*linear)
        corrections.append((full_chi, background_chi, add((D.one, full_chi), (-D.one, background_chi))))
    return {'values': values, 'delta': delta, 'derivative': derivative, 'rpsi': rpsi,
        'active': row_linear(Ra, delta), 'tail': row_linear(Rt, delta), 'corrections': corrections}


def main():
    started = time.monotonic()
    path = HERE/'source_native_chi_euler_forcing.json'
    receipt = json.loads(path.read_text()); checked = bindings(receipt)
    assert receipt['root'] == candidate.ROOT_ID
    previous = json.loads((HERE/'independent_source_canonical_euler_feedback.json').read_text())
    inherited = bindings(previous)
    source = candidate.SourceNativeChiEulerForcing()
    germ = unpack_germ(receipt['source'])
    expected = source.velocities(germ)
    literal = LiteralOdd(source.odd, germ)
    actual = literal.generate()
    for category, values in actual.items():
        for kind, rows in values.items(): compare_rows(rows, expected[category][kind], 504)
    print('PASS all504x3 complete odd values, unit/density velocities and stationary velocities', flush=True)
    chain = literal.chi_chain(actual)
    expected_chain = source.ordered_chi_chain(germ, expected)
    for key, rows in chain.items(): compare_rows(rows, expected_chain[key], 504)
    print('PASS literal D(v chi), chi Dv and the complete quantum-chi remainder', flush=True)
    reference = reference_consumer(source, germ, actual)
    target = source.source_reference_remainder(germ, expected)
    for ours, theirs, n in (('values', target['canonical']['values'], 1208),
        ('delta', target['canonical']['delta'], 1208), ('derivative', target['reference_derivative'], 1208),
        ('active', target['active126'], 126), ('tail', target['tail1082'], 1082),
        ('rpsi', target['primal_reference_remainder'], 504)):
        compare_rows(reference[ours], theirs, n)
    names = ('full_fixed_p_minus_fixed_chi_correction', 'background_Ce0_transporter', 'nonlinear_chi_minus_chi0_remainder')
    for j, values in enumerate(reference['corrections']):
        for key, value in zip(names, values): assert value == exact_state(target['coframe_cotangent_contractions'][j][key])
    assert all(not reference['corrections'][j][0] for j in (0, 4, 8, 12))
    assert any(v[2] for v in reference['corrections'])
    print('PASS complete1208 original reference operator, scalar+tail decomposition and all16 full-chi contractions', flush=True)
    assert bindings(receipt) == checked
    paths = [Path(__file__), path, HERE/'source_native_chi_euler_forcing.py',
        HERE/'source_canonical_euler_feedback.py', HERE/'source_canonical_euler_feedback.json',
        HERE/'independent_source_canonical_euler_feedback.py', HERE/'independent_source_canonical_euler_feedback.json',
        HERE/'source_spatial_active_phase_splice.py', HERE/'source_active_phase_splice.json',
        HERE/'source_physical_phase_splice.json', HERE/'source_full_linear_split.json',
        HERE/'retained_hamiltonian_reduction.json']
    result = {'root': candidate.ROOT_ID, 'verdict': 'CERTIFIED_ALL504_ODD_FIELDS_ORDERED_CHI_CHAIN_AND_FULL_REFERENCE_CONSUMER',
        'source_sha256': receipt['source_sha256'], 'candidate_binding_checks': checked, 'inherited_odd_binding_checks': inherited,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'method': 'Exact QQ(sqrt2,sqrt15,i) occupation masks compose the full paid differential H with every504 creation/annihilation field. Literal scalar product twojets retain both derivative orders.',
        'checked_rows_per_category': 1512, 'categories': list(actual),
        'native_input_numbers': sorted({len(w) for w in germ.words()}),
        'original_source_nonzero_normal_pairs': len(literal.pairs),
        'chi_ordering_defect_nonzero_rows': len(chain['ordering_remainder']),
        'chi_minus_background_nonzero_rows': len(chain['chi_minus_chi0_part']),
        'original_reference_primal_remainder_nonzero_rows': len(reference['rpsi']),
        'original1208_identity_split_and_generator_intertwining': True,
        'all16_full_chi_ordered_cotangent_contractions': True,
        'background_substitution_changes_the_actual_output': True,
        'scope': 'External finite CAR source100 twojets are allowed; the fixed root generates H, phase, density and maps. The zero-k1208 operator is the signed reference-linear action. Full nonlinear original Euler, original289 feed and null-Ward9 compatibility are not inferred from this reference decomposition.',
        'seconds': round(time.monotonic()-started, 3)}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent all504 chi source', result['seconds'], flush=True)


if __name__ == '__main__': main()
