#!/usr/bin/env python3
"""Literal sector density, bit CAR and original four-energy odd commutators.

The received construction draft is independently audited here. The original
residual orbit regenerates rho3, a complex-row calculation regenerates chi,
and new full504 germs consume the literal four-energy operator.
"""
from collections import defaultdict
import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_joint_ccr_car_ports import NormalSymbol, SourceJointCCRCarPorts, linear_car, same, simplified
from source_joint_current_heisenberg import patch_symbolic_equal
from source_gauss_quantum_current import apply_superposition, weighted_sum
from source_lorentz_contact import clean, equal
from real_scalar_car_source import real_bilinear, realify
from source_common_phase_time import OriginalCanonicalPhase
from source_joint_form_hamiltonian import read_bound
from independent_source_quantum_gauss_section import RawGaussSection
from independent_source_common_hamiltonian import original_inventory
from independent_source_lorentz_quantum_section import BitAction, total
from independent_source_gauge_legendre import hodge, W as WEDGE, SIGMA, ETA
from source_joint_current_hilbert_section import current_weyl_action
import source_canonical_euler_feedback as candidate


def bit_linear(row, state, creation=False):
    """Integer occupation masks; no producer creation/annihilation helper."""
    out = defaultdict(lambda: 0)
    columns = [(j, value) for j, value in enumerate(row) if value]
    for word, coefficient in state.items():
        mask = sum(1 << j for j in word)
        for j, value in columns:
            occupied = bool(mask & (1 << j))
            if occupied == creation:
                continue
            sign = (-1)**((mask & ((1 << j)-1)).bit_count())
            target = mask ^ (1 << j)
            output = tuple(i for i in range(target.bit_length()) if target & (1 << i))
            out[output] += sign*coefficient*value
    return simplified(out)


def states(records):
    return {tuple(word): s.sympify(value) for word, value in records}


def sparse_germ(receipt):
    return {'v': states(receipt['values']),
        'g': {tuple(word): decode(value) for word, value in receipt['gradients100']},
        'h': {tuple(word): decode(value) for word, value in receipt['Hessians100']}}


def words(germ):
    return set(germ['v'])|set(germ['g'])|set(germ['h'])


def scalar_multiply(germ, jet_by_number):
    out = {'v': {}, 'g': {}, 'h': {}}
    for word in words(germ):
        value, first, second = jet_by_number(len(word))
        a = germ['v'].get(word, 0)
        b = germ['g'].get(word, s.zeros(100, 1))
        c = germ['h'].get(word, s.zeros(100))
        out['v'][word] = s.expand(value*a)
        out['g'][word] = clean(value*b+first*a)
        out['h'][word] = clean(value*c+first*b.T+b*first.T+second*a)
    return out


def car_multiply(germ, row, creation):
    out = {'v': defaultdict(lambda: 0), 'g': {}, 'h': {}}
    for word in words(germ):
        for image, coefficient in bit_linear(row, {word: 1}, creation).items():
            out['v'][image] += coefficient*germ['v'].get(word, 0)
            out['g'][image] = out['g'].get(image, s.zeros(100, 1))+coefficient*germ['g'].get(word, s.zeros(100, 1))
            out['h'][image] = out['h'].get(image, s.zeros(100))+coefficient*germ['h'].get(word, s.zeros(100))
    return out


def fresh_source_divergences(model, section, phase):
    """Differentiate original inverse equations at this actual source point."""
    rat = lambda A: s.SparseMatrix(A).applyfunc(s.cancel)
    raw, y = section.native, section.source[6:, :]
    free = [j-6 for j in section.free if j >= 6]
    pivots = [j-6 for j in section.fixed]
    O, phi = raw.O, raw.v+raw.R*y[:61, :]
    D = O.T*s.Matrix.hstack(*(T*phi for T in raw.rhob))
    F, parameters = D.T.gauss_jordan_solve(s.eye(9)); assert parameters.rows == 0
    B = s.Matrix.vstack(*((T*y).T for T in raw.Tb))
    S = s.Matrix.hstack(*(T*y for T in raw.Ts))
    M = S[pivots, :]
    U, parameters = M.gauss_jordan_solve(s.eye(3)); assert parameters.rows == 0
    T = S[free, :]*U
    horizontal = B[:, free]-B[:, pivots]*T.T
    reader = s.eye(9).row_join(-B[:, pivots]*U.T)
    a = raw.Rd.row_join(s.zeros(70, 33))-O*F*horizontal
    c = -O*F*reader
    pivot_gauge = s.eye(97)[61:, pivots]
    ag = s.eye(97)[61:, free]-pivot_gauge*T.T
    cg = s.zeros(36, 9).row_join(-pivot_gauge*U.T)
    e = phase.e0
    h00 = (e.det()*e.inv()*ETA*e.inv().T)[0, 0]
    constitutive = rat(-WEDGE*hodge(e)/SIGMA)
    weight = rat(s.kronecker_product(constitutive[:3, :3].inv(), raw.Gram.inv()))
    target = model.data
    equal(rat(a), target['scalar']['a']); equal(rat(c), target['scalar']['current'])
    equal(rat(ag), target['gauge']['a']); equal(rat(cg), target['gauge']['current'])
    scalar_current, gauge_current = s.zeros(1, 12), s.zeros(1, 12)
    scalar_K, gauge_K = s.zeros(1, 94), s.zeros(1, 94)
    for j, u in enumerate(free):
        dD = O.T*s.Matrix.hstack(*(R*raw.R[:, u] for R in raw.rhob)) if u < 61 else s.zeros(9)
        dF, parameters = D.T.gauss_jordan_solve(-dD.T*F); assert parameters.rows == 0
        dS = s.Matrix.hstack(*(R[:, u] for R in raw.Ts))
        dU, parameters = M.gauss_jordan_solve(-dS[pivots, :]*U); assert parameters.rows == 0
        dT = dS[free, :]*U+S[free, :]*dU
        dB = s.Matrix.vstack(*(R[:, u].T for R in raw.Tb))
        d_horizontal = dB[:, free]-dB[:, pivots]*T.T-B[:, pivots]*dT.T
        d_reader = s.zeros(9).row_join(-dB[:, pivots]*U.T-B[:, pivots]*dU.T)
        da, dc = rat(-O*(dF*horizontal+F*d_horizontal)), rat(-O*(dF*reader+F*d_reader))
        dag, dcg = rat(-pivot_gauge*dT.T), s.zeros(36, 9).row_join(rat(-pivot_gauge*dU.T))
        scalar_current += (da[:, j].T*c+a[:, j].T*dc)/h00
        gauge_current += dag[:, j].T*weight*cg+ag[:, j].T*weight*dcg
        scalar_K += (da[:, j].T*a+a[:, j].T*da)/(2*h00)
        gauge_K += (dag[:, j].T*weight*ag+ag[:, j].T*weight*dag)/2
    scalar_current, gauge_current, scalar_K, gauge_K = map(rat, (scalar_current, gauge_current, scalar_K, gauge_K))
    equal(scalar_current.T, model.model.at_time(target['scalar']['div_momentum_current']))
    equal(gauge_current.T, model.model.at_time(target['gauge']['div_momentum_current']))
    equal(scalar_K.T, model.model.at_time(target['scalar']['div_principal']))
    equal(gauge_K.T, model.model.at_time(target['gauge']['div_principal']))
    charges = raw.Qb+raw.Qs
    for left, right in zip(charges, model.model.leaf.charges): equal(left, right)
    divergence = sum((value*Q for value, Q in zip(scalar_current+gauge_current, charges)), s.zeros(504))
    # The six spin factors are differentiated as literal rational curves,
    # independently of the candidate's summed diff expression.
    q = model.model.leaf.weyl.native.joint.coframe.q
    variable = s.Symbol('fresh_source_current_curve', real=True)
    spin = s.zeros(8)
    divK = s.zeros(100, 1)
    for j in range(6):
        sub = dict(zip(q, model.z[:6])); sub[q[j]] += variable
        family = model.model.at_time(model.model.leaf.pairing['Mh'][j].subs(sub))
        base = family.subs(variable, 0)
        spin += rat((family-base)/variable).subs(variable, 0)
        curveK = model.model.at_time(model.model.leaf.pairing['K'][j, :].subs(sub))
        dK = rat((curveK-curveK.subs(variable, 0))/variable).subs(variable, 0)
        divK[:6, :] += dK.T
    divergence += s.kronecker_product(spin, s.eye(63))
    divK[6:, :] = (scalar_K+gauge_K).T
    return rat(divergence), rat(divK)


class IndependentSourceOdd:
    def __init__(self, original_model):
        patch_symbolic_equal()
        self.model = original_model
        self.z = tuple(self.model.leaf.source_point[i] for i in self.model.leaf.free)
        self.data = self.model.coefficients(self.z)
        raw = read_bound('real_scalar_car_source')
        phase = OriginalCanonicalPhase()
        self.phase = phase
        I = s.eye(252)
        self.U = clean(I.row_join(s.I*I).col_join(I.row_join(-s.I*I))/s.sqrt(2))
        equal(self.U, decode(raw['complex_branch_unitary']))
        inverse_e, volume = phase.e0.inv(), phase.e0.det()
        gamma = original_inventory()['gamma']
        self.E = clean(s.kronecker_product(s.I*volume*sum(
            (inverse_e[0, a]*gamma[a] for a in range(4)), s.zeros(4)), s.eye(63)))
        equal(self.E, phase.E)
        Cchi = real_bilinear(self.E.T)
        Ei = clean(self.E.inv().T)
        # P=(-Im p,-Re p), hence chi^T=E^-T(P_real-i P_imag).
        # Take its two real coordinates before introducing the branch CAR.
        inverse_chi = clean(Ei.applyfunc(s.re).row_join(Ei.applyfunc(s.im)).col_join(
            Ei.applyfunc(s.im).row_join(-Ei.applyfunc(s.re))))
        equal(Cchi*inverse_chi, s.eye(504))
        self.maps = {'primal': self.U.H, 'momentum': clean(s.I*self.U.T),
                     'chi': clean(s.I*inverse_chi*self.U.T)}
        self.generators = {'primal': realify(s.I*phase.omega*phase.Rp),
            'momentum': phase.Kpsi, 'chi': realify(s.I*phase.omega*phase.Rd.T)}
        equal(self.maps['primal']*self.maps['momentum'].T, s.I*s.eye(504))
        equal(Cchi*self.maps['chi'], self.maps['momentum'])
        assert self.maps['chi'] != self.maps['primal'].conjugate()
        section = RawGaussSection()
        equal(section.free_reader*section.source, s.Matrix(self.z))
        divergence, self.divK = fresh_source_divergences(self, section, phase)
        self.current_divergence = clean(divergence)
        self.zero = NormalSymbol(0, clean(self.data['zero'].one_body-s.I*divergence/2), self.data['zero'].pairs)
        assert self.zero.pairs
        variables = s.Matrix(s.symbols('density_z0:100', real=True))
        full = section.free_reader.T*variables+section.reader.T*section.reader*section.source
        orbit = s.Matrix.hstack(*(T*full for T in section.T))
        density = s.factor(s.sign(section.source_minor.det())*(section.reader*orbit).det())
        gauge_axes = sorted(list(variables).index(symbol) for symbol in density.free_symbols)
        assert len(gauge_axes) == 2
        self.variables = s.symbols('u0:5', positive=True)
        self.axes = (0, 2, 5, *gauge_axes)
        self.point = dict(zip(self.variables, [self.z[i] for i in self.axes]))
        self.volume = self.variables[0]*self.variables[1]*self.variables[2]
        density = density.subs(dict(zip(variables, self.z)) | {
            variables[axis]: variable for axis, variable in zip(gauge_axes, self.variables[3:])})
        self.density = s.factor(density/density.subs(self.point))
        self.original_density = density
        self.jets = {}
        self.CAR = BitAction()
        self.normal_cache = {}

    def derivative_jet(self, expression):
        at = lambda value: s.simplify(value.subs(self.point))
        first, second = s.zeros(100, 1), s.zeros(100)
        for i, axis in enumerate(self.axes):
            first[axis] = at(s.diff(expression, self.variables[i]))
            for j, other in enumerate(self.axes):
                second[axis, other] = at(s.diff(expression, self.variables[i], self.variables[j]))
        return at(expression), first, second

    def density_jet(self, number, inverse=False):
        key = number, inverse
        if key not in self.jets:
            U = self.volume**(1+s.Rational(number, 2))
            U *= s.sqrt(self.density)
            self.jets[key] = self.derivative_jet(1/U if inverse else U)
        return self.jets[key]

    def transported(self, kind, index, germ):
        native = scalar_multiply(germ, lambda number: self.density_jet(number, True))
        native = car_multiply(native, self.maps[kind][index, :], kind != 'primal')
        if kind == 'chi':
            native = scalar_multiply(native, lambda _: self.derivative_jet(1/self.volume))
        return scalar_multiply(native, self.density_jet)

    def odd_normal_port(self, row, creation, state, symbol):
        def act(values):
            if not symbol.pairs:
                return total((symbol.scalar, values), (1, self.CAR.Q(symbol.one_body, values)))
            key = id(symbol), tuple(sorted(values.items()))
            if key not in self.normal_cache:
                self.normal_cache[key] = self.CAR.raw.hamiltonian(symbol, values)
            return self.normal_cache[key]
        return total((s.I, act(bit_linear(row, state, creation))),
                     (-s.I, bit_linear(row, act(state), creation)))

    def action(self, kind, index, germ):
        row, creation = self.maps[kind][index, :], kind != 'primal'
        bare = car_multiply(germ, row, creation)
        transported = self.transported(kind, index, germ)
        same(bare['v'], transported['v'])
        terms = [(1, self.odd_normal_port(row, creation, germ['v'], self.zero))]
        for j, M in enumerate(self.data['linear_current']):
            gradient = {word: value[j] for word, value in germ['g'].items() if value[j]}
            if gradient and M.todok():
                terms.append((-s.I, self.odd_normal_port(row, creation, gradient, NormalSymbol(0, M, ()))))
        unit = simplified(weighted_sum(terms))
        first, second = {}, {}
        for word in words(transported)|words(bare):
            first[word] = clean(transported['g'].get(word, s.zeros(100, 1))-bare['g'].get(word, s.zeros(100, 1)))
            second[word] = clean(transported['h'].get(word, s.zeros(100))-bare['h'].get(word, s.zeros(100)))
        scalar = {}
        for word in first:
            scalar[word] = -sum(value*second[word][i, j] for (i, j), value in self.data['principal'].todok().items())
            scalar[word] -= ((self.divK+s.I*self.data['linear_identity']).T*first[word])[0]
        correction = [(s.I, scalar)]
        for j, M in enumerate(self.data['linear_current']):
            gradient = {word: value[j] for word, value in first.items() if value[j]}
            if gradient and M.todok(): correction.append((1, apply_superposition(M, gradient)))
        correction = simplified(weighted_sum(correction))
        actual = simplified(weighted_sum(((1, unit), (1, correction))))
        phase = simplified(weighted_sum((value, bit_linear(self.maps[kind][j, :], germ['v'], creation))
            for (i, j), value in self.generators[kind].todok().items() if i == index))
        return actual, correction, simplified(weighted_sum(((1, actual), (-1, phase))))


def to_source_germ(germ):
    return candidate.SourceGerm(germ['v'], germ['g'], germ['h'])


def jet_equal(left, right):
    same(left['v'], right.value)
    for word in words(left)|right.words():
        equal(left['g'].get(word, s.zeros(100, 1)), right.gradient.get(word, s.zeros(100, 1)))
        equal(left['h'].get(word, s.zeros(100)), right.Hessian.get(word, s.zeros(100)))


def new_four_energy_consumer(model, producer):
    pair, hidden = (137, 391), (202,)
    germ = {'v': {(): s.Rational(3, 11), pair: s.I/17},
        'g': {(): s.SparseMatrix(100, 1, {(0, 0): s.I/19, (5, 0): s.Rational(1, 23), (8, 0): -s.Rational(1, 29)}),
              pair: s.SparseMatrix(100, 1, {(2, 0): s.Rational(1, 31), (73, 0): -s.I/37}),
              hidden: s.SparseMatrix(100, 1, {(0, 0): -s.I/41, (96, 0): s.Rational(1, 43)})},
        'h': {(): s.SparseMatrix(100, 100, {(0, 5): s.I/47, (5, 0): s.I/47, (2, 2): s.Rational(1, 53)}),
              pair: s.SparseMatrix(100, 100, {(0, 2): s.Rational(1, 59), (2, 0): s.Rational(1, 59), (8, 8): s.I/61}),
              hidden: s.SparseMatrix(100, 100, {(2, 5): s.I/67, (5, 2): s.I/67})}}
    def literal(g):
        return current_weyl_action(model.model, model.data, g['v'], g['g'], g['h'])
    full_H = literal(germ)
    source_germ = to_source_germ(germ)
    same(producer.H(source_germ), full_H)
    rows = []
    for kind in ('primal', 'momentum', 'chi'):
        for index in (137, 389):
            transported = model.transported(kind, index, germ)
            jet_equal(transported, producer.observable_jet(kind, index, source_germ))
            HO = literal(transported)
            same(producer.H(to_source_germ(transported)), HO)
            actual = total((s.I, HO), (-s.I, bit_linear(model.maps[kind][index, :], full_H, kind != 'primal')))
            independent, correction, stationary = model.action(kind, index, germ)
            same(actual, independent)
            same(actual, producer.heisenberg(kind, index, source_germ))
            same(stationary, producer.stationary_heisenberg(kind, index, source_germ))
            assert correction
            same(total((1, actual), (-1, correction)),
                 producer.heisenberg(kind, index, source_germ, keep_density_derivatives=False))
            rows.append({'kind': kind, 'coordinate': index, 'full_literal_commutator_words': len(actual),
                'nonzero_density_derivative_defect_words': len(correction),
                'output_numbers': sorted({len(word) for word in actual})})
            print('PASS new full504 literal four-energy bitCAR commutator', kind, index, flush=True)
    dropped = {key: {word: value for word, value in part.items() if word != hidden} for key, part in germ.items()}
    assert total((1, full_H), (-1, literal(dropped)))
    return {'original_full_H_normal_quartic_pairs': len(model.zero.pairs),
        'fresh_nonzero_value_words': [[], list(pair)], 'retained_zero_value_derivative_word': list(hidden),
        'complete_coefficient_left_H_compared_to_all_four_literal_energies': True,
        'dropping_zero_value_derivative_germ_changes_H': True, 'commutators': rows}


def original_phase_and_density(model, producer):
    for kind in model.maps:
        equal(model.maps[kind], producer.specification(kind)[0])
        equal(model.generators[kind], producer.phase_generators[kind])
    equal(model.current_divergence, producer.current_divergence)
    equal(model.divK, producer.divergence)
    equal(model.zero.one_body, producer.differential_zero.one_body)
    phase = model.phase
    unit = (s.Integer(3)+4*s.I)/5
    Up = s.diag(*(s.expand_complex(unit**rate) for rate in phase.rates))
    Ud = s.diag(*(s.expand_complex(unit**rate) for rate in phase.dual_rates))
    equal(Ud*model.E*Up, model.E)
    assert phase.Rd != -phase.Rp
    t = s.Symbol('source_epoch_time', real=True)
    for kind, matrix in model.maps.items():
        pulled = (s.eye(504)-t*model.generators[kind])*matrix
        equal(pulled.diff(t), -model.generators[kind]*matrix)
    e, inverse, volume = phase.e0, phase.e0.inv(), phase.e0.det()
    gamma = original_inventory()['gamma']
    tangent = s.zeros(504, 16)
    for j in range(16):
        direction = s.zeros(4); direction[j] = 1
        d_inverse = -inverse*direction*inverse
        d_volume = volume*s.trace(inverse*direction)
        dE = clean(s.kronecker_product(s.I*sum(
            ((d_volume*inverse[0, a]+volume*d_inverse[0, a])*gamma[a] for a in range(4)), s.zeros(4)), s.eye(63)))
        equal(dE, phase.dE[j])
        p_derivative = -s.I*phase.chi0*dE
        tangent[:, j] = (-p_derivative.T.applyfunc(s.im)).col_join(-p_derivative.T.applyfunc(s.re))
    equal(tangent, producer.Ce0)
    equal(phase.N*s.Matrix([phase.omega/phase.N]), s.Matrix([phase.omega]))
    assert s.simplify(phase.omega/phase.N-3*s.sqrt(2)/5) == 0
    v = model.volume
    for number in (0, 1, 2, 3, 7):
        U = s.sqrt(model.density)*v**(1+s.Rational(number, 2))
        for jump in (-1, 1):
            ratio = s.sqrt(model.density)*v**(1+s.Rational(number+jump, 2))/U
            assert s.simplify(ratio-v**s.Rational(jump, 2)) == 0
            actual = model.derivative_jet(ratio)
            reference = producer.volume_weight_jet(s.Rational(jump, 2))
            assert actual[0] == reference[0]
            equal(actual[1], reference[1]); equal(actual[2], reference[2])
    return {'original_residual_orbit_density': str(model.original_density),
        'rho_coordinates_generated_from_original_orbit': list(model.axes[3:]),
        'literal_U_m_inverse_native_CAR_U_next_first_and_second_jets': True,
        'all504_chi_maps_from_complex_row_i_p_E_inverse': True,
        'all16_background_cotangent_columns_from_original_complex_p_derivative': True,
        'all100_current_and_principal_divergences_fresh_at_actual_source': True,
        'independent_dual_Rd_distinct_from_negative_Rp': True,
        'finite_original_phase_and_epoch_minus_K_derivative': True,
        'source_frequency': str(phase.omega), 'proper_frequency': str(s.simplify(phase.omega/phase.N)),
        'proper_clock': 'tau=N*t; every proper-time derivative is the source-time derivative divided by the same N.'}


def mutable_germ_consumer(model, producer):
    germ = {'v': {(): s.Rational(2, 7)},
            'g': {(): s.SparseMatrix(100, 1, {(0, 0): s.Rational(1, 11)})},
            'h': {(): s.SparseMatrix(100, 100, {(2, 2): s.Rational(1, 13)})}}
    shared = to_source_germ(germ)
    previous = producer.H(shared)
    changes = []
    for kind in ('value', 'gradient', 'Hessian'):
        if kind == 'value':
            germ['v'][()] += s.Rational(1, 17)
        elif kind == 'gradient':
            germ['g'][()][0] += s.I/19
        else:
            germ['h'][()][2, 2] += s.Rational(1, 23)
        expected = current_weyl_action(model.model, model.data, germ['v'], germ['g'], germ['h'])
        actual = producer.H(shared)
        same(actual, expected)
        assert total((1, actual), (-1, previous))
        previous = actual
        independent, _, _ = model.action('momentum', 137, germ)
        same(producer.heisenberg('momentum', 137, shared), independent)
        changes.append(kind)
    return {'same_SourceGerm_object_reused': True,
        'original_four_energy_H_and_bitCAR_commutator_after_each_mutation': changes,
        'all_three_changes_have_nonzero_H_defect_against_stale_output': True}


def main():
    began = time.monotonic()
    path = HERE/'source_canonical_euler_feedback.json'
    receipt = json.loads(path.read_bytes())
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in receipt[key].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    producer = candidate.SourceCanonicalEulerFeedback()
    model = IndependentSourceOdd(producer.model)
    primitives = original_phase_and_density(model, producer)
    print('PASS raw orbit density, original complex chi order, full504 maps and phase/clock', flush=True)
    germ = sparse_germ(receipt['actual_cross_N_source'])
    rows = []
    for row in receipt['actual_cross_N_source']['consumers']:
        actual, correction, stationary = model.action(row['kind'], row['real_coordinate'], germ)
        same(actual, states(row['original_source_Heisenberg']))
        same(correction, states(row['unit_CAR_omission_defect']))
        same(stationary, states(row['stationary_reference_velocity']))
        assert correction
        rows.append({'kind': row['kind'], 'real_coordinate': row['real_coordinate'],
            'independent_full_U_N_inverse_native_CAR_U_next_twojet': True,
            'whole_normal_quartic_CAR_and_current_gradient_formula': True,
            'original_moving_phase_velocity_retained': True,
            'nonzero_density_derivative_output_words': len(correction)})
        print('PASS independent source sector transport and normal-CAR odd action', row['kind'], row['real_coordinate'], flush=True)
    assert len(rows) == 12
    fresh = new_four_energy_consumer(model, producer)
    mutations = mutable_germ_consumer(model, producer)
    print('PASS same mutable germ after value/gradient/Hessian updates', flush=True)
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in receipt[key].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    paths = [path, HERE/'source_canonical_euler_feedback.py', HERE/'independent_source_canonical_euler_feedback.py',
        HERE/'source_joint_ccr_car_ports.py', HERE/'source_scalar_weyl_symbol.py', HERE/'source_common_weyl_symbol.py',
        HERE/'real_scalar_car_source.json', HERE/'source_gauss_section_measure.json',
        HERE/'independent_source_quantum_gauss_section.py', HERE/'independent_source_quantum_stabilizer.py',
        HERE/'independent_source_common_hamiltonian.py', HERE/'independent_source_lorentz_quantum_section.py',
        HERE/'independent_source_joint_charge_conservation.py', HERE/'source_joint_current_hilbert_section.py']
    out = {'root': ROOT_ID, 'scope': 'INDEPENDENT_NATIVE_ODD_SOURCE_OBSERVABLE_DENSITY_AND_HEISENBERG',
        'source_sha256': receipt['source_sha256'],
        'candidate_binding_checks': sum(len(receipt[key]) for key in ('source_sha256', 'input_sha256')),
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'all_original504_maps_checked': True, 'canonical_CAR_pairing_matrix': 'i I504',
        'independent_chi_not_replaced_by_primal_adjoint': True,
        'original_primitives': primitives, 'consumers': rows, 'fresh_four_energy_consumer': fresh,
        'mutable_germ_consumer': mutations,
        'classification': 'The actual odd same-H producer and density twojets are certified. Ce0 is a background cotangent transporter; no full quantum chi-Euler/Ward or complete289 retarded feed is inferred.',
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_canonical_euler_feedback.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS independent source odd observables', out['seconds'], flush=True)


if __name__ == '__main__': main()
