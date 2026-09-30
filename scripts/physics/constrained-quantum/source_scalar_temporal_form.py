#!/usr/bin/env python3
"""Original scalar adjoint form on the complete four-time coframe family.

The specified Pi-dagger Pi realization changes four fixed nongauge atoms.
Every shift coefficient and its scalar/gauge derivatives remain in the same
original momentum graph. No all-time coframe metric or summed temporal series
is supplied by this scalar construction.
"""
from __future__ import annotations

from functools import cached_property
import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode, ETA
from source_scalar_form_hamiltonian import SourceScalarFormHamiltonian, relocate_section
from source_quantum_temporal_symbol import N
from source_quantum_ordered_temporal import SourceTemporalQuantumFamily, OrderedTemporalCoefficients
from source_gauss_quantum_current import weighted_sum, encode_state
from source_quantum_grade_structure import occupation_grade


class SourceScalarTemporalForm:
    def __init__(self):
        self.form = SourceScalarFormHamiltonian()
        self.section = self.form.section
        self.native = self.form.native
        self.q = self.native.joint.coframe.q
        self.y = (s.Symbol('scalar_n', positive=True), *s.symbols('scalar_b1:4', real=True))
        self.e = self.native.joint.coframe.e.copy()
        self.e[:, 0] = s.Matrix(self.y)
        inverse = rational(self.e.inv())
        self.metric = rational(self.e.det()*inverse*ETA*inverse.T)
        self.weights = rational(s.Matrix([1/(2*self.metric[0, 0]),
            *[self.metric[0, i+1]/(2*self.metric[0, 0]) for i in range(3)]]))
        self.time_coefficients = rational(self.weights.jacobian(self.y))
        equal(self.weights, self.time_coefficients*s.Matrix(self.y))
        assert not set(self.y).intersection(self.time_coefficients.free_symbols)

    @cached_property
    def family(self):
        return SourceTemporalQuantumFamily(self.native)

    def coefficients(self, time_column, q, x, A):
        e = self.e.subs({**dict(zip(self.y, time_column)), **dict(zip(self.q, q))})
        return self.form.coefficients(e, x, A)

    def correction_coefficients(self, data, q):
        """Four fixed first-order operators; each consumes arbitrary CAR jets."""
        W = rational(self.time_coefficients.subs(dict(zip(self.q, q))))
        r = data['divergence']
        U = [clean(sum((data['spatial_A'][i, a]*self.form.scalar.c.rho[a]*data['phi']
                        for a in range(12)), s.zeros(70, 1))) for i in range(3)]
        rU = rational(s.Matrix([(r.T*u)[0] for u in U]))
        return [{'derivative': rational(-W[0, a]*data['adjoint_derivative']),
                 'current': rational(-s.I*W[0, a]*data['adjoint_current']),
                 'multiplication': s.cancel(s.I*(W[1:, a].T*rU)[0])}
                for a in range(4)]

    def correction_atom(self, coefficient, value, gradient):
        terms = [(coefficient['multiplication'], value)]
        for word, g in gradient.items():
            terms.append(((coefficient['derivative'].T*g)[0], {word: 1}))
        for a, scalar in enumerate(coefficient['current']):
            if scalar: terms.append((scalar, self.form.current(a, value)))
        return weighted_sum(terms)

    def correction_atoms(self, data, q, value, gradient):
        return [self.correction_atom(c, value, gradient)
                for c in self.correction_coefficients(data, q)]

    def nested_actions(self, data, value, gradient, Hessian):
        """Pi Pi and Pi-dagger Pi directly, including the differentiated shift."""
        old, new = [], []
        scalar = self.form.scalar
        for word in set(value)|set(gradient)|set(Hessian):
            f = value.get(word, 0)
            g = gradient.get(word, s.zeros(97, 1))
            H = Hessian.get(word, s.zeros(97))
            unit = {word: 1}
            for j in range(70):
                a = data['momentum_vectors'][j, :].T
                c = -data['normal_embedding'][j, :]
                b = data['shift'][j]
                derivative = scalar.directional_momentum(data, a)
                da = derivative['momentum_vectors'][j, :].T
                dc = -derivative['normal_embedding'][j, :]
                db = (data['shift_derivative'][j, :]*a)[0]
                inner = weighted_sum([(-s.I*(a.T*g)[0]-b*f, unit),
                                      (f, scalar.current(c, unit))])
                differentiated = weighted_sum([
                    (-s.I*((da.T*g)[0]+(a.T*H*a)[0])-db*f-b*(a.T*g)[0], unit),
                    (f, scalar.current(dc, unit)), ((a.T*g)[0], scalar.current(c, unit))])
                square = weighted_sum([(-s.I, differentiated),
                    (1, scalar.current(c, inner)), (-b, inner)])
                old.append((1/(2*data['h00']), square))
                new.extend([(1/(2*data['h00']), square),
                    (-s.I*data['divergence'][j]/(2*data['h00']), inner)])
            potential = (f*data['spatial_potential'], unit)
            old.append(potential); new.append(potential)
        return weighted_sum(old), weighted_sum(new)

    def atoms_at(self, q, x, A, word, gradient, Hessian, value=1):
        """Replace actual nongauge atoms0..3; original atoms4..13 are identical."""
        old, family_data = self.family.atoms_at(q, x, A, word, gradient, Hessian, value)
        data = self.form.coefficients(family_data['e'], x, A)
        delta = self.correction_atoms(data, q, {word: value}, {word: gradient[6:, :]})
        return [weighted_sum([(1, old[j]), (1, delta[j])]) if j < 4 else old[j]
                for j in range(14)], old, delta


def main():
    started = time.monotonic()
    m = SourceScalarTemporalForm()
    assert m.time_coefficients.det() != 0
    print('PASS original generic six-q/four-time scalar correction is exactly homogeneous affine', flush=True)
    q = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8),
         s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    time_column = (7*N/6, s.Rational(1, 13), -s.Rational(1, 17), s.Rational(1, 19))
    x = s.Matrix([s.Rational((3*j+1) % 7-3, 100) for j in range(61)])
    A = m.section.A0.copy()
    for i, denominator in enumerate((31, 37, 41)):
        A[i, 2] += s.Rational(1, denominator)
    data = m.coefficients(time_column, q, x, A)
    source_time = m.coefficients((N, 0, 0, 0), q, x, A)
    for name in ('F', 'momentum_vectors', 'normal_embedding', 'divergence'):
        equal(data[name], source_time[name])
    m.form.verify_coordinate_divergence(data)
    assert all(data['metric'][0, i] for i in range(1, 4))
    assert data['adjoint_shift'] and data['shift_derivative'].todok()
    coefficients = m.correction_coefficients(data, q)
    assert all(c['multiplication'] for c in coefficients[1:])
    print('PASS all three actual shifts, original derivatives and four nonzero source atom coefficients', flush=True)

    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    relocate_section(m.section, point)
    word = (144, 396)
    gradient100 = s.Matrix([s.I*s.Rational(j % 5-2, 47) for j in range(100)])
    u = s.Matrix([s.Rational(j % 3-1, 43) for j in range(100)])
    Hessian100 = u*u.T-s.eye(100)
    jet = m.section.extend_jet({word: 1}, {word: gradient100}, {word: Hessian100})
    gauss = m.section.verify_Gauss_jet(jet)
    values = {w: j['value'] for w, j in jet.items() if j['value']}
    gradients = {w: j['gradient'][6:, :] for w, j in jet.items()}
    Hessians = {w: j['Hessian'][6:, 6:] for w, j in jet.items()}
    old, new = m.nested_actions(data, values, gradients, Hessians)
    delta = m.correction_atoms(data, q, values, gradients)
    correction = weighted_sum(zip(time_column, delta))
    assert weighted_sum([(1, new), (-1, old), (-1, correction)]) == {}
    assert all(delta)
    assert weighted_sum([(1, correction), (-time_column[0], delta[0])])
    assert weighted_sum([(1, correction), (-1, m.form.correction(data, values, gradients))]) == {}
    print('PASS complete70 shifted nested form and four fixed correction atoms on actual Gauss two-jet', flush=True)

    # A separate direct97 divergence-form implementation rebuilds the original
    # coefficients from native exterior representations and differentiated solves.
    from independent_source_scalar_form_hamiltonian import RawGaussSection, raw_coefficients, form_action, general_scalar_action
    raw = RawGaussSection()
    e = m.e.subs({**dict(zip(m.y, time_column)), **dict(zip(m.q, q))})
    rd = raw_coefficients(raw.native, e, x, A)
    equal(rd['a'], data['momentum_vectors']); equal(rd['divergence'], data['divergence'])
    old_direct, new_direct = [], []
    for w, j in jet.items():
        args = (rd, w, j['value'], j['gradient'][6:, :], j['Hessian'][6:, 6:])
        old_direct.append((1, general_scalar_action(*args)))
        new_direct.append((1, form_action(*args)))
    assert weighted_sum([(1, old), (-1, weighted_sum(old_direct))]) == {}
    assert weighted_sum([(1, new), (-1, weighted_sum(new_direct))]) == {}
    assert rd['principal'][:61, 61:].todok()
    assert sum(rd['a'][j, u]*rd['db'][j, u] for j in range(70) for u in range(97)) != 0
    print('PASS independent full97 divergence form, differentiated shifts and scalar-gauge mixed symbol', flush=True)

    atom_terms = [[] for _ in range(14)]
    original_terms = [[] for _ in range(14)]
    for w, j in jet.items():
        atoms, original, _ = m.atoms_at(q, x, A, w, j['gradient'], j['Hessian'], j['value'])
        for a in range(14):
            atom_terms[a].append((1, atoms[a])); original_terms[a].append((1, original[a]))
    atoms = [weighted_sum(v) for v in atom_terms]
    original_atoms = [weighted_sum(v) for v in original_terms]
    for a in range(4): assert weighted_sum([(1, atoms[a]), (-1, original_atoms[a]), (-1, delta[a])]) == {}
    for a in range(4, 14): assert atoms[a] == original_atoms[a]
    ordered = OrderedTemporalCoefficients(); substitution = dict(zip(ordered.y, time_column))
    reconstructed = weighted_sum([(ordered.seed.subs(substitution), values)]+
        [(f.subs(substitution), atoms[a]) for a, f in enumerate(ordered.coefficients)]+
        [(ordered.coefficients[0].subs(substitution), atoms[13])])
    parts = {}
    for w, j in jet.items():
        _, original_parts, _ = m.family.action(time_column, q, x, A, w, j['gradient'], j['Hessian'], j['value'])
        for name, part in original_parts.items(): parts.setdefault(name, []).append((1, part))
    parts = {name: weighted_sum(v) for name, v in parts.items()}
    assert parts['scalar'] == old
    parts['scalar'] = new
    full_image = weighted_sum((1, v) for v in parts.values())
    assert weighted_sum([(1, reconstructed), (-1, full_image)]) == {}
    assert atoms[13] and all(occupation_grade(w) == 1 for w in atoms[13])
    assert all(occupation_grade(w) == 0 for a in range(4) for w in delta[a])
    print('PASS actual fourteen-atom four-time family with scalar-form replacements0..3 and unchanged original Yukawa', flush=True)

    files = [HERE/name for name in ('source_scalar_temporal_form.py',
        'source_scalar_form_hamiltonian.py', 'source_scalar_form_hamiltonian.json',
        'source_scalar_shift_quantum.py', 'source_gauss_live_ordering.py',
        'source_quantum_ordered_temporal.py', 'source_quantum_ordered_temporal.json',
        'source_quantum_gauss_section.py', 'source_quantum_stabilizer.py',
        'independent_source_scalar_form_hamiltonian.py', 'independent_source_quantum_gauss_section.py')]
    result = {'root': ROOT_ID, 'source_sha256': m.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'scope': 'ORIGINAL_FOUR_TIME_SCALAR_ADJOINT_FORM_AND_ACTUAL_FOURTEEN_ATOM_REPLACEMENT',
        'original_momentum_graph': 'Pi_b=-i a.partial+c-b, a=Rdual-O D^-T V, c=-O D^-T Q, b=sum_i h0i U_i. All a,c,r=div(a) are independent of the four time-column parameters.',
        'difference': 'Hscalar_form-Hscalar_old=-i sum_j r_j Pi_b,j/(2h00). This keeps the original real shift and its differentiated terms in both complete operators.',
        'generic_time_weights': encode(m.weights), 'generic_time_coefficients': encode(m.time_coefficients),
        'generic_affinity': 'The original metric density gives weights (1,h01,h02,h03)/(2h00)=W(q)*(n,b1,b2,b3). Multiplying the original time-independent graph and Ui generates four fixed first-order/CAR correction atoms. No finite time interpolation defines their coefficients.',
        'four_atoms': [{k: encode(v) if isinstance(v, s.MatrixBase) else str(v) for k, v in c.items()} for c in coefficients],
        'actual_consumer': {'time_column': list(map(str, time_column)), 'q': list(map(str, q)),
            'x61': encode(x), 'A36': encode(A), 'input_CAR': list(word),
            'gradient100': encode(gradient100), 'Hessian100': encode(Hessian100), 'Gauss': gauss,
            'all_three_shift_weights_nonzero': True, 'original_shift': encode(data['shift']),
            'shift_derivative_nonzero_entries': len(data['shift_derivative'].todok()),
            'original_full70_old_square': encode_state(old), 'original_full70_adjoint_form': encode_state(new),
            'four_correction_atom_images': [encode_state(v) for v in delta],
            'all_four_actual_corrections_nonzero': True, 'omit_shift_correction_nonzero': True,
            'independent_full97_divergence_and_nested70_images_equal': True,
            'scalar_gauge_cross_principal_and_shift_derivative_contraction_nonzero': True},
        'actual_fourteen_atom_consumer': {'all_four_component_images': {k: encode_state(v) for k, v in parts.items()},
            'all_fourteen_images': [encode_state(v) for v in atoms], 'whole_image': encode_state(full_image),
            'unchanged_atoms': list(range(4, 14)), 'original_Yukawa_atom13_unchanged': True,
            'all_four_delta_atoms_preserve_grade_and_particle_number': True,
            'old_ordered_scalar_coefficient_functions_and_source_seed_unchanged': True},
        'public_API': 'SourceScalarTemporalForm.coefficients, correction_coefficients, correction_atoms, nested_actions, atoms_at. atoms_at returns the new14, old14 and four correction images on arbitrary103 two-jets.',
        'ordering_scope': 'Only the specified scalar Pi-dagger Pi realization replaces the old scalar square. The unchanged free-word recurrence can consume these four new actual atoms; this file does not sum its temporal series or identify different quantization orders.',
        'all_time_coframe_metric_or_temporal_series_sum_or_spectrum_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_scalar_temporal_form.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source scalar temporal form', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
