#!/usr/bin/env python3
"""Actual even time forces and the same-coframe Lorentz balance.

The original four-time form acts after its existing positive-pairing pullback.
The generated output is a two-jet on the thirteen time/orbit directions,
embedded in the original122 configuration coordinates. Its horizontal100
output derivatives are not inferred from an input two-jet.
"""
from __future__ import annotations
import hashlib
import json
import time
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from source_joint_current_hilbert_section import SourceJointCurrentHilbertSection
from source_common_temporal_form import SourceCommonTemporalForm
from source_joint_ccr_car_ports import simplified, same
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_quantum_gauss_section import exterior_word
from source_coframe_live_ordering import full
from source_lorentz_quantum_section import TIME
from source_temporal_gauss_relations import shift_images
from source_quantum_temporal_symbol import N
from source_lorentz_contact import equal, encode
from source_joint_form_hamiltonian import read_bound
from source_lorentz_temporal_ordering import SourceLorentzTemporalOrdering


def combine(*terms):
    return simplified(weighted_sum(terms))


class SourceTemporalLorentzBalance:
    """Raw finite CAR-valued source100 two-jets are the only producer input."""
    def __init__(self):
        self.current = SourceJointCurrentHilbertSection()
        self.common = SourceCommonTemporalForm()
        m = self.current.section
        self.spin, self.native = m.spin, self.common.section
        self.q, self.x, self.A = m.spin.q, s.zeros(61, 1), m.gauge.A0
        self.y = self.common.family.y
        self.y0 = s.Matrix([N, 0, 0, 0])
        self.at_clock = dict(zip(self.y, self.y0))
        self.data = self.common.coefficients(self.y, self.q, self.x, self.A)
        self.T = self.spin.native.lorentz.basis
        self.R = self.spin.R + self.native.R
        self.ordering = SourceLorentzTemporalOrdering()
        self.original_covariance = self.ordering.primitive_covariance()
        equal(self.ordering.ambient.e, self.data['e'])
        for key in ('K', 'W', 'drift', 'correction', 'one_body'):
            equal(self.ordering.ambient.data[key], self.data['coframe'][key])
        self.base122 = m.spin.e.reshape(16, 1).col_join(m.gauge.source.base[6:, :])
        columns = [s.eye(122)[:, i] for i in TIME] + m.orbit[:6] + m.orbit[15:18]
        self.directions122 = s.Matrix.hstack(*columns)
        assert self.directions122.rank() == 13

    def canonical_symbols(self, state, extra=()):
        # The established coframe action has a serialized diagnostic boundary;
        # restore the exact source symbols before taking any derivative.
        symbols = {str(v): v for v in (*self.y, *extra)}
        return {w: c.xreplace({a: symbols[str(a)] for a in c.free_symbols
            if str(a) in symbols}) for w, c in state.items()}

    def generate(self, value, gradient, Hessian):
        parameters = set(map(str, self.y))
        coefficients = list(value.values())
        coefficients += [c for row in (*gradient.values(), *Hessian.values()) for c in row]
        assert all(not parameters.intersection(map(str, s.sympify(c).free_symbols)) for c in coefficients)
        native_germ = self.current.inverse_half_density_jet(value, gradient, Hessian)
        jet103 = self.native.extend_jet(*native_germ)
        action = self.common.action(self.data, jet103)
        image = simplified(self.canonical_symbols(action['H']))
        qgradient = {w: g[:6, :] for w, g in native_germ[1].items()}
        qHessian = {w: H[:6, :6] for w, H in native_germ[2].items()}
        coframe_jet = self.ordering.source.extend_jet(native_germ[0], qgradient, qHessian)
        ambient = self.ordering.ambient.ambient_action(coframe_jet)
        coframe = self.canonical_symbols(action['pieces']['coframe'])
        difference = self.ordering.difference(native_germ[0], qgradient)
        same(combine((1, ambient), (-1, coframe)), difference)
        current_difference = self.ordering.difference(value,
            {w: g[:6, :] for w, g in gradient.items()}, current_pairing=True)
        same(difference, current_difference)
        result = _SourceTemporalLorentzOrbitImage(self, native_germ, jet103, image)
        result.coframe_ordering_difference = current_difference
        return result


class _SourceTemporalLorentzOrbitImage:
    """Generated family and its actual time/orbit jets; no constraint witness."""
    def __init__(self, source, native_germ, input103, family):
        self.source, self.native_germ, self.input103 = source, native_germ, input103
        self.family = family
        self.value = simplified({w: c.subs(source.at_clock) for w, c in family.items()})
        self.time_first = [simplified({w: s.diff(c, y).subs(source.at_clock)
            for w, c in family.items()}) for y in source.y]
        self.time_second = [[simplified({w: s.diff(c, y, z).subs(source.at_clock)
            for w, c in family.items()}) for z in source.y] for y in source.y]
        self.forces = [combine((-1, row)) for row in self.time_first]
        self._input122 = None

    def input122(self):
        if self._input122 is None:
            self._input122 = self.source.current.section.extend_jet(*self.native_germ)
        return self._input122

    def orbit_direction_jet(self, coefficients):
        """True output two-jet along an original122 time/orbit curve.

        Parameters are time4, spatial Lorentz6, residual su(2)3. Body time is
        exp(-t T)(y0+t dy), a frame readout of the same coframe column.
        """
        u = s.Matrix(coefficients)
        assert u.shape == (13, 1)
        m = self.source
        X = sum((u[4+j]*m.T[j] for j in range(6)), s.zeros(4))
        R = sum((u[4+j]*m.R[j] for j in range(9)), s.zeros(504))
        body1 = u[:4, :]-X*m.y0
        body2 = X*X*m.y0-2*X*u[:4, :]
        df = combine(*((v, row) for v, row in zip(body1, self.time_first) if v))
        first = combine((1, apply_superposition(R, self.value)), (1, df))
        second = combine((1, apply_superposition(R, apply_superposition(R, self.value))),
            (2, apply_superposition(R, df)),
            *((v, row) for v, row in zip(body2, self.time_first) if v),
            *((body1[i]*body1[j], self.time_second[i][j])
              for i in range(4) for j in range(4) if body1[i]*body1[j]))
        e2 = s.zeros(122, 1)
        spatial = m.spin.e.copy(); spatial[:, 0] = s.zeros(4, 1)
        e2[:16, :] = (X*X*spatial).reshape(16, 1)
        G = sum((u[10+j]*m.current.section.gauge.L[9+j]
            for j in range(3)), s.zeros(112))
        e2[16:, :] = (G*G*m.current.section.gauge.source.base)[6:, :]
        return {'value': self.value, 'first': first, 'second': second,
            'configuration122_first': m.directions122*u,
            'configuration122_second': e2}

    def noether_ports(self):
        """Original primary actions on Hf, and i[H,primary]f."""
        m = self.source
        spatial, full_lorentz, commutator = [], [], []
        for j, T in enumerate(m.T):
            derivative = self.orbit_direction_jet(s.eye(13)[:, 4+j])['first']
            Gsp = combine((-s.I, derivative), (s.I, apply_superposition(m.spin.R[j], self.value)))
            time_part = combine(*((s.I*v, self.forces[mu])
                for mu, v in enumerate(T*m.y0) if v))
            spatial.append(Gsp); full_lorentz.append(combine((1, Gsp), (1, time_part)))
            commutator.append(combine((-s.I, Gsp)))
        gauss = []
        for h in range(3):
            derivative = self.orbit_direction_jet(s.eye(13)[:, 10+h])['first']
            gauss.append(combine((-s.I, derivative),
                (s.I, apply_superposition(m.native.R[h], self.value))))
        return {'temporal_primary_on_H': [combine((s.I, f)) for f in self.forces],
            'i_H_temporal_primary': self.forces, 'spatial_primary_on_H': spatial,
            'i_H_spatial_primary': commutator, 'full_Lorentz_primary_on_H': full_lorentz,
            'residual_su2_primary_on_H': gauss}


def finite_lorentz_consumers(image):
    m = image.source; t = s.Symbol('source_lorentz_curve', real=True)
    results = []
    for j, (T, S) in enumerate(zip(m.T, m.spin.native.lorentz.spin)):
        if j < 3:
            Lam = s.eye(4)+s.sinh(t)*T+(s.cosh(t)-1)*T*T
            spin = s.cosh(t/2)*s.eye(4)+2*s.sinh(t/2)*S
        else:
            Lam = s.eye(4)+s.sin(t)*T+(1-s.cos(t))*T*T
            spin = s.cos(t/2)*s.eye(4)+2*s.sin(t/2)*S
        equal(Lam.diff(t).subs(t, 0), T); equal(spin.diff(t).subs(t, 0), S)
        body = Lam.subs(t, -t)*m.y0
        CAR = full(s.diag(spin, spin.conjugate()))
        finite = weighted_sum((s.cancel(c.subs(dict(zip(m.y, body)))), exterior_word(CAR, w))
            for w, c in image.family.items())
        actual = [simplified({w: s.diff(c, t, k).subs(t, 0)
            for w, c in finite.items()}) for k in (1, 2)]
        jet = image.orbit_direction_jet(s.eye(13)[:, 4+j])
        same(actual[0], jet['first']); same(actual[1], jet['second'])
        results.append({'direction': j, 'finite_first': encode_state(actual[0]),
            'finite_second': encode_state(actual[1])})
    return results


def original_native_consumers(image):
    """Differentiate original coefficients and the full transformed input jet."""
    m = image.source; t = s.Symbol('source_native_curve', real=True)
    results = []
    for h in range(3):
        L, R = m.native.L[h], m.native.R[h]
        delta = L*m.native.b0
        transformed = {}
        def add(word, value, g, H):
            row = transformed.setdefault(word, {'value': s.S.Zero,
                'gradient': s.zeros(103, 1), 'Hessian': s.zeros(103)})
            row['value'] += value; row['gradient'] += g; row['Hessian'] += H
        for w, row in image.input103.items():
            add(w, row['value'], row['gradient']-t*L.T*row['gradient'],
                row['Hessian']-t*(L.T*row['Hessian']+row['Hessian']*L))
            for v, c in apply_superposition(R, {w: 1}).items():
                add(v, t*c*row['value'], t*c*row['gradient'], t*c*row['Hessian'])
        point = m.native.b0+t*delta
        data = m.common.coefficients(m.y, m.q, point[6:67, :], point[67:, :].reshape(3, 12))
        out = m.canonical_symbols(m.common.action(data, transformed)['H'], (t,))
        derivative = simplified({w: s.diff(c, t).subs(t, 0) for w, c in out.items()})
        same(derivative, apply_superposition(R, image.family))
        for mu, y in enumerate(m.y):
            actual = simplified({w: -s.diff(c, y).subs(m.at_clock) for w, c in derivative.items()})
            same(actual, apply_superposition(R, image.forces[mu]))
        results.append({'generator': h, 'original_H_directional_image': encode_state(derivative),
            'all_four_force_derivative_identities': True})
    return results


def main():
    began = time.monotonic()
    bound = read_bound('source_joint_current_hilbert_section')
    for name in ('source_common_temporal_form', 'source_temporal_gauss_relations',
                 'source_coframe_constraints', 'source_quantum_stabilizer', 'source_lorentz_temporal_ordering'):
        read_bound(name)
    source = SourceTemporalLorentzBalance()
    word = (5, 144, 396)
    value = {word: s.S.One}
    gradient = {word: s.Matrix([s.I*s.Rational(j % 7-3, 31) for j in range(100)])}
    u = s.Matrix([s.Rational(j % 5-2, 37) for j in range(100)])
    Hessian = {word: u*u.T-s.eye(100)}
    image = source.generate(value, gradient, Hessian)
    old = {tuple(w): s.sympify(c) for w, c in bound['actual_consumer']['returned_current_H']}
    same(image.value, old)
    _, a, d, _, _ = shift_images(source.common.scalar, source.q, source.x, source.A, image.input103)
    for j in range(3):
        same(a[j], d[j]); same(image.forces[j+1], combine((-1, a[j]), (1/N**2, d[j])))
        assert image.forces[j+1]
    print('PASS current H and actual all4 time forces; nonzero3 shifts consume a=Gd', flush=True)
    curves = finite_lorentz_consumers(image)
    ports = image.noether_ports()
    assert not any(ports['full_Lorentz_primary_on_H']) and not any(ports['residual_su2_primary_on_H'])
    for j in range(6):
        expected = combine(*((-v, image.forces[mu]) for mu, v in enumerate(source.T[j]*source.y0) if v))
        same(ports['i_H_spatial_primary'][j], expected)
        assert bool(expected) == (j < 3)
    print('PASS six finite Lorentz first/second derivatives and original primary/time-force sign', flush=True)
    native = original_native_consumers(image)
    print('PASS three original su(2) Hamiltonian derivatives and all12 force consumers', flush=True)
    generated122 = image.input122()
    assert all(row['gradient'].rows == 122 and row['Hessian'].shape == (122, 122)
        for row in generated122.values())
    files = ('source_temporal_lorentz_balance.py', 'source_joint_current_hilbert_section.py',
        'source_joint_current_hilbert_section.json', 'source_common_temporal_form.py',
        'source_common_temporal_form.json', 'source_quantum_ordered_temporal.py',
        'source_temporal_gauss_relations.py', 'source_temporal_gauss_relations.json',
        'source_lorentz_quantum_section.py', 'source_joint_quantum_section.py',
        'source_coframe_constraints.json', 'source_quantum_stabilizer.json',
        'source_lorentz_temporal_ordering.py', 'source_lorentz_temporal_ordering.json')
    out = {'root': ROOT_ID, 'scope': 'CURRENT_H_EVEN_TIME_FORCES_AND_SOURCE_TRANSPORTED_THIRTEEN_ORBIT_TWO_JET',
        'source_sha256': bound['source_sha256'],
        'input_sha256': {str((HERE/f).relative_to(ROOT)): hashlib.sha256((HERE/f).read_bytes()).hexdigest()
            for f in files}, 'source_clock': 'tau=N*t, N=3*sqrt(30)/25; body time is the same coframe column in its original Lorentz frame.',
        'original_tensor_covariance': source.original_covariance,
        'actual_alltime_coframe_ordering_difference_on_same_germ': encode_state(image.coframe_ordering_difference),
        'current_H': encode_state(image.value), 'forces_minus_time_derivative': [encode_state(f) for f in image.forces],
        'time_Hessian': [[encode_state(v) for v in row] for row in image.time_second],
        'native_shift_atoms': [encode_state(v) for v in a], 'gauge_cross_atoms': [encode_state(v) for v in d],
        'original122_direction_frame': encode(source.directions122), 'source122_base': encode(source.base122),
        'generated_input122_words': len(generated122), 'finite_Lorentz_consumers': curves,
        'original_native_derivative_consumers': native,
        'noether_ports': {k: [encode_state(v) for v in rows] for k, rows in ports.items()},
        'orbit_transport_provenance': 'The original generic16 Dirac/Hodge tensors and full H/G/metric-lift/current covariance are freshly consumed. The complete four-time ambient-minus-reduced coframe operator is then evaluated on the same raw germ and matched to the existing half-density pullback; its nonzero b-squared ordering terms are retained. Thus the orbit extension transports the current ordering, with the raw ambient ordering separately identified.',
        'jet_contract': 'orbit_direction_jet(u13) generates Hf and both derivatives on time4/spatial-Lorentz6/residual-su2-3 curves, with both original122 configuration derivatives. Arbitrary horizontal100 output jets require higher input derivatives and are not supplied.',
        'all_finite_CAR_source_mouth': 'Only the raw100 two-jet is accepted; the existing inverse positive half-density, actual residual section, all four original energies and all504 CAR modes generate the family and its four derivatives. These are number-preserving operators, not odd field ports or a selected physical state.',
        'ordering': 'The current H and the existing raw ambient ordering remain distinct. The same already signed current transport is used; no ambient-ordering correction is renamed a physical force.',
        'broken9_status': 'Original second-class relations remain on the input122 germ; only the original residual su(2) is used as a native quantum symmetry.',
        'secondary_zero_or_spatial_primary_preservation_claimed': False,
        'new_source_occurrence_pairing_or_clock': False,
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_temporal_lorentz_balance.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS source temporal Lorentz balance', out['seconds'], 'seconds', flush=True)

if __name__ == '__main__':
    main()
