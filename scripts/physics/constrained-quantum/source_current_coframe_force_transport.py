#!/usr/bin/env python3
"""Current q-forces from the actual fixed-Pi coforces and source jet chain.

The differentiated input is the original inverse chart and positive pairing,
not a supplied horizontal derivative of Hf. All six reduced momentum carriers
stay distinct from the full ambient canonical Pi until the chain is consumed.
"""
from __future__ import annotations
import copy
from functools import lru_cache
import hashlib
import json
import time
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from source_joint_current_hilbert_section import SourceJointCurrentHilbertSection
from source_common_temporal_form import SourceCommonTemporalForm
from source_full_coframe_quantum_force import SourceFullCoframeQuantumForce
from source_coframe_live_ordering import FREE
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode
from source_gauss_quantum_current import weighted_sum, encode_state
from source_joint_ccr_car_ports import simplified, same
from source_joint_form_hamiltonian import read_bound
from source_full_gauss_section import DOMAIN
from source_quantum_temporal_symbol import N


class SourceCurrentCoframeForceTransport:
    def __init__(self):
        self.current = SourceJointCurrentHilbertSection()
        self.section = self.current.section
        self.spin, self.native = self.section.spin, self.section.native
        self.common = SourceCommonTemporalForm()
        self.raw = SourceFullCoframeQuantumForce()
        self.scalar_gap = self.section.complete_ordering_difference().copy()
        self.scalar_gap[:6, :] = s.zeros(6, 1)
        self._verify_uncontracted_gauge_inverse()
        for model in (self.section.gauge, self.native):
            for L in model.L:
                equal(L[:, :6], s.zeros(L.rows, 6)); equal(L[:6, :], s.zeros(6, L.cols))

    def _verify_uncontracted_gauge_inverse(self):
        """Every inverse second coefficient, before any coframe-dependent W."""
        chart = self.section.gauge.source; old = self.native
        equal(chart.z[:, 76:], old.z[:, 67:])
        equal(chart.alpha[:9, 76:], s.zeros(9, 36))
        equal(chart.alpha[9:, 76:], old.alpha[:, 67:])
        sparse = chart.inverse_second.rep
        nonzero = 0
        for row in range(112):
            actual = {((col//112)-76, (col % 112)-76): c
                for col, c in sparse.get(row, {}).items()
                if col//112 >= 76 and col % 112 >= 76 and c}
            H = None if row < 9 else old.alpha2[row-9] if row < 12 else old.z2[row-12]
            expected = {} if H is None else {(i-67, j-67): DOMAIN.from_sympy(c)
                for (i, j), c in H.todok().items() if i >= 67 and j >= 67 and c}
            assert actual == expected, row
            nonzero += len(actual)
        self.gauge_inverse_entries = nonzero

    @lru_cache(None)
    def _chart_curve(self, axis):
        m = copy.copy(self.spin)
        variable = s.Dummy('source_q_'+str(axis), positive=True) if axis in (0, 2, 5) else s.Dummy('source_q_'+str(axis), real=True)
        m.e = self.spin.e.copy(); m.e[FREE[axis]] = variable
        m.q = tuple(m.e[i] for i in FREE)
        m.data = m.model.coefficients(m.q)
        point = m.Is.T*m.e.reshape(16, 1)
        m.Z = rational(s.Matrix.hstack(*(L*point for L in m.L)))
        m.minor = m.Cp*m.Z
        m.alpha = rational(m.minor.inv()*m.Cp)
        m.z = rational(m.If.T*(s.eye(12)-m.Z*m.alpha))
        m.forward = m.Z.row_join(m.If); m.inverse = m.alpha.col_join(m.z)
        equal(rational(m.forward*m.inverse), s.eye(12))
        curvature = [s.zeros(12) for _ in range(12)]
        for a in range(6):
            mixed = m.L[a]*m.If*m.z
            for k in range(12):
                curvature[k] += m.alpha[a, :].T*mixed[k, :]+mixed[k, :].T*m.alpha[a, :]
            for b in range(a, 6):
                acceleration = (m.L[a]*m.L[b]+m.L[b]*m.L[a])*point/2
                outer = m.alpha[a, :].T*m.alpha[b, :]
                if a != b: outer += m.alpha[b, :].T*m.alpha[a, :]
                for k in range(12): curvature[k] += acceleration[k]*outer
        m.second = [rational(-sum((m.inverse[i, k]*curvature[k] for k in range(12)), s.zeros(12))) for i in range(12)]
        for k in range(12):
            equal(rational(sum((m.forward[k, i]*m.second[i] for i in range(12)), s.zeros(12))+curvature[k]), s.zeros(12))
        m._ambient_coefficients()
        return variable, m

    @lru_cache(None)
    def _curve_coefficients(self, axis):
        variable, chart = self._chart_curve(axis)
        cf_drift = chart.complete_ordering_difference()
        data = self.common.coefficients((N, 0, 0, 0), chart.q, s.zeros(61, 1), self.section.gauge.A0)
        for key in ('momentum_vectors', 'normal_embedding'):
            equal(data['scalar'][key], self.section.data['scalar'][key])
        for key in ('divergence', 'adjoint_derivative', 'adjoint_current', 'shift'):
            assert not data['scalar'][key].todok()
        assert data['scalar']['adjoint_shift'] == 0
        ratio = s.cancel(self.section.data['scalar']['h00']/data['scalar']['h00'])
        return cf_drift, data, ratio

    def _pairing_jet(self, q, value, gradient, Hessian):
        gs, hs = {}, {}
        for word in set(value)|set(gradient)|set(Hessian):
            ell = self.current.rho_log_half_gradient.copy()
            logH = self.current.rho_log_half_Hessian.copy()
            alpha = s.Rational(len(word)+2, 2)
            for j in (0, 2, 5): ell[j], logH[j, j] = alpha/q[j], -alpha/q[j]**2
            f, g, H = value.get(word, 0), gradient.get(word, s.zeros(100, 1)), Hessian.get(word, s.zeros(100))
            gs[word] = g-ell*f
            hs[word] = H-ell*g.T-g*ell.T+(ell*ell.T-logH)*f
        return value.copy(), gs, hs

    def generate(self, value, gradient, Hessian):
        source_germ = self.current.inverse_half_density_jet(value, gradient, Hessian)
        source122 = self.section.extend_jet(*source_germ)
        raw = [self.raw.apply(axis, source122) for axis in FREE]
        rows = []
        for axis in range(6):
            variable, chart = self._chart_curve(axis)
            at = {variable: self.spin.q[axis]}
            germ = self._pairing_jet(chart.q, value, gradient, Hessian)
            qg = {w: g[:6, :] for w, g in germ[1].items()}
            qH = {w: H[:6, :6] for w, H in germ[2].items()}
            jet16 = chart.extend_jet(germ[0], qg, qH)
            changing = {w: {'value': s.diff(row['value'], variable).subs(at),
                'gradient': rational(row['gradient'].diff(variable).subs(at)),
                'Hessian': rational(row['Hessian'].diff(variable).subs(at))} for w, row in jet16.items()}
            connection = self.spin.ambient_action(changing)
            cf_drift, data, ratio = self._curve_coefficients(axis)
            gap = {w: (cf_drift.T*germ[1][w][:6, :])[0]+ratio*(self.scalar_gap.T*germ[1][w])[0]
                for w in set(germ[0])|set(germ[1])}
            dgap = simplified({w: s.diff(c, variable).subs(at) for w, c in gap.items()})
            transported = simplified(weighted_sum(((1, raw[axis]), (-1, connection), (1, dgap))))
            native103 = self.common.section.extend_jet(*germ)
            direct = self.common.action(data, native103)['H']
            direct = {w: c.xreplace({a: variable for a in c.free_symbols
                if str(a) == str(variable) or str(a) == variable.name}) for w, c in direct.items()}
            current_force = simplified({w: -s.diff(c, variable).subs(at) for w, c in direct.items()})
            same(transported, current_force)
            rows.append({'q_axis': axis, 'ambient_e_axis': FREE[axis], 'fixed_Pi_force': raw[axis],
                'inverse_jet_and_half_density_chain': connection, 'source_ordering_gap_derivative': dgap,
                'current_q_force': current_force, 'transported_current_q_force': transported,
                'all_q_curve_coframe_drift': cf_drift, 'scalar_original_h00_ratio': ratio})
        return {'source122_jet': source122, 'q_forces': rows}


def main():
    began = time.monotonic()
    bound = read_bound('source_full_coframe_quantum_force')
    for name in ('source_joint_current_hilbert_section', 'source_lorentz_temporal_ordering'):
        read_bound(name)
    model = SourceCurrentCoframeForceTransport()
    word = (5, 144, 396); value = {word: s.S.One}
    gradient = {word: s.Matrix([s.I*s.Rational(j % 7-3, 31) for j in range(100)])}
    u = s.Matrix([s.Rational(j % 5-2, 37) for j in range(100)])
    Hessian = {word: u*u.T-s.eye(100)}
    result = model.generate(value, gradient, Hessian)
    assert all(row['inverse_jet_and_half_density_chain'] for row in result['q_forces'])
    print('PASS original N3 six-force consumer and nonzero chain controls', flush=True)
    cases = []
    old_forces = [{tuple(w): s.sympify(c) for w, c in row}
        for row in bound['actual_consumer']['all16_raw_forces_in_source_pairing']]
    for row in result['q_forces']:
        same(row['fixed_Pi_force'], old_forces[row['ambient_e_axis']])
        cases.append({k: encode(v) if isinstance(v, s.MatrixBase)
            else encode_state(v) if isinstance(v, dict) else str(v) if isinstance(v, s.Basic) else v
            for k, v in row.items()})
    zero_word = (16, 268)
    zero = model.generate({zero_word: s.S.Zero}, {zero_word: s.zeros(100, 1)}, {zero_word: s.zeros(100)})
    assert all(not row[key] for row in zero['q_forces'] for key in ('fixed_Pi_force',
        'inverse_jet_and_half_density_chain', 'source_ordering_gap_derivative',
        'current_q_force', 'transported_current_q_force'))
    assert all(row['value'] == 0 and not row['gradient'].todok() and not row['Hessian'].todok()
        for row in zero['source122_jet'].values())
    print('PASS zero germ through the same public force producer', flush=True)
    mixed_value = {(): s.Rational(2, 3), zero_word: s.I/7}
    mixed_gradient = {(): s.SparseMatrix(100, 1, {(0, 0): s.Rational(1, 11),
        (9, 0): -s.Rational(1, 13), (74, 0): s.I/17}),
        zero_word: s.SparseMatrix(100, 1, {(5, 0): s.I/19, (7, 0): s.Rational(1, 23), (95, 0): -s.Rational(2, 29)}),
        (5,): s.SparseMatrix(100, 1, {(1, 0): s.Rational(1, 31), (97, 0): s.I/37})}
    mixed_Hessian = {(): s.SparseMatrix(100, 100, {(0, 0): s.Rational(1, 41), (7, 7): s.Rational(1, 43)}),
        zero_word: s.SparseMatrix(100, 100, {(5, 5): s.Rational(3, 47),
            (7, 84): s.Rational(1, 53), (84, 7): s.Rational(1, 53)}),
        (5,): s.SparseMatrix(100, 100, {(0, 5): s.I/59, (5, 0): s.I/59})}
    mixed = model.generate(mixed_value, mixed_gradient, mixed_Hessian)
    assert {len(w) for row in mixed['q_forces'] for w in row['current_q_force']} == {0, 1, 2}
    mixed_rows = [{k: encode_state(row[k]) for k in ('fixed_Pi_force',
        'inverse_jet_and_half_density_chain', 'source_ordering_gap_derivative', 'current_q_force')}
        for row in mixed['q_forces']]
    print('PASS cross-branch mixed N0/N2 and zero-valued N1 derivative germ', flush=True)
    paths = ('source_current_coframe_force_transport.py', 'source_full_coframe_quantum_force.py',
        'source_full_coframe_quantum_force.json', 'source_joint_current_hilbert_section.py',
        'source_joint_current_hilbert_section.json', 'source_lorentz_quantum_section.py',
        'source_joint_quantum_section.py', 'source_common_temporal_form.py', 'source_full_gauss_section.py')
    out = {'root': ROOT_ID, 'scope': 'SOURCE_INVERSE_JET_CHAIN_RETURNS_ALL6_FIXED_REDUCED_CURRENT_COFORCES',
        'source_sha256': bound['source_sha256'],
        'input_sha256': {str((HERE/p).relative_to(ROOT)): hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in paths},
        'source_mouth': 'SourceCurrentCoframeForceTransport.generate(raw100 two-jet) independently generates the original122 germ, fixed-Pi raw forces, differentiated source inverse jets and pairing, and all ordering-gap derivatives. No Hf derivative, target force or constraint solution is supplied.',
        'force_identity': 'Fcurrent_q = Fraw_eFREE - Hraw_cf(partial_q Phi) + partial_q Delta_current, with fixed reduced momentum on the current side and fixed ambient Pi on the raw side.',
        'gauge_uncontracted_inverse': {'all112_by36_by36_entries_checked': True,
            'nonzero_entries': model.gauge_inverse_entries,
            'broken9_rows_zero_and_native103_residual_rows_identical': True,
            'q_independence': 'All native generators annihilate the six coframe coordinates; the first and second native inverse jets therefore remain independent of q. The checked gauge identity is consumed before inserting any original coframe/time weight.'},
        'scalar_gap': 'The unchanged original scalar momentum graph and vanishing source adjoint-form correction are checked on each actual q curve. Its difference is multiplied by the original h00_source/h00(q), rather than copied from the source value.',
        'actual_consumer': {'word': list(word), 'generated122_words': len(result['source122_jet']), 'all6_current_force_returns': cases},
        'zero_consumer': 'The zero-valued N2 word with zero gradient/Hessian traverses the same public producer and all five outputs vanish in every direction.',
        'mixed_N_consumer': {'values': encode_state(mixed_value),
            'gradients100': [[list(w), encode(g)] for w, g in mixed_gradient.items()],
            'Hessians100': [[list(w), encode(H)] for w, H in mixed_Hessian.items()],
            'all6_force_returns': mixed_rows, 'output_numbers': [0, 1, 2]},
        'scope_boundary': 'These are coefficient derivatives of the same current Hamiltonian on the source six-coordinate slice. The inverse two-jet is differentiated, generating its needed third derivatives. No completed horizontal output jet Hf or new physical state is selected.',
        'physical_Ward9_or_retarded289_feed_claimed': False,
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_current_coframe_force_transport.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS complete current coframe force transport', out['seconds'], 'seconds', flush=True)

if __name__ == '__main__': main()
