#!/usr/bin/env python3
"""One source100 CAR germ generates the complete122 configuration two-jet.

The native12 orbit and the spatial Lorentz6 orbit commute, but their CAR
representations create genuine mixed two-jet terms. Broken9 retain their
original second-class meaning. The joint configuration identities are not
relabelled as spacetime Ward identities or temporal secondary solutions.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_lorentz_quantum_section import SourceLorentzQuantumSection, TIME
from source_full_gauss_section import SourceFullGaussSection
from source_quantum_gauss_section import SourceQuantumGaussSection
from source_coframe_live_ordering import full, FREE
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_joint_ccr_car_ports import simplified, same
from source_joint_form_hamiltonian import read_bound
from source_lorentz_contact import clean, equal, encode
from retained_hamiltonian_reduction import DOMAIN


class SourceJointQuantumSection:
    """Full coframe16, original scalar70 and spatial native connection36."""
    def __init__(self):
        self.spin = SourceLorentzQuantumSection()
        self.gauge = SourceFullGaussSection()
        self.native = SourceQuantumGaussSection()
        spin, gauge = self.spin, self.gauge
        for S in spin.R8:
            for R in gauge.R:
                equal(clean(full(S)*R-R*full(S)), s.zeros(504))
        self.retraction = s.zeros(112, 122)
        self.retraction[:6, :16] = spin.z*spin.Is.T
        self.retraction[6:, 16:] = s.eye(106)
        self.alpha = s.zeros(6, 122)
        self.alpha[:, :16] = spin.alpha*spin.Is.T
        self.second = []
        for H in spin.second:
            lifted = s.zeros(122)
            lifted[:16, :16] = spin.Is*H*spin.Is.T
            self.second.append(lifted)
        self.L, self.orbit = [], []
        self.R = spin.R+gauge.R
        for a in range(6):
            matrix = s.zeros(122)
            matrix[:16, :16] = spin.Is*spin.L[a]*spin.Is.T
            self.L.append(matrix)
            column = s.zeros(122, 1); column[:16, :] = spin.Is*spin.Z[:, a]
            self.orbit.append(column)
        for a in range(12):
            matrix = s.zeros(122); matrix[16:, 16:] = gauge.L[a][6:, 6:]
            self.L.append(matrix)
            column = s.zeros(122, 1); column[16:, :] = gauge.source.orbit[6:, a]
            self.orbit.append(column)
        self.section_embedding = s.zeros(122, 100)
        for j, i in enumerate(FREE):
            self.section_embedding[i, j] = 1
        self.section_embedding[16:, :] = gauge.embedding[6:, :]
        equal(gauge.source.z*self.retraction*self.section_embedding, s.eye(100))
        equal(self.alpha*self.section_embedding, s.zeros(6, 100))
        equal(gauge.source.alpha*self.retraction*self.section_embedding, s.zeros(12, 100))
        self.data = self.native.native.joint.coefficients(spin.q, s.zeros(61, 1), gauge.A0)
        assert not self.data['scalar']['shift'].todok()
        assert self.data['scalar']['spatial_potential'] == 0
        assert self.data['scalar']['h00'] == -1/spin.e[0, 0]
        assert not self.data['gauge']['momentum_shift'].todok()
        assert self.data['gauge']['derivative_ordering_constant'] == 0

    def _extend_spin(self, old, omit_mixed=False):
        D, a = self.retraction, self.alpha
        values = {w: row['value'] for w, row in old.items() if row['value']}
        result = {}
        def add(state, value=0, gradient=None, Hessian=None):
            for word, coefficient in state.items():
                row = result.setdefault(word, {'value': s.S.Zero,
                    'gradient': s.zeros(122, 1), 'Hessian': s.zeros(122)})
                row['value'] += coefficient*value
                if gradient is not None: row['gradient'] += coefficient*gradient
                if Hessian is not None: row['Hessian'] += coefficient*Hessian
        for word, row in old.items():
            dg = D.T*row['gradient']
            H = D.T*row['Hessian']*D+sum((row['gradient'][j]*self.second[6+j]
                for j in range(6)), s.zeros(122))
            add({word: 1}, row['value'], dg, H)
            if not omit_mixed:
                for j in range(6):
                    add(apply_superposition(self.spin.R[j], {word: 1}),
                        Hessian=a[j, :].T*dg.T+dg*a[j, :])
        for j in range(6):
            add(apply_superposition(self.spin.R[j], values),
                gradient=a[j, :].T, Hessian=self.second[j])
            for k in range(j, 6):
                jk = apply_superposition(self.spin.R[j], apply_superposition(self.spin.R[k], values))
                if j == k:
                    add(jk, Hessian=a[j, :].T*a[k, :])
                else:
                    kj = apply_superposition(self.spin.R[k], apply_superposition(self.spin.R[j], values))
                    add(weighted_sum(((s.Rational(1, 2), jk), (s.Rational(1, 2), kj))),
                        Hessian=a[j, :].T*a[k, :]+a[k, :].T*a[j, :])
        for row in result.values():
            row['value'] = s.expand(row['value'])
            row['gradient'] = clean(row['gradient'])
            row['Hessian'] = clean(row['Hessian'])
        return result

    def extend_jet(self, value, gradient, Hessian):
        """No Gauss, Lorentz or completed122 jet is accepted as an input."""
        return self._extend_spin(self.gauge.extend_jet(value, gradient, Hessian))

    def constraint_defects(self, jet):
        """Original6 Spin-primary and native12 configuration moment maps."""
        values = {w: row['value'] for w, row in jet.items() if row['value']}
        result = []
        for a in range(18):
            first = {w: -s.I*(self.orbit[a].T*row['gradient'])[0] for w, row in jet.items()}
            value = simplified(weighted_sum(((1, first),
                (s.I, apply_superposition(self.R[a], values)))))
            derivatives = {w: clean(-s.I*(self.L[a].T*row['gradient']+
                row['Hessian']*self.orbit[a])) for w, row in jet.items()}
            for word, row in jet.items():
                for out, coefficient in apply_superposition(self.R[a], {word: 1}).items():
                    derivatives.setdefault(out, s.zeros(122, 1))
                    derivatives[out] += s.I*coefficient*row['gradient']
            derivatives = {w: clean(M) for w, M in derivatives.items() if clean(M).todok()}
            result.append({'value': value, 'derivative': derivatives})
        return result

    def verify_constraints(self, jet):
        defects = self.constraint_defects(jet)
        assert all(not row['value'] and not row['derivative'] for row in defects)
        for row in jet.values():
            equal(row['gradient'].extract(TIME, [0]), s.zeros(4, 1))
            equal(row['Hessian'].extract(TIME, range(122)), s.zeros(4, 122))
        return {'original18_configuration_constraints_zero': True,
            'all2196_configuration_derivatives_zero': True,
            'original_four_temporal_primary_zero': True}

    def complete_ordering_difference(self):
        """All100 differential/CAR coefficients at the original source point."""
        if hasattr(self, '_ordering_drift'):
            return self._ordering_drift
        chart, old = self.gauge.source, self.native
        scalar = old.native.joint.scalar; data = self.data['scalar']
        h00 = data['h00']
        def full_trace(weights):
            out = s.zeros(112, 1)
            for row, entries in chart.inverse_second.rep.items():
                value = DOMAIN.zero
                for (i, j), weight in weights.items():
                    if weight and (coefficient := entries.get(112*i+j)):
                        value += DOMAIN.from_sympy(weight)*coefficient
                out[row] = DOMAIN.to_sympy(value)
            return clean(out)
        def trace(H, W):
            return s.expand(sum(v*H[i, j] for (i, j), v in W.todok().items()))
        A = s.zeros(103, 70); OF = data['normal_embedding']
        derivative = s.zeros(103, 1); dOF = s.zeros(9, 1)
        for j in range(70):
            aj = data['momentum_vectors'][j, :].T
            dj = scalar.directional_momentum(data, aj)
            A[6:, j] = aj
            derivative[6:, :] += dj['momentum_vectors'][j, :].T
            dOF += dj['normal_embedding'][j, :].T
        G = clean(A*A.T)
        ao, zo = old.alpha*A, old.z*A
        af, zf = chart.alpha[:, 6:76], chart.z[:, 6:76]
        equal(clean(zf-zo), s.zeros(100, 70))
        equal(clean(af-OF.T.col_join(ao)), s.zeros(12, 70))
        for a in range(3):
            equal(self.gauge.R[9+a], old.R[a])
        traced = full_trace({(j, j): s.S.One for j in range(6, 76)})
        ztrace = s.Matrix([trace(H, G) for H in old.z2])+old.z*derivative
        atrace = s.Matrix([trace(H, G) for H in old.alpha2])+old.alpha*derivative
        central = clean((ztrace-traced[12:, :])/(2*h00))
        body = clean((dOF.col_join(atrace)-traced[:12, :])/(2*h00))
        ordered = s.zeros(12)
        ordered[:9, :9] = -OF.T*OF
        ordered[:9, 9:] = -2*OF.T*ao.T
        ordered[9:, 9:] = -ao*ao.T
        tensor = clean((-af*af.T-ordered)/(2*h00))
        equal(clean(tensor+tensor.T), s.zeros(12))
        # Antisymmetric ordered pairs leave the original Lie commutator;
        # their normal products cancel on every CAR occupation.
        for a in range(12):
            for b in range(a+1, 12):
                if tensor[a, b]:
                    structure = self.gauge.structure[a][:, b]
                    equal(clean(self.gauge.R[a]*self.gauge.R[b]-
                        self.gauge.R[b]*self.gauge.R[a]),
                        clean(sum((v*R for v, R in zip(structure, self.gauge.R)), s.zeros(504))))
                    body += tensor[a, b]*structure
        equal(clean(body), s.zeros(12, 1))
        W = self.data['gauge']['weight']
        gt = full_trace({(76+i, 76+j): v for (i, j), v in W.todok().items()})
        gsmall = s.zeros(103); gsmall[67:, 67:] = W
        gz = s.Matrix([trace(H, gsmall) for H in old.z2])
        ga = s.Matrix([trace(H, gsmall) for H in old.alpha2])
        equal(clean(gt[12:, :]-gz), s.zeros(100, 1))
        equal(clean(gt[:9, :]), s.zeros(9, 1))
        equal(clean(gt[9:12, :]-ga), s.zeros(3, 1))
        equal(chart.z[:, 76:], old.z[:, 67:])
        equal(chart.alpha[9:, 76:], old.alpha[:, 67:])
        equal(chart.alpha[:9, 76:], s.zeros(9, 36))
        central[:6, :] += self.spin.complete_ordering_difference()
        self._ordering_drift = central
        return central

    def ambient_action(self, jet):
        """The original four energies before the two configuration reductions."""
        cf = self.spin.ambient_action({w: {'value': row['value'],
            'gradient': row['gradient'][:16, :], 'Hessian': row['Hessian'][:16, :16]}
            for w, row in jet.items()})
        N = self.spin.e[0, 0]
        scalar = {w: s.expand(N*sum(row['Hessian'][16+i, 16+i]
            for i in range(70))/2) for w, row in jet.items()}
        gauge_data = self.data['gauge']; W = gauge_data['weight']
        gauge = {w: s.expand(-sum(v*row['Hessian'][86+i, 86+j]
            for (i, j), v in W.todok().items())/2+
            gauge_data['magnetic_potential']*row['value']) for w, row in jet.items()}
        values = {w: row['value'] for w, row in jet.items() if row['value']}
        matter = apply_superposition(self.data['matter_CAR'], values)
        parts = {'coframe': cf, 'scalar': simplified(scalar),
            'gauge': simplified(gauge), 'matter_without_Lorentz': simplified(matter)}
        return parts, simplified(weighted_sum((1, result) for result in parts.values()))

    def native_action_from_extended_jet(self, jet):
        """Read the unchanged native H through the generated full122 germ.

        The coefficient identity pays the explicit ordering correction; no
        positive-pairing equivalence or full-configuration claim is inserted.
        """
        parts, ambient = self.ambient_action(jet)
        drift = self.complete_ordering_difference()
        pulled_gradient = {word: self.section_embedding.T*row['gradient']
                           for word, row in jet.items()}
        correction = simplified({word: (drift.T*gradient)[0]
                                 for word, gradient in pulled_gradient.items()})
        native = simplified(weighted_sum(((1, ambient), (-1, correction))))
        return {'ambient_components': parts, 'ambient': ambient,
            'source_ordering_correction': correction, 'native': native}

    def existing_native_action(self, value, gradient, Hessian):
        """Retain the old reduce-first source ordering as its own operator."""
        old = self.native.extend_jet(value, gradient, Hessian)
        self.native.verify_Gauss_jet(old)
        return self.native.Hamiltonian_action(old)


def main():
    began = time.monotonic()
    bound = read_bound('source_lorentz_quantum_section')
    read_bound('source_full_gauss_section')
    m = SourceJointQuantumSection()
    drift = m.complete_ordering_difference()
    reports = []
    for word in ((16, 268), (5, 144, 396)):
        value = {word: s.S.One}
        gradient = {word: s.Matrix([s.I*s.Rational(j % 7-3, 31) for j in range(100)])}
        u = s.Matrix([s.Rational(j % 5-2, 37) for j in range(100)])
        Hessian = {word: u*u.T-s.eye(100)}
        middle = m.gauge.extend_jet(value, gradient, Hessian)
        m.gauge.verify_Gauss_jet(middle)
        jet = m._extend_spin(middle)
        constraints = m.verify_constraints(jet)
        assert all(len(w) == len(word) for w in jet)
        returned = m.native_action_from_extended_jet(jet)
        parts, ambient = returned['ambient_components'], returned['ambient']
        old_parts, old = m.existing_native_action(value, gradient, Hessian)
        difference = simplified(weighted_sum(((1, ambient), (-1, old))))
        same(returned['native'], old)
        same(difference, {word: (drift.T*gradient[word])[0]})
        assert difference
        omitted = m.constraint_defects(m._extend_spin(middle, omit_mixed=True))
        counts = [sum(len(M.todok()) for M in row['derivative'].values()) for row in omitted]
        assert any(counts)
        mixed = sum(sum(bool(row['Hessian'][i, j]) for i in range(16) for j in range(16, 122))
                    for row in jet.values())
        reports.append({'input_CAR': list(word), 'jet_CAR_words': len(jet),
            'gradient100': encode(gradient[word]),
            'Hessian100': {'rank_one_vector': encode(u), 'identity_coefficient': '-1', 'formula': 'u*u^T-I100'},
            'mixed_coframe_native_Hessian_entries': mixed, 'constraint_checks': constraints,
            'all_CAR_outputs_preserve_input_number': True,
            'ambient_components': {k: encode_state(v) for k, v in parts.items()},
            'existing_native_components': {k: encode_state(v) for k, v in old_parts.items()},
            'ambient_H': encode_state(ambient), 'existing_native_H': encode_state(old),
            'actual_ambient_minus_existing': encode_state(difference),
            'same_native_H_from_complete122_jet': encode_state(returned['native']),
            'source_ordering_correction': encode_state(returned['source_ordering_correction']),
            'omitted_mixed_derivative_defect_counts': counts})
        print('PASS source joint122 jet and four energies:', word, 'mixed', mixed,
              'omitted defects', sum(counts), flush=True)
    paths = ['source_joint_quantum_section.py', 'source_lorentz_quantum_section.py',
        'source_lorentz_quantum_section.json', 'source_full_gauss_section.py',
        'source_full_gauss_section.json', 'source_quantum_gauss_section.py',
        'source_quantum_stabilizer.py', 'source_joint_local_quantum.py',
        'source_scalar_legendre.py', 'source_gauge_quantum_energy.py']
    out = {'root': ROOT_ID, 'source_sha256': bound['source_sha256'],
        'input_sha256': {str((HERE/p).relative_to(ROOT)):
            hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in paths},
        'scope': 'COMMON122_CONFIGURATION_JET_FROM_ORIGINAL100_GERM_AND_FULL504_CAR',
        'configuration_order': ['coframe16', 'scalar70', 'spatial_gauge36'],
        'input_order': ['coframe6', 'scalar61', 'spatial_gauge33'],
        'generator_order': ['Lorentz6', 'native_broken9', 'native_residual_su2_3'],
        'source_group_factorization': 'Original spin8 tensor I63 commutes with all12 original native real504 matrices; all72 full matrix identities are checked before the joint extension.',
        'mixed_twojet': 'The chain rule retains the mixed Lorentz/native CAR products and both configuration legs. No commuting-group shortcut deletes these Hessian entries.',
        'four_time_columns': 'Original time parameters retain their identities; these germs have zero time-parameter derivative and satisfy the four temporal primary momenta. Temporal secondary forces are not assigned values.',
        'full504_CAR_and_all63_internal_entries_retained': True,
        'occupied_matter_projection_used': False,
        'native_broken9_second_class_meaning_retained': True,
        'native_full12_first_class_physical_symmetry_claimed': False,
        'complete_operator_difference': {'central_drift100': encode(drift),
            'all70_original_momentum_principal_and_current_coefficients_equal': True,
            'native12_symmetric_normal_pair_tensor_zero': True,
            'actual_native_Lie_commutators_cancel_the_remaining_onebody': True,
            'all_gauge36_inverse_jet_contractions_equal': True,
            'complete_coframe_spin8_tensor_identity63_consumed': True,
            'identity': 'ambient_H(extended_germ)-existing_native_H(germ)=drift100.dot(gradient100), for every finite CAR germ at the exact source point'},
        'same_native_H_transport': {'API': 'native_action_from_extended_jet',
            'section_embedding122_by100': encode(m.section_embedding),
            'formula': 'Hnative f=Hambient(extend f)-drift100.dot(section_embedding^T gradient(extend f)) at the source',
            'old_native_H_preserved': True, 'new_physical_H_or_pairing_claimed': False},
        'actual_consumers': reports,
        'operator_scope': 'Both ambient-before-reduction and existing reduce-first coefficient-left four-energy actions are evaluated on their generated configuration germs. Their actual differences are retained; no equivalence of positive pairings or replacement of the common native Hamiltonian is asserted.',
        'direct_consumer': 'Full configuration jets for original differential Hamiltonian, bilinear current and force readbacks, including both coefficient and CAR derivatives.',
        'physical_spacetime_Ward9_or_interacting_spectrum_claimed': False,
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_joint_quantum_section.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS joint source122 configuration producer', out['seconds'], flush=True)


if __name__ == '__main__':
    main()
