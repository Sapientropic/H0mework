#!/usr/bin/env python3
"""The current common Hilbert Hamiltonian consumes the same full122 source jet.

The source scalar adjoint-form correction and both existing half-densities
are consumed before extending the input germ. This returns to the current
Gauss100/real504 Weyl operator, retaining the distinct ambient-ordering image.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_joint_quantum_section import SourceJointQuantumSection
from source_scalar_form_hamiltonian import SourceScalarFormHamiltonian
from source_joint_ccr_car_ports import SourceJointCCRCarPorts, same, simplified
from source_joint_current_heisenberg import patch_symbolic_equal
from source_scalar_weyl_symbol import quadratic_weyl_action
from source_common_weyl_symbol import coframe_action
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_joint_form_hamiltonian import read_bound
from source_lorentz_contact import equal, encode


class SourceJointCurrentHilbertSection:
    """Only source100 germ coefficients are inputs; all representation data are fixed."""
    def __init__(self):
        self.section = SourceJointQuantumSection()
        self.form = SourceScalarFormHamiltonian()
        m = self.section
        self.point = m.native.If.T*m.native.b0
        form = self.form.coefficients(m.spin.e, s.zeros(61, 1), m.gauge.A0)
        for name in ('momentum_vectors', 'normal_embedding', 'phi', 'shift'):
            equal(form[name], m.data['scalar'][name])
        assert form['h00'] == m.data['scalar']['h00']
        # All coefficients vanish here; derivatives away from the source are
        # not discarded and no statement at other configurations is inferred.
        for name in ('divergence', 'adjoint_derivative', 'adjoint_current'):
            assert not form[name].todok()
        assert form['adjoint_shift'] == 0
        self.rho_log_half_gradient = s.zeros(100, 1)
        self.rho_log_half_Hessian = s.zeros(100)
        for full_index, power in ((68, s.S.One), (79, s.Rational(1, 2))):
            j = m.native.free.index(full_index)
            self.rho_log_half_gradient[j] = power/self.point[j]
            self.rho_log_half_Hessian[j, j] = -power/self.point[j]**2

    def inverse_half_density_jet(self, value, gradient, Hessian):
        """Actual U(source) times U^-1 f, U_m=sqrt(rho3)*v^(1+m/2)."""
        gs, hs = {}, {}
        for word in set(value)|set(gradient)|set(Hessian):
            ell = self.rho_log_half_gradient.copy()
            logH = self.rho_log_half_Hessian.copy()
            alpha = s.Rational(len(word)+2, 2)
            for j in (0, 2, 5):
                ell[j] = alpha/self.point[j]
                logH[j, j] = -alpha/self.point[j]**2
            v = value.get(word, 0)
            g = gradient.get(word, s.zeros(100, 1))
            H = Hessian.get(word, s.zeros(100))
            gs[word] = g-ell*v
            hs[word] = H-ell*g.T-g*ell.T+(ell*ell.T-logH)*v
        return value.copy(), gs, hs

    def action(self, value, gradient, Hessian):
        """Generate the full122 germ and return the unchanged current H action."""
        native_germ = self.inverse_half_density_jet(value, gradient, Hessian)
        jet = self.section.extend_jet(*native_germ)
        returned = self.section.native_action_from_extended_jet(jet)
        return {'generated122_jet': jet, 'current_H_image': returned['native'],
            'ambient_image': returned['ambient'],
            'source_ordering_correction': returned['source_ordering_correction']}


def current_weyl_action(model, data, value, gradient, Hessian):
    """Direct action of the current production Weyl leaf, without this transport."""
    m = model.leaf.weyl
    pieces = {name: quadratic_weyl_action(data[name], value, gradient, Hessian,
        m.current_word, m.current) for name in ('scalar', 'gauge')}
    pieces['coframe'] = coframe_action(m,
        {'coframe': data['coframe'], 'e': data['matter']['e']},
        model.leaf.pairing, value, gradient, Hessian)
    pieces['matter_without_Lorentz'] = apply_superposition(data['matter']['matter_CAR'], value)
    return simplified({w: model.at_time(c)
        for w, c in weighted_sum((1, v) for v in pieces.values()).items()})


def main():
    began = time.monotonic()
    patch_symbolic_equal()
    bound = read_bound('source_joint_quantum_section')
    for name in ('source_scalar_form_hamiltonian', 'source_gauss_section_measure',
                 'source_reducing_coframe_metric', 'source_joint_ccr_car_ports'):
        read_bound(name)
    source = SourceJointCurrentHilbertSection()
    current = SourceJointCCRCarPorts()
    z = tuple(current.leaf.source_point[i] for i in current.leaf.free)
    equal(s.Matrix(z), source.point)
    data = current.coefficients(z)
    word = (5, 144, 396)
    value = {word: s.S.One}
    gradient = {word: s.Matrix([s.I*s.Rational(j % 7-3, 31) for j in range(100)])}
    u = s.Matrix([s.Rational(j % 5-2, 37) for j in range(100)])
    Hessian = {word: u*u.T-s.eye(100)}
    returned = source.action(value, gradient, Hessian)
    constraints = source.section.verify_constraints(returned['generated122_jet'])
    expected = current_weyl_action(current, data, value, gradient, Hessian)
    same(returned['current_H_image'], expected)
    assert expected and returned['source_ordering_correction']
    # A bound earlier-order image on exactly this germ detects omission of U.
    old = next(row for row in bound['actual_consumers'] if row['input_CAR'] == list(word))
    assert old['gradient100'] == encode(gradient[word])
    assert old['Hessian100']['rank_one_vector'] == encode(u)
    old_image = {tuple(w): s.sympify(v) for w, v in old['existing_native_H']}
    omission = simplified(weighted_sum(((1, expected), (-1, old_image))))
    assert omission
    paths = ['source_joint_current_hilbert_section.py', 'source_joint_quantum_section.py',
        'source_joint_quantum_section.json', 'source_scalar_form_hamiltonian.py',
        'source_scalar_form_hamiltonian.json', 'source_gauss_section_measure.py',
        'source_gauss_section_measure.json', 'source_reducing_coframe_metric.py',
        'source_reducing_coframe_metric.json', 'source_joint_ccr_car_ports.py',
        'source_joint_ccr_car_ports.json', 'source_common_weyl_symbol.py',
        'source_scalar_weyl_symbol.py', 'source_scalar_temporal_form.py']
    out = {'root': ROOT_ID, 'source_sha256': bound['source_sha256'],
        'input_sha256': {str((HERE/p).relative_to(ROOT)):
            hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in paths},
        'scope': 'SOURCE122_CONFIGURATION_RETURN_TO_CURRENT_FORM_HALF_DENSITY_WEYL_H',
        'source_configuration100': list(map(str, z)),
        'form_splice': 'The actual original scalar Pi-dagger Pi minus coefficient-left Pi Pi has zero divergence, adjoint derivative/current and shift coefficients at the exact source. This is an operator-coefficient equality here, not an expectation or off-source statement.',
        'half_density': 'U_m=sqrt(rho3)*v^(1+m/2), rho3=8 A1^2 A12, v=q0 q2 q5; the generated inverse two-jet retains both full logarithmic Hessians and their mixed gradient products.',
        'all_finite_CAR_germs': 'The source100-to122 extension, complete ordering-difference identity and vanishing source form correction are coefficient identities. Number preservation lets the original U_m act separately on every finite word; summing gives the same current operator on any finite CAR germ.',
        'actual_consumer': {'input_CAR': list(word), 'gradient100': encode(gradient[word]),
            'Hessian100': {'rank_one_vector': encode(u), 'identity_coefficient': '-1'},
            'generated122_CAR_words': len(returned['generated122_jet']),
            'original_configuration_constraint_checks': constraints,
            'direct_current_Weyl_H': encode_state(expected),
            'returned_current_H': encode_state(returned['current_H_image']),
            'ambient_order_image': encode_state(returned['ambient_image']),
            'source_ordering_correction': encode_state(returned['source_ordering_correction']),
            'omitting_actual_half_density_defect': encode_state(omission)},
        'direct_consumer': 'The current common Hamiltonian and its even bilinear current/force operators can now consume the full source122 configuration germ through the original positive-pairing normalization.',
        'full504_CAR_preserved': True, 'occupied12_projection_used': False,
        'new_H_pairing_state_or_source_occurrence_supplied': False,
        'physical_spacetime_Ward9_or_temporal_secondary_solution_claimed': False,
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_joint_current_hilbert_section.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS current common H through source122 jet:', len(expected),
          'output words;', out['seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
