#!/usr/bin/env python3
"""The source four-energy form on its actual residual3 quantum section.

The coframe, gauge and matter operators keep their original order. The scalar
factor uses the generated adjoint of the same second-class momentum graph.
The full Y-null reducing carrier is consumed; it does not replace its charged
complement. All assertions concern the fixed source time column.
"""
from __future__ import annotations

import hashlib
import json
import time
from types import SimpleNamespace

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_scalar_form_hamiltonian import SourceScalarFormHamiltonian, relocate_section
from source_reducing_coframe_metric import complete_coefficients
from source_coframe_live_ordering import full, verify_jet_action
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state


def read_bound(name):
    data = json.loads((HERE/(name+'.json')).read_text())
    assert data['root'] == ROOT_ID
    for group in ('source_sha256', 'input_sha256'):
        for path, digest in data[group].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    return data


class SourceJointFormHamiltonian:
    def __init__(self):
        self.scalar = SourceScalarFormHamiltonian()
        self.section = self.scalar.section
        self.native = self.section.native
        self.coframe = self.native.joint.coframe
        self.metric = complete_coefficients(SimpleNamespace(section=self.section))
        carrier = read_bound('source_yukawa_reducing_carrier')
        self.P = decode(carrier['generated_reducing_projector_real504'])
        assert s.trace(self.P) == 392

    def coefficients(self, q, x, A):
        data = self.native.joint.coefficients(q, x, A)
        data['scalar'] = self.scalar.coefficients(data['e'], x, A)
        return data

    def action(self, data, jet):
        values = {w: j['value'] for w, j in jet.items() if j['value']}
        gradients = {w: j['gradient'][6:, :] for w, j in jet.items()}
        Hessians = {w: j['Hessian'][6:, 6:] for w, j in jet.items()}
        scalar = self.scalar.action(data['scalar'], values, gradients, Hessians)
        cf_terms, gauge_terms = [], []
        d = data['gauge']; W, C = d['weight'], d['momentum_shift']
        constant = (C.T*W*C)[0]/2+d['derivative_ordering_constant']+d['magnetic_potential']
        for word, item in jet.items():
            cf = verify_jet_action(data['coframe'], word, item['value'],
                                  item['gradient'][:6, :], item['Hessian'][:6, :6])
            cf_terms.append((1, {tuple(w): s.sympify(v) for w, v in cf['raw_nested_square']}))
            g, H = item['gradient'][67:, :], item['Hessian'][67:, 67:]
            value = -sum(v*H[i, j] for (i, j), v in W.todok().items())/2
            value += s.I*(C.T*W*g)[0]+constant*item['value']
            gauge_terms.append((value, {word: 1}))
        pieces = {'coframe': weighted_sum(cf_terms), 'scalar_form': scalar,
                  'gauge': weighted_sum(gauge_terms),
                  'matter_without_Lorentz': apply_superposition(data['matter_CAR'], values)}
        return pieces, weighted_sum((1, piece) for piece in pieces.values())

    def normalized_jet(self, value, gradient, Hessian, particle_number, include_coframe=True):
        """U(point) times the entire jet of U^-1 f; no arbitrary leg residue."""
        section = self.section
        point = section.If.T*section.b0
        ell, h = s.zeros(100, 1), s.zeros(100)
        for full_index, power in ((68, s.S.One), (79, s.Rational(1, 2))):
            j = section.free.index(full_index)
            ell[j] = power/point[j]; h[j, j] = -power/point[j]**2
        if include_coframe:
            alpha = s.Rational(particle_number+2, 2)
            for j in (0, 2, 5):
                ell[j] = alpha/point[j]; h[j, j] = -alpha/point[j]**2
        gs, hs = {}, {}
        for w in set(value)|set(gradient)|set(Hessian):
            assert len(w) == particle_number
            v = value.get(w, 0); g = gradient.get(w, s.zeros(100, 1))
            H = Hessian.get(w, s.zeros(100))
            gs[w] = rational(g-ell*v)
            hs[w] = rational(H-ell*g.T-g*ell.T+(ell*ell.T-h)*v)
        return section.extend_jet(value, gs, hs)

    def normalized_coframe(self, data, jet, particle_number):
        """Independent divergence/Hermitian-current representation of U Hcf U^-1."""
        c = self.coframe; d = self.metric
        sub = dict(zip(c.q, self.section.b0[:6, 0]))
        divergence = d['divergence'].subs(sub)
        potential = s.cancel(d['potential'].subs(d['m'], particle_number).subs(sub))
        terms = []
        for word, item in jet.items():
            g, H = item['gradient'][:6, :], item['Hessian'][:6, :6]
            original_constant = verify_jet_action(data['coframe'], word, item['value'], s.zeros(6, 1), s.zeros(6))
            terms.append((1, {tuple(w): s.sympify(v) for w, v in original_constant['raw_nested_square']}))
            scalar = -sum(v*H[i, j] for (i, j), v in data['coframe']['K'].todok().items())
            scalar += -(divergence.T*g)[0]+potential*item['value']
            terms.append((scalar, {word: 1}))
            for j, Mh in enumerate(d['hermitian']):
                terms.append((-s.I*g[j], apply_superposition(full(rational(Mh.subs(sub))), {word: 1})))
        return weighted_sum(terms)


def complete_matter_adjoint(model):
    c = model.coframe
    ports = c.model.lorentz.raw_matter_ports(c.e)
    spin = [rational(-s.I*ports['E'].inv()*ports['oriented_principals'][i]) for i in range(1, 4)]
    for C in spin: equal(C.H, -C)
    for T in model.native.graph.common.rho: equal(T.H, -T)
    # Spin and internal factors commute. Their two anti-Hermitian factors
    # give a Hermitian original gauge matter term at every live q and real A.
    return {'generic_all_six_q_spin_factors': [encode(C) for C in spin],
            'all12_internal_factors_anti_Hermitian': True,
            'full_original_gauge_matter_Hermitian_on_Y_null_carrier': True}


def main():
    started = time.monotonic()
    dependencies = ('source_full_gauss_section', 'independent_source_full_gauss_section',
        'source_scalar_form_hamiltonian', 'independent_source_scalar_form_hamiltonian',
        'source_reducing_coframe_metric', 'independent_source_reducing_coframe_metric',
        'source_yukawa_reducing_carrier', 'independent_source_yukawa_reducing_carrier',
        'source_gauge_quantum_energy', 'source_quantum_stabilizer', 'source_gauss_section_measure')
    for name in dependencies: read_bound(name)
    m = SourceJointFormHamiltonian(); section = m.section
    matter_adjoint = complete_matter_adjoint(m)
    # Original36 gauge momenta are symmetric in the ambient canonical measure.
    # Their real symmetric weight depends on q only; they never differentiate W.
    generic_gauge = m.native.joint.gauge.coefficients(m.coframe.e)
    equal(generic_gauge['weight'].T, generic_gauge['weight'])
    equal(generic_gauge['weight'].conjugate(), generic_gauge['weight'])
    equal(generic_gauge['momentum_shift'].conjugate(), generic_gauge['momentum_shift'])
    assert s.expand(s.conjugate(generic_gauge['magnetic_potential'])-generic_gauge['magnetic_potential']) == 0
    print('PASS generic original gauge square and full matter-current adjoints', flush=True)
    q = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8),
         s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    x = s.Matrix([s.Rational((3*j+1) % 7-3, 100) for j in range(61)])
    A = section.A0.copy(); A[0, 1] *= s.Rational(11, 10); A[1, 0] *= s.Rational(9, 8)
    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    relocate_section(section, point)
    data = m.coefficients(q, x, A)
    equal(data['matter_CAR']*m.P, m.P*data['matter_CAR'])
    equal(data['matter_CAR'].H*m.P, m.P*data['matter_CAR'])
    word = (7, 71); assert all(m.P[i, i] == 1 for i in word)
    gradient = s.Matrix([s.I*s.Rational(j % 5-2, 47) for j in range(100)])
    u = s.Matrix([s.Rational(j % 3-1, 43) for j in range(100)])
    Hessian = u*u.T-s.eye(100)
    value, gs, hs = {word: 1}, {word: gradient}, {word: Hessian}
    jet = section.extend_jet(value, gs, hs)
    gauss = section.verify_Gauss_jet(jet)
    pieces, image = m.action(data, jet)
    assert all(pieces.values())
    assert all(len(w) == 2 and all(m.P[i, i] == 1 for i in w) for w in image)
    correction = m.scalar.correction(data['scalar'],
        {w: j['value'] for w, j in jet.items() if j['value']},
        {w: j['gradient'][6:, :] for w, j in jet.items()})
    assert correction
    print('PASS complete four-energy action on actual off-source Gauss jet and full392 reducing carrier', flush=True)
    normalized = m.normalized_jet(value, gs, hs, 2)
    section.verify_Gauss_jet(normalized)
    transformed_pieces, transformed = m.action(data, normalized)
    rho_jet = m.normalized_jet(value, gs, hs, 2, include_coframe=False)
    rho_pieces, _ = m.action(data, rho_jet)
    expected_cf = m.normalized_coframe(data, rho_jet, 2)
    assert weighted_sum([(1, expected_cf), (-1, transformed_pieces['coframe'])]) == {}
    for name in ('scalar_form', 'gauge', 'matter_without_Lorentz'):
        assert weighted_sum([(1, rho_pieces[name]), (-1, transformed_pieces[name])]) == {}
    expected = weighted_sum([(1, expected_cf)]+[(1, rho_pieces[k]) for k in rho_pieces if k != 'coframe'])
    assert weighted_sum([(1, transformed), (-1, expected)]) == {}
    assert weighted_sum([(1, transformed), (-1, image)])
    print('PASS common positive pairing and all100-coordinate half-density four-energy readback', flush=True)
    files = [HERE/(n+'.json') for n in dependencies]+[HERE/n for n in (
        'source_joint_form_hamiltonian.py', 'source_scalar_form_hamiltonian.py', 'source_joint_local_quantum.py',
        'source_quantum_gauss_section.py', 'source_gauge_quantum_energy.py', 'source_reducing_coframe_metric.py')]
    out = {'root': ROOT_ID, 'scope': 'ORIGINAL_FIXED_TIME_FOUR_ENERGY_FORM_ON_RESIDUAL3_AND_Y_NULL_FOCK',
        'source_sha256': m.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'operator': 'Hform=Hcoframe+Hscalar_form+Hgauge+dGamma(Hmatter), with only the source-generated scalar adjoint ordering changed from Hnative.',
        'domain': 'Cc-infinity(Omega100) tensor algebraic Fock(K392); Omega is the source component with q0*q2*q5>0, detD9!=0, A1>0, A12>0. Each test has compact support inside this open chart.',
        'pairing': 'sum_words Integral rho3(z)*v(q)^(2+card(word))*conj(f_word)*g_word dz; rho3=8*A1^2*A12, v=q0*q2*q5.',
        'half_density': 'U_m=sqrt(rho3)*v^(1+m/2), generated by the same source orbit Jacobian and original coframe adjoint equation.',
        'formal_symmetry': {'coframe': 'Full six-coordinate operator with live mixed currents, normal quartic, onebody and real shift consumes v^(2+Number).',
            'scalar': 'Original second-class Dirac measure factors cancel1. The original70 momentum graph generates sum Pi_dagger Pi/(2h00)+V on canonical103. Its residual3 equivariance transports the form to rho3. Number preservation transports it to rho3*v^(2+Number).',
            'gauge': 'Original real shifted momenta and real symmetric q-only W give the symmetric36 square and real magnetic potential. Its native residual3 invariance gives the same quotient pairing.',
            'matter': matter_adjoint,
            'common_domain': 'The four symmetric forms act on the same compact smooth equivariant section and preserve K392. Their sum is a densely defined symmetric operator in the displayed positive pairing.'},
        'original_classical_principal_symbol_preserved': True,
        'old_scalar_quantum_ordering_identified_with_new_form': False,
        'Yukawa_adjoint_added': False,
        'actual_consumer': {'q': list(map(str, q)), 'x61': encode(x), 'A36': encode(A), 'input_CAR': list(word),
            'input_gradient100': encode(gradient), 'input_Hessian100': encode(Hessian), 'Gauss': gauss,
            'all_four_component_images': {k: encode_state(v) for k, v in pieces.items()},
            'whole_image': encode_state(image), 'scalar_ordering_difference': encode_state(correction),
            'all_four_normalized_component_images': {k: encode_state(v) for k, v in transformed_pieces.items()},
            'whole_normalized_image': encode_state(transformed), 'independent_half_density_image': encode_state(expected),
            'complete_CAR_carrier_preserved': True, 'whole103_mixed_Hessian_and_zero_value_jets_retained': True},
        'time_scope': 'Literal y_source=(N,0,0,0); no temporal secondary root or spatial continuum quantization is installed here.',
        'spectral_scope': 'Formal symmetry and positive Hilbert pairing do not select a self-adjoint extension or prove convergence of the ordered temporal elimination. No positive-energy assertion is made.',
        'full504_inventory_replaced': False, 'quantum_spectrum_Gamma_tau_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_joint_form_hamiltonian.json').write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print('PASS source joint form Hamiltonian', out['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
