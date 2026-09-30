#!/usr/bin/env python3
"""One positive pairing and adjoint pair for the original four-time family.

The scalar source form is composed with the original coframe, gauge and matter
operators before taking time derivatives. The Dirac antiunitary reflects the
three shift parameters; it does not fix a generic nonzero-shift Hamiltonian.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_scalar_temporal_form import SourceScalarTemporalForm
from source_scalar_form_hamiltonian import relocate_section
from source_joint_form_hamiltonian import read_bound
from source_quantum_antiunitary import SourceQuantumAntiunitary
from source_full_quantum_adjoint import split_matter
from source_coframe_live_ordering import verify_jet_action
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode, GAMMA
from source_gauss_quantum_current import weighted_sum, apply_superposition, encode_state


class SourceCommonTemporalForm:
    def __init__(self):
        self.scalar = SourceScalarTemporalForm()
        self.native, self.section = self.scalar.native, self.scalar.section
        self.family = self.scalar.family
        self.C = SourceQuantumAntiunitary(self)

    def coefficients(self, time_column, q, x, A):
        data = self.family.coefficients(time_column, q, x, A)
        data['scalar'] = self.scalar.form.coefficients(data['e'], x, A)
        return data

    def scalar_action(self, d, value, gradients, Hessians):
        """Full shifted scalar graph after contraction, retaining every db."""
        base = self.scalar.form.old_square({**d, 'shift': s.zeros(70, 1)}, value, gradients, Hessians)
        a, n, b = d['momentum_vectors'], -d['normal_embedding'], d['shift']
        db = d['shift_derivative']; h = 2*d['h00']
        trace = sum(a[i, u]*db[i, u] for (i, u) in a.todok())
        terms = [(1, base), ((s.I*trace+(b.T*b)[0])/h, value)]
        for word, g in gradients.items():
            terms.append((2*s.I*(b.T*a*g)[0]/h, {word: 1}))
        current = rational(-2*b.T*n/h)
        for j in range(9): terms.append((current[j], self.scalar.form.current(j, value)))
        terms.append((1, self.scalar.form.correction(d, value, gradients)))
        return weighted_sum(terms)

    def action(self, data, jet):
        values = {w: row['value'] for w, row in jet.items() if row['value']}
        gradients = {w: row['gradient'][6:, :] for w, row in jet.items()}
        Hessians = {w: row['Hessian'][6:, 6:] for w, row in jet.items()}
        scalar = self.scalar_action(data['scalar'], values, gradients, Hessians)
        coframe, gauge = [], []
        gd = data['gauge']; W, b = gd['weight'], gd['momentum_shift']
        constant = (b.T*W*b)[0]/2+gd['derivative_ordering_constant']+gd['magnetic_potential']
        for w, row in jet.items():
            cf = verify_jet_action(data['coframe'], w, row['value'], row['gradient'][:6, :], row['Hessian'][:6, :6])
            coframe.append((1, {tuple(word): s.sympify(v) for word, v in cf['raw_nested_square']}))
            g, H = row['gradient'][67:, :], row['Hessian'][67:, 67:]
            out = -sum(v*H[i, j] for (i, j), v in W.todok().items())/2+s.I*(b.T*W*g)[0]+constant*row['value']
            gauge.append((out, {w: 1}))
        M0, Y = split_matter(data)
        pieces = {'coframe': weighted_sum(coframe), 'scalar_form': scalar,
                  'gauge': weighted_sum(gauge), 'matter_noY': apply_superposition(M0, values)}
        H0 = weighted_sum((1, image) for image in pieces.values())
        Yimage = apply_superposition(Y, values)
        return {'pieces': pieces, 'H0': H0, 'Y': Yimage,
                'H': weighted_sum([(1, H0), (1, Yimage)]),
                'Hsharp': weighted_sum([(1, H0), (1, apply_superposition(Y.H, values))])}


def generic_laws(model):
    family = model.family; e = family.e; y = family.y
    reflection = dict(zip(y, (y[0], *[-b for b in y[1:]])))
    gauge = model.native.joint.gauge.coefficients(e)
    W, b = gauge['weight'], gauge['momentum_shift']
    equal(rational(W.H-W), s.zeros(36))
    equal(rational(W.xreplace(reflection)-W), s.zeros(36))
    equal(rational(b.xreplace(reflection)+b), s.zeros(36, 1))
    assert s.cancel(gauge['magnetic_potential'].xreplace(reflection)-gauge['magnetic_potential']) == 0
    assert s.expand(s.conjugate(gauge['magnetic_potential'])-gauge['magnetic_potential']) == 0
    ports = model.native.joint.coframe.model.lorentz.raw_matter_ports(e)
    spin = []
    for i in range(1, 4):
        S = rational(-s.I*ports['E'].inv()*ports['oriented_principals'][i])
        equal(rational(S.H+S), s.zeros(4))
        equal(rational(-GAMMA[0]*S*GAMMA[0].H-S.xreplace(reflection)), s.zeros(4))
        spin.append(S)
    for rho in model.native.graph.common.rho: equal(rho.H, -rho)
    smetric = model.scalar.metric
    sr = dict(zip(model.scalar.y, (model.scalar.y[0], *[-b for b in model.scalar.y[1:]])))
    assert s.cancel(smetric[0, 0].xreplace(sr)-smetric[0, 0]) == 0
    equal(rational(smetric[0, 1:].xreplace(sr)+smetric[0, 1:]), s.zeros(1, 3))
    equal(rational(smetric[1:, 1:].xreplace(sr)-smetric[1:, 1:]), s.zeros(3))
    for Q in model.native.Q_b+model.native.Q_s:
        equal(model.C.U*Q.conjugate()*model.C.U.H, -Q)
    return {'generic_gauge_W_real_symmetric_and_shift_even': True,
        'generic_gauge_C_shift_odd_and_potential_real_even': True,
        'all3_matter_spin_anti_Hermitian_at_all4time': [encode(S) for S in spin],
        'all12_internal_generators_anti_Hermitian': True,
        'scalar_Pi_and_adjoint_map_to_negated_reflected_shift': True,
        'all12_CAR_current_antiunitary_signs': True}


def main():
    started = time.monotonic()
    deps = ('source_scalar_temporal_form', 'independent_source_scalar_temporal_form',
        'source_temporal_coframe_pairing', 'independent_source_temporal_coframe_pairing',
        'source_temporal_gauss_relations', 'independent_source_temporal_gauss_relations',
        'source_quantum_antiunitary', 'independent_source_quantum_antiunitary')
    bound = {name: read_bound(name) for name in deps}
    model = SourceCommonTemporalForm(); facts = generic_laws(model)
    print('PASS complete generic four-time gauge/matter adjoints and source shift-reflection laws', flush=True)
    row = bound['source_scalar_temporal_form']['actual_consumer']
    q = tuple(map(s.sympify, row['q'])); x, A = decode(row['x61']), decode(row['A36'])
    positive = tuple(map(s.sympify, row['time_column'])); negative = (positive[0], *[-b for b in positive[1:]])
    relocate_section(model.section, s.Matrix(q).col_join(x).col_join(A.reshape(36, 1)))
    word = tuple(row['input_CAR']); g = decode(row['gradient100']); H = decode(row['Hessian100'])
    jet = model.section.extend_jet({word: 1}, {word: g}, {word: H})
    gauss = model.section.verify_Gauss_jet(jet)
    data = model.coefficients(positive, q, x, A)
    actual = model.action(data, jet)
    scalar_nested = {tuple(w): s.sympify(v) for w, v in row['original_full70_adjoint_form']}
    assert weighted_sum([(1, actual['pieces']['scalar_form']), (-1, scalar_nested)]) == {}
    previous = bound['source_scalar_temporal_form']['actual_fourteen_atom_consumer']
    previous_H = {tuple(w): s.sympify(v) for w, v in previous['whole_image']}
    assert weighted_sum([(1, actual['H']), (-1, previous_H)]) == {}
    assert actual['Y'] and all(actual['pieces'].values())
    reflected_jet = model.C.jet(jet)
    model.section.verify_Gauss_jet(reflected_jet)
    reflected_data = model.coefficients(negative, q, x, A)
    reflected = model.action(reflected_data, reflected_jet)
    for part in actual['pieces']:
        assert weighted_sum([(1, reflected['pieces'][part]), (-1, model.C.state(actual['pieces'][part]))]) == {}
    assert weighted_sum([(1, reflected['H0']), (-1, model.C.state(actual['H0']))]) == {}
    full_defect = weighted_sum([(1, reflected['H']), (-1, model.C.state(actual['H']))])
    assert full_defect
    unreflected = model.action(data, reflected_jet)
    unreflected_defect = weighted_sum([(1, unreflected['H0']), (-1, model.C.state(actual['H0']))])
    assert unreflected_defect
    print('PASS actual full504 Gauss four-energy family, complete reflected H0 action and nonzero unreflected/Y controls', flush=True)
    files = [HERE/(name+'.json') for name in deps]+[HERE/name for name in (
        'source_common_temporal_form.py', 'source_scalar_temporal_form.py', 'source_quantum_ordered_temporal.py',
        'source_scalar_form_hamiltonian.py', 'source_quantum_antiunitary.py', 'source_full_quantum_adjoint.py')]
    out = {'root': ROOT_ID, 'scope': 'FULL504_FOUR_TIME_FORM_ADJOINT_PAIR_AND_ORIGINAL_SHIFT_REFLECTION',
        'source_sha256': model.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'generic_laws': facts,
        'common_pairing': 'rho3*v^(2+Number) on Cc-infinity(Omega100) tensor Fock(C504), independent of n,b.',
        'whole_family': 'H(n,b)=H0(n,b)+Y(n), Hsharp(n,b)=H0(n,b)+Y(n)^dagger; all four source energies and all504 modes retained. For every real admitted n,b the same test pairing gives the displayed formal adjoint, and H0 is symmetric.',
        'time_derivative_consumers': 'The smooth coefficient functions have the same source-independent compact test domain and positive pairing. Differentiating the generated form identity in any of the four real time parameters gives the corresponding formal-adjoint identity for the original temporal constraint operator -partial_y H.',
        'reflection': 'C H0(n,b)=H0(n,-b) C. The opposite-shift test graph and its closure have conjugate defect parameters. C does not commute with a generic fixed nonzero-shift H0, and the original Y term is not inserted or symmetrized.',
        'actual_consumer': {'time': list(map(str, positive)), 'reflected_time': list(map(str, negative)),
            'q': list(map(str, q)), 'x61': encode(x), 'A36': encode(A), 'input_CAR': list(word),
            'gradient100': encode(g), 'Hessian100': encode(H), 'Gauss': gauss,
            'positive_components': {k: encode_state(v) for k, v in actual['pieces'].items()},
            'positive_H': encode_state(actual['H']), 'positive_H0': encode_state(actual['H0']),
            'positive_Hsharp': encode_state(actual['Hsharp']),
            'reflected_components': {k: encode_state(v) for k, v in reflected['pieces'].items()},
            'reflected_H0_C': encode_state(reflected['H0']), 'C_H0': encode_state(model.C.state(actual['H0'])),
            'unreflected_H0_defect': encode_state(unreflected_defect), 'original_Y_reflection_defect': encode_state(full_defect),
            'full70_nested_scalar_and_full14_reconstruction_consumed': True},
        'temporal_secondary_operator_solution_or_summed_series_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_common_temporal_form.json').write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print('PASS source common temporal form', out['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
