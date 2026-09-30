#!/usr/bin/env python3
"""Source-generated local initial data solving all four temporal coframe rows.

The fixed-canonical-variable Jacobian is nondegenerate at the original source.
A nonlinear source family has an explicit positive clock root and zero shift.
All velocities used by the original Euler readback come from the same common
Legendre maps. Temporal coframe multiplier rates are not thereby solved.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_coframe_constraints import SourceCoframeConstraints
from source_constraint_preservation import SourceConstraintPreservation
from source_lorentz_contact import clean, equal, encode
from source_scalar_legendre import dot


class SourceCoframeInitialConstraints:
    def __init__(self):
        self.full = SourceCoframeConstraints()
        self.common = self.full.common
        self.constraints = SourceConstraintPreservation()
        active = self.common.scalar.exchange.active
        self.background = active['actual_background']
        self.e0 = s.Matrix(self.background['coframe']).applyfunc(s.sympify)
        self.N = self.e0[0, 0]
        self.A = s.Matrix(self.background['gauge_connection']).applyfunc(s.sympify)
        occupied = json.loads((BASE/'occupied-response/receipt.json').read_text())
        self.psi0 = decode(occupied['occupied_frame'])*s.Matrix(self.background['primal_H']).applyfunc(s.sympify)
        self.chi0 = s.sqrt(2)*self.psi0.T
        self.vacuum = self.constraints.vacuum
        self.direction = clean(self.constraints.projector*s.eye(70)[:, 23])
        self.source_momenta = self.common.momenta(self.e0, s.zeros(64, 1),
            self.vacuum, [s.zeros(70, 1)]*4, self.A, s.zeros(4, 48), self.psi0, self.chi0)
        equal(self.source_momenta['coframe'], s.zeros(16, 1))
        equal(self.source_momenta['scalar'], s.zeros(70, 1))
        equal(self.source_momenta['gauge'], s.zeros(3, 12))
        F = self.common.gauge.curvature(self.A, s.zeros(4, 48))
        magnetic_gram = clean(F[3:, :]*self.common.gauge.gram*F[3:, :].T)
        self.c = s.simplify(s.trace(magnetic_gram)/(6*self.common.gauge.sigma))
        assert self.c == s.Rational(162, 625)

    def fields(self, n, shift, scalar_amplitude, primal_amplitude, dual_amplitude, radial_momentum=0):
        e = s.diag(n, 1, 1, 1)
        e[1:, 0] = s.Matrix(shift)
        psi, chi = self.psi0.copy(), self.chi0.copy()
        psi[135] += primal_amplitude
        chi[126] += dual_amplitude
        phi = clean(self.vacuum+scalar_amplitude*self.direction)
        Pi_phi = clean(radial_momentum*scalar_amplitude*self.direction)
        # E depends only on the spatial coframe columns. Thus p is fixed
        # when differentiating the four temporal coframe variables below.
        p = clean(-s.I*chi*self.common.matter_data(self.e0, phi, self.A)['E'])
        return {'e': e, 'phi': phi, 'Pi_phi': Pi_phi, 'psi': psi, 'chi': chi, 'p': p,
                'scalar_amplitude': scalar_amplitude, 'primal_amplitude': primal_amplitude,
                'dual_amplitude': dual_amplitude, 'radial_momentum': radial_momentum}

    def hamiltonian(self, fields):
        return self.common.hamiltonian(fields['e'], self.source_momenta['coframe'], s.zeros(48, 1),
            fields['phi'], fields['Pi_phi'], [s.zeros(70, 1)]*3, self.A,
            self.source_momenta['gauge'], s.zeros(3, 48), fields['psi'], fields['p'],
            [s.zeros(252, 1)]*3, s.zeros(10, 1))

    @staticmethod
    def clock_coefficient(u, alpha, beta, radial=0):
        return s.Rational(9, 5)-alpha*beta*u/2+(s.Rational(73, 200)-radial**2/4)*u**2

    def solve(self, u, alpha, beta, radial=0):
        coefficient = s.factor(self.clock_coefficient(u, alpha, beta, radial))
        assert coefficient.is_positive is True, 'this positive-source family requires its generated coefficient a>0'
        square = s.cancel(3*self.c/coefficient)
        fields = self.fields(s.sqrt(square), s.zeros(3, 1), u, alpha, beta, radial)
        return {**fields, 'clock_squared': square, 'clock_coefficient': coefficient}

    def local_initial_jet(self, fields):
        """Generate original time jets from fixed canonical source data."""
        common = self.common
        e, phi, psi, p = [fields[name] for name in ('e', 'phi', 'psi', 'p')]
        velocities = common.boson_velocities(e, self.source_momenta['coframe'], s.zeros(48, 1),
            phi, fields['Pi_phi'], [s.zeros(70, 1)]*3, self.A,
            self.source_momenta['gauge'], s.zeros(3, 48), psi, p, s.zeros(10, 1))
        de = s.zeros(64, 1)
        de[:16, :] = velocities['coframe']
        # Every current spatial field jet is zero in this homogeneous datum.
        # The inverse-Legendre velocities are consequently spatially constant,
        # so the mixed second coframe jets are zero by their chain rule.
        dde = s.zeros(4, 64)
        dphi = [velocities['scalar'], *[s.zeros(70, 1)]*3]
        dA = s.zeros(4, 48)
        dA[0, 12:] = velocities['gauge_spatial'].reshape(1, 36)
        chi, dpsi, dchi = self.full.on_matter_flow(e, de, phi, self.A, psi, p,
                                                   [s.zeros(252, 1)]*3, [s.zeros(1, 252)]*3)
        return {'de': de, 'dde': dde, 'dphi': dphi, 'dA': dA,
                'chi': chi, 'dpsi': dpsi, 'dchi': dchi, 'velocities': velocities}


def certify_actual_canonical_family(model):
    n = s.Symbol('n', positive=True)
    shift = s.Matrix(s.symbols('shift1:4', real=True))
    u, alpha, beta, radial = s.symbols('u alpha beta radial', real=True)
    fields = model.fields(n, shift, u, alpha, beta, radial)
    actual = model.hamiltonian(fields)
    a = model.clock_coefficient(u, alpha, beta, radial)
    radius = dot(shift, shift)
    expected = n*a+model.c*(3*n**2-radius)/(n*(n**2-radius))
    assert s.factor(actual['value']-expected) == 0
    expected_components = {
        'coframe_Lorentz_matter': 9*n,
        'scalar': n*u**2*(s.Rational(73, 200)-radial**2/4),
        'gauge': model.c*(3*n**2-radius)/(n*(n**2-radius)),
        'matter_without_Lorentz': -n*(s.Rational(36, 5)+alpha*beta*u/2)}
    for name, value in expected_components.items():
        assert s.factor(actual['components'][name]-value) == 0, name
    equal(actual['coframe_primary'], s.zeros(10, 1))
    equal(actual['dual'], fields['chi'])
    data = model.common.matter_data(fields['e'], fields['phi'], model.A)
    equal(data['E'], model.common.matter_data(model.e0, fields['phi'], model.A)['E'])
    # This is the original momentum, not an independently set zero momentum:
    # the whole nonlinear matter-induced coframe shift is recomputed here.
    shift_data = model.common.coframe.currents(fields['e'], s.zeros(48, 1), fields['psi'], fields['chi'])
    equal(shift_data['momentum_shift'], model.source_momenta['coframe'])
    equal(model.constraints.potential_constraint(fields['phi']), s.zeros(12, 1))
    scalar_charge = s.Matrix([dot(fields['Pi_phi'], R*fields['phi']) for R in model.constraints.rho])
    equal(scalar_charge, s.zeros(12, 1))
    common_gauss = model.common.gauss(fields['e'], fields['phi'], fields['Pi_phi'], model.A,
        model.source_momenta['gauge'], [s.zeros(3, 12)]*3, fields['psi'], fields['p'])
    equal(common_gauss['total'], s.zeros(12, 1))
    variables = [n, *shift]
    constraints = s.Matrix([-s.diff(expected, value) for value in variables])
    source = {u: 0, alpha: 0, beta: 0, radial: 0, n: model.N, **dict.fromkeys(shift, 0)}
    equal(constraints.subs(source), s.zeros(4, 1))
    Jacobian = clean(constraints.jacobian(variables).subs(source))
    equal(Jacobian, s.diag(-s.sqrt(30), *[-2*s.sqrt(30)/3]*3))
    assert s.simplify(Jacobian.det()) == s.Rational(800, 3)
    # Actual nonlinear solution, proved at symbolic positive n without
    # introducing a new proper-clock convention or solving an old probe.
    stationary = constraints.subs(dict.fromkeys(shift, 0))
    assert s.expand(stationary[0]*n**2+a*n**2-3*model.c) == 0
    equal(stationary[1:, :], s.zeros(3, 1))
    for i in range(3):
        assert s.factor(constraints[i+1]+4*model.c*n*shift[i]/(n**2-radius)**2) == 0
    assert s.factor((3*model.c/a).subs({u: 0, alpha: 0, beta: 0, radial: 0})) == s.Rational(54, 125)
    return {'family_coframe': encode(fields['e']),
            'family_scalar': encode(fields['phi']), 'family_scalar_momentum': encode(fields['Pi_phi']),
            'family_primal': encode(fields['psi']), 'family_independent_dual': encode(fields['chi']),
            'family_canonical_matter_momentum': encode(fields['p']),
            'original_coframe_momentum': encode(model.source_momenta['coframe']),
            'original_gauge_momentum': encode(model.source_momenta['gauge']),
            'actual_source_point': 'alpha=beta=u=radial=0, n=N, shift=0; this returns the original SpinPair.actual matter as well as its coframe',
            'fixed_canonical_variables': 'Pi_e and Pi_A are their actual source momenta; Pi_phi=radial*(phi-v); p=-i chi E(spatial e) is independent of n and shift',
            'whole_recomputed_coframe_momentum_shift': 'equals the original source Pi_e=0 for the entire displayed family',
            'common_Hamiltonian_components': {name: str(value) for name, value in expected_components.items()},
            'common_Hamiltonian': str(expected), 'generated_clock_coefficient': str(a),
            'four_canonical_temporal_constraints': encode(constraints),
            'actual_source_temporal_Jacobian': encode(Jacobian),
            'actual_source_temporal_Jacobian_determinant': '800/3',
            'exact_positive_time_column': 'shift=0, n=sqrt((486/625)/a), on a>0',
            'original_source_clock_squared_regenerated': '54/125',
            'family_constraint_Jacobian_at_solved_column': 'diag(-6c/n^3,-4c/n^3,-4c/n^3,-4c/n^3), determinant384c^4/n^12, c=162/625',
            'analytic_local_branch': 'the actual rational/real-analytic common canonical constraint map has this nonzero four-variable Jacobian at the original source. On the same positive orientation and noncharacteristic primary chart, the real-analytic implicit-function theorem gives a unique nearby temporal coframe branch as the remaining canonical field/spatial-jet data vary; the displayed family supplies its explicit restriction',
            'uniform_all_live_coframes_or_all_canonical_data_claimed': False}


def certify_nonlinear_initial_jet(model):
    # A true nonzero-field member of the same family, not the source labelled
    # after changing its matter data. Its scalar momentum is also nonzero.
    fields = model.solve(s.Rational(1, 4), s.Integer(1), s.Integer(1), s.Rational(1, 3))
    jet = model.local_initial_jet(fields)
    e, phi, psi, p = [fields[name] for name in ('e', 'phi', 'psi', 'p')]
    equal(jet['chi'], fields['chi'])
    equal(jet['de'], s.zeros(64, 1))
    assert jet['dphi'][0] != s.zeros(70, 1)
    # The real original Euler is recomputed after the Legendre velocities;
    # no old raw time jet is held fixed while the clock changes.
    original = model.full.euler(e, jet['de'], jet['dde'], phi, jet['dphi'], model.A,
        jet['dA'], psi, jet['dpsi'], jet['chi'], jet['dchi'])
    equal(original['temporal_coframe'], s.zeros(4, 1))
    equal(original['Lorentz_projection'], s.zeros(6, 1))
    matter = model.common.matter_euler(e, jet['de'], phi, model.A, psi, jet['chi'],
                                      jet['dpsi'], jet['dchi'], original['connection'])
    equal(matter['primal'], s.zeros(252, 1))
    equal(matter['dual'], s.zeros(1, 252))
    equal(model.common.fixed_p_coframe_correction(e, jet['chi'], matter['primal']), s.zeros(16, 1))
    momenta = model.common.momenta(e, jet['de'], phi, jet['dphi'], model.A, jet['dA'], psi, jet['chi'])
    equal(momenta['coframe'], model.source_momenta['coframe'])
    equal(momenta['scalar'], fields['Pi_phi'])
    equal(momenta['gauge'], model.source_momenta['gauge'])
    equal(momenta['matter'], p)
    gauss = model.common.gauss(e, phi, fields['Pi_phi'], model.A, model.source_momenta['gauge'],
                               [s.zeros(3, 12)]*3, psi, p)
    equal(gauss['total'], s.zeros(12, 1))
    equal(model.constraints.potential_constraint(phi), s.zeros(12, 1))
    equal(model.constraints.potential_constraint(jet['dphi'][0]), s.zeros(12, 1))
    A0 = model.constraints.solve_time_connection(e, phi, fields['Pi_phi'], [s.zeros(70, 1)]*3, model.A)
    equal(A0['time_connection'], model.A[0, :].T)
    rates = model.constraints.original_scalar_rates(e, s.zeros(16, 1), [s.zeros(16, 1)]*3,
        phi, fields['Pi_phi'], [s.zeros(70, 1)]*3, [s.zeros(70, 1)]*3,
        [[s.zeros(70, 1)]*3 for _ in range(3)], model.A, s.zeros(3, 48),
        model.source_momenta['gauge'], psi, jet['chi'])
    assert rates['Yukawa_scalar_source'] != s.zeros(70, 1)
    assert model.constraints.orbit.T*rates['Yukawa_scalar_source'] != s.zeros(12, 1)
    update = model.constraints.solve_time_connection_derivative(phi, rates['scalar_velocity'],
                     rates['time_connection_rhs_rate'], A0['time_connection'])
    equal(A0['matrix']*update['time_connection_rate']+
          model.constraints.consistency_matrix(rates['scalar_velocity'])*A0['time_connection']-
          rates['time_connection_rhs_rate'], s.zeros(12, 1))
    # The parent complete Euler readback keeps all four original BF fluxes.
    # A selected zero temporal multiplier rate here is a representative for
    # evaluating initial constraints, not an assertion of their time preservation.
    return {'family_parameters': {'u': '1/4', 'alpha': '1', 'beta': '1', 'radial': '1/3'},
            'generated_clock_coefficient': str(fields['clock_coefficient']),
            'generated_clock_squared': str(fields['clock_squared']), 'coframe': encode(e),
            'scalar': encode(phi), 'scalar_canonical_momentum': encode(fields['Pi_phi']),
            'primal': encode(psi), 'independent_dual': encode(jet['chi']), 'canonical_matter_momentum': encode(p),
            'canonical_coframe_momentum': encode(momenta['coframe']),
            'canonical_gauge_momentum': encode(momenta['gauge']),
            'actual_scalar_time_velocity': encode(jet['dphi'][0]),
            'actual_gauge_time_velocity': encode(jet['velocities']['gauge_spatial']),
            'actual_full252_matter_time_velocity': encode(jet['dpsi'][0]),
            'actual_full252_dual_time_velocity': encode(jet['dchi'][0]),
            'all64_first_coframe_jets': encode(jet['de']),
            'all_symmetric_second_coframe_jets': encode(jet['dde']),
            'original_four_temporal_coframe_constraints': encode(original['temporal_coframe']),
            'original_six_Lorentz_projection': encode(original['Lorentz_projection']),
            'original_all252_primal_and_dual_Euler': '0',
            'original_fixed_p_chain_correction': '0 on this generated matter flow; its four temporal entries are identically0 even off shell',
            'original_total_Gauss': encode(gauss['total']),
            'original_scalar_constraint_and_rate': 'C=0 and dotC=0',
            'generated_time_gauge_connection': encode(A0['time_connection']),
            'nonzero_full_Yukawa_scalar_source': encode(rates['Yukawa_scalar_source']),
            'nonzero_source_time_gauge_connection_rate': encode(update['time_connection_rate']),
            'original_four_BF_boundary_fluxes': encode(original['boundary_flux']),
            'time_coframe_multiplier_rate_status': 'not selected by preservation; zero is only the representative used to evaluate initial constraints, which are independent of these four rates',
            'remaining_initial_Euler_data': encode(original['Euler']),
            'local_initial_data_not_global_Cauchy_solution': True}


def certify_temporal_independence(model):
    common = model.common
    e = common.coframe.e
    temporal = (0, 4, 8, 12)
    for a in temporal:
        equal(common.coframe.adj[0, :].diff(e[a]), s.zeros(1, 4))
        equal(common.coframe.G[:, a], s.zeros(24, 1))
    # The local A0 term contains no coframe coefficient at fixed canonical
    # variables. Its spatial divergence is retained in the common Gauss API.
    return {'generic16_temporal_Dirac_principal_derivatives': 'all four zero',
            'generic16_coframe_temporal_momentum_columns': 'all four zero',
            'fixed_p_temporal_chain': 'chi=i p E^-1 has no variation along e[:,0]; the four fixed-p correction entries are zero off shell',
            'A0_coframe_mixed_block': 'H_A0=-A0.Gauss+sum_i partial_i(Pi_Ai.A0), and each canonical Gauss term is independent of e: scalar Pi_phi.rho.phi, matter Re(i p rho psi), native gauge covector divergence',
            'next_coupled_update_interface': 'first use the generated4x4 temporal coframe Jacobian on the actual derivative of its constraints to solve the four temporal coframe rates; then pass that whole coframe rate into original_scalar_rates and solve the existing9x9 D(phi) time-gauge consistency equation',
            'joint13_update_block_shape': 'upper-right A0 block is zero at fixed canonical data; no new coupled13x13 inverse is required',
            'actual_temporal_coframe_preservation_forcing_already_constructed': False}


def main():
    began = time.monotonic()
    model = SourceCoframeInitialConstraints()
    family = certify_actual_canonical_family(model)
    print('PASS actual common fixed-canonical H family,original source N^2=54/125 and4x4 Jacobian det800/3', flush=True)
    initial = certify_nonlinear_initial_jet(model)
    print('PASS nonlinear generated clock with nonzero Yukawa and scalar velocity:all4 original time-coframe rows,Gauss,C9 andfull matter Euler', flush=True)
    next_interface = certify_temporal_independence(model)
    paths = [HERE/name for name in ('source_coframe_initial_constraints.py','source_coframe_constraints.py',
        'source_coframe_constraints.json','source_common_hamiltonian.py','source_common_hamiltonian.json',
        'source_constraint_preservation.py','source_constraint_preservation.json',
        'source_coframe_legendre.py','source_coframe_legendre.json','source_gauge_legendre.py','source_gauge_legendre.json')]
    result = {'root': ROOT_ID, 'source_sha256': model.common.scalar.exchange.vertices['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'scope': 'ORIGINAL_COMMON_HAMILTONIAN_GENERATED_TEMPORAL_COFRAME_BRANCH_AND_CONSTRAINT_SATISFYING_LOCAL_INITIAL_JET',
        'actual_canonical_source_family': family, 'nonlinear_constraint_satisfying_initial_jet': initial,
        'temporal_principal_and_next_consistency': next_interface,
        'public_API': 'SourceCoframeInitialConstraints.{fields,hamiltonian,clock_coefficient,solve,local_initial_jet}',
        'new_source_occurrence_or_proper_clock_normalization': False,
        'complete_constraint_preservation_global_Cauchy_or_spectrum_claimed': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_coframe_initial_constraints.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source-generated nonlinear local initial constraints', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
