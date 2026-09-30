#!/usr/bin/env python3
"""Original temporal-coframe spatial-gradient flux and its canonical constraints.

The whole source curl identity gives a velocity translation.  Its exact
Hamiltonian form transports the original primary multipliers off the primary
surface; on primary fields only the spatial divergence remains.  Consequently
the four temporal coframe equations are point equations in their time column,
with the canonical momentum divergence retained as actual input data.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_coframe_constraints import SourceCoframeConstraints
from source_common_hamiltonian import real
from source_lorentz_contact import clean, equal, encode


TIME = (0, 4, 8, 12)


class SourceTemporalCoframeFlux:
    def __init__(self):
        self.full = SourceCoframeConstraints()
        self.common = self.full.common
        self.model = self.common.coframe
        self.J = s.SparseMatrix(16, 12, {(4*a+i+1, 4*i+a): 1 for i in range(3) for a in range(4)})
        self.spatial_generators = self.spatial_Lorentz_frame(self.model.e)
        self.divergence_coefficients = self.model.G[:6, 16:]

    def spatial_Lorentz_frame(self, e):
        spatial = e.copy(); spatial[:, 0] = s.zeros(4, 1)
        return clean(s.Matrix.hstack(*[(T*spatial).reshape(16, 1) for T in self.model.lorentz.basis]))

    def split_spatial_jet(self, spatial):
        assert spatial.shape == (48, 1)
        retained = spatial.copy(); gradient = s.zeros(12, 1)
        for i in range(3):
            for a in range(4):
                gradient[4*i+a] = spatial[16*i+4*a]
                retained[16*i+4*a] = 0
        return clean(retained), clean(gradient)

    def restore_spatial_jet(self, retained, gradient):
        result = retained.copy()
        for i in range(3):
            for a in range(4):
                result[16*i+4*a] = gradient[4*i+a]
        return clean(result)

    def spin_charge(self, psi, p):
        return s.Matrix([real((s.I*p*s.kronecker_product(S, s.eye(63))*psi)[0])
                         for S in self.model.lorentz.spin])

    def canonical_dual(self, e, p):
        ports = self.model.lorentz.matter_ports(e)
        inverse = clean(s.kronecker_product(ports['E'].inv(), s.eye(63)))
        return clean(s.I*p*inverse)

    def primary_rows(self, e, momentum, spatial_e, psi, p):
        """An equivalent10-row basis independent of the temporal coframe jet."""
        Lorentz = (self.spatial_Lorentz_frame(e).T*momentum+
                   self.model.at(self.divergence_coefficients, e)*spatial_e+self.spin_charge(psi, p))
        return clean(momentum.extract(TIME, [0]).col_join(Lorentz))

    def primary_prolongations(self, e, momentum, spatial_e, spatial_momentum,
                              second_spatial_e, psi, p, spatial_psi, spatial_p):
        """The spatial derivative of every primary row, from the actual jets."""
        Z, G = self.spatial_Lorentz_frame(e), self.model.at(self.divergence_coefficients, e)
        rows = []
        for i in range(3):
            direction = spatial_e[16*i:16*(i+1), 0]
            dZ = self.model.at(sum((direction[a]*self.spatial_generators.diff(self.model.e[a])
                                    for a in range(16)), s.zeros(16, 6)), e)
            dG = self.model.at(sum((direction[a]*self.divergence_coefficients.diff(self.model.e[a])
                                    for a in range(16)), s.zeros(6, 48)), e)
            dj = self.spin_charge(spatial_psi[i], p)+self.spin_charge(psi, spatial_p[i])
            value = (dZ.T*momentum+Z.T*spatial_momentum[i, :].T+dG*spatial_e+
                     G*second_spatial_e[i]+dj)
            rows.append(spatial_momentum[i, list(TIME)].T.col_join(value))
        return clean(s.Matrix.hstack(*rows).T)

    def multiplier_translation(self, e, gradient):
        """The source null-frame coordinates needed for the exact off-primary law."""
        data = self.model.geometry(e)
        null_velocity = clean((data['R']*data['D']-s.eye(16))*self.J*gradient)
        metric, parameters = self.model.velocity_coordinates(e, null_velocity)
        equal(metric, s.zeros(6, 1))
        equal(self.model.universal_null_frame(e)*parameters, null_velocity)
        return clean(parameters)

    def flux(self, e, momentum):
        return s.Matrix([sum(momentum[4*a+i+1]*e[a, 0] for a in range(4)) for i in range(3)])

    def common_H(self, fields, spatial_e, momentum, multipliers):
        return self.common.hamiltonian(fields['e'], momentum, spatial_e, fields['phi'], fields['Pi_phi'],
            fields['spatial_phi'], fields['A'], fields['Pi_A'], fields['spatial_A'],
            fields['psi'], fields['p'], fields['spatial_psi'], multipliers)

    def temporal_constraints(self, fields, momentum, spatial_e, spatial_momentum, multipliers):
        """Point constraint map on primary fields (including their spatial jets).

        The executable primary_prolongations mouth checks the required spatial
        prolongation; a single point with primary rows zero is not silently
        substituted for a field satisfying them in a neighborhood.
        """
        retained, _ = self.split_spatial_jet(spatial_e)
        equal(self.primary_rows(fields['e'], momentum, spatial_e, fields['psi'], fields['p']), s.zeros(10, 1))
        u = s.Symbol('temporal_coframe_variation', real=True)
        gradient = []
        for a in range(4):
            curve = fields['e'].copy(); curve[a, 0] += u
            value = self.common_H({**fields, 'e': curve}, retained, momentum, multipliers)['value']
            gradient.append(s.simplify(s.diff(value, u).subs(u, 0)))
        divergence = s.Matrix([sum(spatial_momentum[i, 4*a+i+1] for i in range(3)) for a in range(4)])
        return {'Hamiltonian_time_column_gradient': clean(s.Matrix(gradient)),
                'spatial_momentum_divergence': clean(divergence),
                'temporal_constraints': clean(-s.Matrix(gradient)+divergence),
                'retained_spatial_Hamiltonian_flux': self.flux(fields['e'], momentum)}


def certify_generic_source(model):
    e, G, H = model.model.e, model.model.G, model.model.H
    Gt = G[:, :16]
    Z = model.model.universal_null_frame(e)[:, 4:]
    for i in range(3):
        for a in range(4):
            equal(G[:, 16*(i+1)+4*a], -Gt[:, 4*a+i+1])
    equal(Gt*Z, H[:, :6])
    equal(Gt[:6, :], s.zeros(6, 16))
    equal(Gt[:, list(TIME)], s.zeros(24, 4))
    for i in range(3):
        f = model.model.boundary[0, 6*(i+1):6*(i+2)].T
        equal(G[:6, 16*(i+1):16*(i+2)], f.jacobian(list(e)))
    for a in TIME:
        equal(model.model.boundary[0, :].diff(e[a]), s.zeros(1, 24))
        equal(model.divergence_coefficients.diff(e[a]), s.zeros(6, 48))
        equal(model.spatial_generators.diff(e[a]), s.zeros(16, 6))
    gradient_columns = [16*i+4*a for i in range(3) for a in range(4)]
    equal(G[:, 16:][:, gradient_columns], -Gt*model.J)
    # This graph identity covers all generated original momenta without an
    # inverse or a guessed metric/ADM Lagrangian.
    v = s.Matrix(s.symbols('velocity0:16'))
    g = s.Matrix(s.symbols('gradient0:12'))
    q = s.Matrix(s.symbols('q0:24'))
    equal(Gt*(v+model.J*g)+q-Gt*model.J*g, Gt*v+q)
    return {'independent_live_coframe_variables': 16,
            'all12_curl_columns': 'G_(partial_i e_a0)=-Gt_(partial_0 e_ai)',
            'all6_Lorentz_columns': 'Gt Z_L=H_Lorentz[:,Omega0]',
            'time_connection_and_time_coframe_zero_blocks': 'Gt[Omega0,:]=0 and Gt[:,e_a0]=0',
            'source_BF_momentum_divergence': 'G[Omega0,:]de=sum_i partial_i f_i(e_spatial), f_i,a=C_a,(0i)',
            'canonical_spin_charge': 'j_Omega0=Re(i p S_a psi), p=-i chi E',
            'invariant_primary_row_basis': 'Pi_e[a0]=0; (T_a e_spatial).Pi_e+sum_i partial_i f_i,a+Re(i p S_a psi)=0',
            'primary_basis_independence': 'all10 rows in this equivalent basis are independent of e[:,0] and every partial_i e[:,0]',
            'actual_velocity_translation': 'G de+j is unchanged when spatial time-column gradients g are added and dot e is translated by Jg',
            'velocity_gradient_injection': encode(model.J),
            'generic_Legendre_graph_identity': 'Pi_e is unchanged, so H(g)-H(0)=Pi_e.Jg on the complete original Legendre image',
            'native_domain': 'the same original common noncharacteristic primary chart; no inverse-metric Maxwell or separately assumed ADM density'}


def example_fields(model):
    e = s.Matrix([[2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    psi = s.Matrix([s.Rational(i % 5-2, 7)+s.I*s.Rational(i % 3-1, 11) for i in range(252)])
    chi = s.Matrix(1, 252, lambda _, i: s.Rational(i % 7-3, 13)+s.I*s.Rational(i % 4-2, 17))
    phi = s.Matrix([s.Rational(i % 9-4, 19) for i in range(70)])
    A = s.Matrix(4, 12, lambda mu, a: s.Rational((mu+1)*(a-5), 17))
    p = clean(-s.I*chi*model.common.matter_data(e, phi, A)['E'])
    spatial_e = s.Matrix([s.Rational(i % 11-5, 29) for i in range(48)])
    retained, _ = model.split_spatial_jet(spatial_e)
    v = s.Matrix([s.Rational(i % 7-3, 31) if i % 4 else 0 for i in range(16)])
    momentum = model.model.momentum(e, v, retained, psi, chi)
    fields = {'e': e, 'psi': psi, 'chi': chi, 'p': p, 'phi': phi, 'A': A,
        'Pi_phi': s.Matrix([s.Rational(i % 7-3, 23) for i in range(70)]),
        'Pi_A': s.Matrix(3, 12, lambda i, j: s.Rational((i+j*2)%13-6, 37)),
        'spatial_phi': [s.Matrix([s.Rational((i+j)%5-2, 41) for j in range(70)]) for i in range(3)],
        'spatial_A': s.Matrix(3, 48, lambda i, j: s.Rational((i+j)%7-3, 43)),
        'spatial_psi': [s.zeros(252, 1)]*3, 'spatial_p': [s.zeros(1, 252)]*3}
    return fields, spatial_e, retained, v, momentum


def certify_actual_Hamiltonian(model, fields, retained, momentum):
    e, psi, p = fields['e'], fields['psi'], fields['p']
    chi = model.canonical_dual(e, p)
    equal(chi, fields['chi'])
    arbitrary = s.Matrix(s.symbols('canonicalPi0:16', real=True))
    g = s.Matrix(s.symbols('time_gradient0:12', real=True))
    spatial = model.restore_spatial_jet(retained, g)
    raw = model.model.constraints(e, arbitrary, spatial, psi, chi)
    invariant = model.primary_rows(e, arbitrary, spatial, psi, p)
    Ztime = model.model.universal_null_frame(e).extract(TIME, range(4, 10))
    equal(raw[:4, :], invariant[:4, :])
    equal(raw[4:, :]-Ztime.T*raw[:4, :], invariant[4:, :])
    equal(model.primary_rows(e, momentum, spatial, psi, p), s.zeros(10, 1))
    translation = model.multiplier_translation(e, g)
    first = model.common_H(fields, spatial, arbitrary, s.zeros(10, 1))
    second = model.common_H(fields, retained, arbitrary, translation)
    flux_density = (arbitrary.T*model.J*g)[0]
    assert s.expand(first['value']-second['value']-flux_density) == 0
    for name in ('scalar', 'gauge', 'matter_without_Lorentz'):
        assert s.expand(first['components'][name]-second['components'][name]) == 0
    without_transport = model.common_H(fields, retained, arbitrary, s.zeros(10, 1))
    defect = s.expand(first['value']-without_transport['value']-flux_density)
    assert defect != 0
    assert s.expand(defect-(translation.T*raw)[0]) == 0
    substitute = dict(zip(arbitrary, momentum))
    on_primary = s.expand(first['value'].xreplace(substitute))
    primary_base = s.expand(without_transport['value'].xreplace(substitute))
    assert s.expand(on_primary-primary_base-(momentum.T*model.J*g)[0]) == 0
    equal(s.Matrix([s.diff(on_primary, value) for value in g]), model.J.T*momentum)
    return {'actual_live_coframe': encode(e), 'actual_full252_primal': encode(psi),
            'actual_full252_canonical_momentum': encode(p), 'actual_primary_coframe_momentum': encode(momentum),
            'original_primary_rows': 'all10 exact after original Legendre generation',
            'canonical_invariant_rows': 'the same zero fiber after subtracting Z_time^T Pi_time from the Lorentz rows',
            'all16_independent_canonical_momenta_and12_independent_gradients': True,
            'exact_multiplier_transport': encode(translation),
            'off_primary_identity': 'H_common(g,lambda)=H_common(0,lambda+deltaLambda(e,g))+Pi_e.Jg',
            'source_of_multiplier_transport': 'Z10 deltaLambda=(R D_h-I)Jg, an actual source null velocity',
            'omitted_multiplier_transport_negative_control': 'nonzero polynomial in the independent canonical Pi and all12 time-column gradients',
            'on_primary_common_identity': 'H_common(g)-H_common(0)=sum_ia Pi_e[ai] partial_i e[a0]',
            'all12_actual_gradient_derivatives': 'equal the corresponding Pi_e[ai]',
            'other_original_Hamiltonian_blocks': 'scalar70, native gauge12 and full252 remaining Dirac are exactly unchanged by these coframe gradients'}


def certify_actual_field_jet(model, fields, spatial_e, retained, v, momentum):
    e, psi, p = fields['e'], fields['psi'], fields['p']
    _, g = model.split_spatial_jet(spatial_e)
    full_velocity = clean(v+model.J*g)
    base_data = model.model.currents(e, retained, psi, fields['chi'])
    null_velocity = clean(v-base_data['velocity_inverse']*(momentum-base_data['momentum_shift']))
    _, base_multiplier = model.model.velocity_coordinates(e, null_velocity)
    multiplier = clean(base_multiplier-model.multiplier_translation(e, g))
    velocities = model.common.boson_velocities(e, momentum, spatial_e, fields['phi'], fields['Pi_phi'],
        fields['spatial_phi'], fields['A'], fields['Pi_A'], fields['spatial_A'], psi, p, multiplier)
    equal(velocities['coframe'], full_velocity)
    de = full_velocity.col_join(spatial_e)
    dde = s.zeros(4, 64)
    chi, dpsi, dchi = model.full.on_matter_flow(e, de, fields['phi'], fields['A'], psi, p,
                                               fields['spatial_psi'], fields['spatial_p'])
    dphi = [velocities['scalar'], *fields['spatial_phi']]
    dA = s.zeros(4, 48); dA[1:, :] = fields['spatial_A']
    dA[0, 12:] = velocities['gauge_spatial'].reshape(1, 36)
    original = model.full.euler(e, de, dde, fields['phi'], dphi, fields['A'], dA, psi, dpsi, chi, dchi)
    data = model.model.geometry(e)
    equal(data['G'][:, :16].T*original['connection'], momentum)
    # Differentiate the original Legendre-generated momentum field. Since e
    # is affine in space, the chosen v/spatial jets and canonical p/psi are
    # spatially constant, all mixed coframe second jets are genuinely zero.
    spatial_momentum = s.zeros(3, 16)
    for i in range(3):
        direction = spatial_e[16*i:16*(i+1), 0]
        dGt = model.model.at(sum((direction[a]*model.model.dG[a][:, :16] for a in range(16)), s.zeros(24, 16)), e)
        spatial_momentum[i, :] = clean(dGt.T*original['connection']+
            data['G'][:, :16].T*original['connection_derivative'][i+1, :].T).T
    prolongations = model.primary_prolongations(e, momentum, spatial_e, spatial_momentum,
        [s.zeros(48, 1)]*3, psi, p, fields['spatial_psi'], fields['spatial_p'])
    equal(prolongations, s.zeros(3, 10))
    point = model.temporal_constraints(fields, momentum, spatial_e, spatial_momentum, base_multiplier)
    equal(point['temporal_constraints'], original['temporal_coframe'])
    assert point['spatial_momentum_divergence'] != s.zeros(4, 1)
    return {'all64_actual_first_coframe_jets': encode(de), 'all_symmetric_second_coframe_jets': encode(dde),
            'spatial_canonical_coframe_momentum_jets': encode(spatial_momentum),
            'all30_primary_spatial_prolongations': encode(prolongations),
            'point_Hamiltonian_time_gradient': encode(point['Hamiltonian_time_column_gradient']),
            'actual_canonical_momentum_divergence': encode(point['spatial_momentum_divergence']),
            'original_full_four_temporal_Euler': encode(original['temporal_coframe']),
            'point_map_readback': 'exactly equals the original full gravity/Lorentz+scalar+gauge+Dirac Euler time rows',
            'dropping_spatial_momentum_flux_negative_control': 'nonzero on this actual primary field jet',
            'Hamiltonian_spatial_flux': encode(point['retained_spatial_Hamiltonian_flux']),
            'original_four_BF_fluxes': encode(original['boundary_flux']),
            'all_original_constraint_rows_solved_in_this_test': False}


def main():
    began = time.monotonic()
    model = SourceTemporalCoframeFlux()
    generic = certify_generic_source(model)
    print('PASS generic16 original curl/Lorentz/BF identities and temporal-independent primary row basis', flush=True)
    fields, spatial, retained, v, momentum = example_fields(model)
    Hamiltonian = certify_actual_Hamiltonian(model, fields, retained, momentum)
    print('PASS exact full common Hamiltonian off-primary multiplier transport and12 on-primary gradient derivatives', flush=True)
    jet = certify_actual_field_jet(model, fields, spatial, retained, v, momentum)
    print('PASS actual primary field jet:all30 spatial prolongations and original4 Euler equal the point constraints plus retained flux', flush=True)
    paths = [HERE/name for name in ('source_temporal_coframe_flux.py','source_coframe_constraints.py',
        'source_coframe_constraints.json','source_common_hamiltonian.py','source_common_hamiltonian.json',
        'source_coframe_legendre.py','source_coframe_legendre.json','source_lorentz_contact.py','source_lorentz_contact.json')]
    output = {'root': ROOT_ID, 'source_sha256': model.common.scalar.exchange.vertices['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'scope': 'ORIGINAL_GENERAL_LIVE_PRIMARY_COFRAME_GRADIENT_FLUX_AND_POINT_TEMPORAL_CONSTRAINT_MAP',
        'generic_original_source_identities': generic, 'actual_full_Hamiltonian_consumer': Hamiltonian,
        'actual_primary_field_Euler_consumer': jet,
        'public_API': 'SourceTemporalCoframeFlux.{split_spatial_jet,primary_rows,primary_prolongations,multiplier_translation,flux,temporal_constraints}',
        'functional_time_constraint': '-partial_e[a0] H0+sum_i partial_i Pi_e[ai], H0 has all partial_i e[a0] set to0; fixed canonical variables and primary fields with their spatial prolongation',
        'original_spatial_boundary_identity': 'sum_ia Pi_e[ai]partial_i e[a0]=sum_i partial_i(sum_a Pi_e[ai]e[a0])-sum_a e[a0]sum_i partial_i Pi_e[ai]',
        'temporal_coframe_spatial_differential_operator_remaining': False,
        'actual_point_Jacobian_consumer': 'the common four time constraints can be differentiated in e[:,0] at fixed remaining canonical/spatial jet data; no unknown spatial derivative of this time column is hidden in the operator',
        'temporal_multiplier_preservation_or_global_Cauchy_claimed': False,
        'new_source_occurrence': False, 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_temporal_coframe_flux.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS source temporal-coframe flux/point constraint producer', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
