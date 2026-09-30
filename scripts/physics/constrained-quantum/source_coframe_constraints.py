#!/usr/bin/env python3
"""Original full-action coframe constraints after auxiliary elimination.

The Lorentz Noether directions and the four temporal coframe equations are
read from the same complete Euler vector. No extra gravitational stress or
independently chosen matter Hamiltonian is added.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_common_hamiltonian import SourceCommonHamiltonian, example_fields, real
from source_lorentz_contact import clean, equal, encode, GAMMA
from source_scalar_legendre import dot


class SourceCoframeConstraints:
    def __init__(self):
        self.common = SourceCommonHamiltonian()

    def lorentz_euler(self, e, de, dde, psi, dpsi, chi, dchi):
        """Exact internal trace of the full252 current, with all63 entries kept."""
        model = self.common.coframe
        data = model.geometry(e)
        ports = model.lorentz.raw_matter_ports(e)
        spin_density = clean(psi.reshape(4, 63)*chi.reshape(4, 63).T)
        def current(matrices, density):
            return s.Matrix([real(s.trace(V*density)) for V in matrices])
        def port_derivatives(direction):
            adj = model.at(sum((direction[a]*model.dadj[a] for a in range(16)), s.zeros(4)), e)
            return [clean(ports['orientation']*sum((s.I*adj[mu, b]*GAMMA[b]
                         for b in range(4)), s.zeros(4))*S)
                    for mu in range(4) for S in model.lorentz.spin]
        j = current(ports['V'], spin_density)
        Omega = clean(-data['Lorentz_inverse']*(data['G']*de+j))
        dH = [model.at(M, e) for M in model.dH]
        dG = [model.at(M, e) for M in model.dG]
        force = s.zeros(16, 1)
        for a in range(16):
            dj = current(port_derivatives(s.eye(16)[:, a]), spin_density)
            ddet = e.adjugate()[a % 4, a//4]
            force[a] = s.expand(-3*ddet+(Omega.T*dH[a]*Omega)[0]/2+
                                (Omega.T*dG[a]*de)[0]+(Omega.T*dj)[0])
        divergence = s.zeros(16, 1)
        derivatives = s.zeros(4, 24)
        for mu in range(4):
            direction = de[16*mu:16*(mu+1), :]
            d_density = clean(dpsi[mu].reshape(4, 63)*chi.reshape(4, 63).T+
                              psi.reshape(4, 63)*dchi[mu].reshape(4, 63).T)
            dj = current(port_derivatives(direction), spin_density)+current(ports['V'], d_density)
            H_mu = clean(sum((direction[a]*dH[a] for a in range(16)), s.zeros(24)))
            G_mu = clean(sum((direction[a]*dG[a] for a in range(16)), s.zeros(24, 64)))
            dOmega = clean(-data['Lorentz_inverse']*(H_mu*Omega+G_mu*de+data['G']*dde[mu, :].T+dj))
            derivatives[mu, :] = dOmega.T
            divergence += G_mu[:, 16*mu:16*(mu+1)].T*Omega+data['G'][:, 16*mu:16*(mu+1)].T*dOmega
        return {'Euler': clean(force-divergence), 'connection': Omega,
                'connection_derivative': clean(derivatives),
                'boundary_flux': model.boundary_flux(e, Omega)}

    def remaining_stress(self, e, phi, dphi, A, dA, psi, dpsi, chi):
        """All16 original scalar/gauge/free-Dirac coframe variations at fixed chi."""
        common = self.common
        data = common.matter_data(e, phi, A)
        volume = s.Abs(e.det())
        inverse = e.inv()
        h, _ = common.scalar.metric_density(e)
        metric_inverse = h/volume
        temporal, spatial = common.scalar.covariant(phi, dphi[1:], A)
        U = [dphi[0]+temporal, *spatial]
        F = common.gauge.curvature(A, dA)
        constitutive = common.gauge.constitutive(e)
        connection = [sum((A[mu, a]*common.rho[a] for a in range(12)), s.zeros(252)) for mu in range(4)]
        covariant_without_Lorentz = [dpsi[mu]+connection[mu]*psi for mu in range(4)]
        scalar, gauge, matter = [], [], []
        for a in range(16):
            delta = s.zeros(4)
            delta[a//4, a % 4] = 1
            determinant_derivative = e.adjugate()[a % 4, a//4]
            volume_derivative = s.sign(e.det())*determinant_derivative
            dh = clean(volume_derivative*metric_inverse-volume*(inverse*delta*metric_inverse+
                                                                metric_inverse*delta.T*inverse.T))
            scalar.append(s.expand(sum(dh[mu, nu]*dot(U[mu], U[nu])/2
                                       for mu in range(4) for nu in range(4))-
                                   volume_derivative*dot(phi-common.scalar.vacuum, phi-common.scalar.vacuum)))
            dK = (common.gauge.at(common.gauge.dkernel[a], e)/e.det()-
                  constitutive['kernel']*determinant_derivative/e.det())
            gauge.append(s.expand(sum(x*y for x, y in zip(F, dK*F*common.gauge.gram))/2))
            adj_a = common.coframe.at(common.coframe.dadj[a], e)
            vector = volume_derivative*data['Y']*psi
            for mu in range(4):
                dC = clean(s.kronecker_product(s.sign(e.det())*sum(
                    (s.I*adj_a[mu, b]*GAMMA[b] for b in range(4)), s.zeros(4)), s.eye(63)))
                vector += dC*covariant_without_Lorentz[mu]
            matter.append(real((chi*vector)[0]))
        return {'scalar': clean(s.Matrix(scalar)), 'gauge': clean(s.Matrix(gauge)),
                'matter_without_Lorentz': clean(s.Matrix(matter))}

    def euler(self, e, de, dde, phi, dphi, A, dA, psi, dpsi, chi, dchi):
        gravity = self.lorentz_euler(e, de, dde, psi, dpsi, chi, dchi)
        remaining = self.remaining_stress(e, phi, dphi, A, dA, psi, dpsi, chi)
        total = clean(gravity['Euler']+sum(remaining.values(), s.zeros(16, 1)))
        Z = self.common.coframe.universal_null_frame(e)
        return {'Euler': total, 'gravity_Lorentz_Euler': gravity['Euler'],
                'remaining_stress': remaining, 'connection': gravity['connection'],
                'connection_derivative': gravity['connection_derivative'],
                'temporal_coframe': total.extract([0, 4, 8, 12], [0]),
                'Lorentz_projection': clean(Z[:, 4:].T*total),
                'boundary_flux': gravity['boundary_flux']}

    def on_matter_flow(self, e, de, phi, A, psi, p, spatial_psi, spatial_p):
        """Generate both matter time jets; retain arbitrary spatial field jets."""
        common = self.common
        data = common.matter_data(e, phi, A)
        chi = common.canonical_dual(data, p)
        Omega = common.coframe.lorentz.eliminate(e, de, psi, chi)['connection']
        flow = common.matter_canonical_flow(e, de, phi, A, psi, p, spatial_psi, spatial_p, Omega)
        dpsi = [flow['primal_velocity'], *spatial_psi]
        dp = [flow['canonical_dual_velocity'], *spatial_p]
        dchi = []
        for mu in range(4):
            dadj = common.coframe.at(sum((de[16*mu+a]*common.coframe.dadj[a]
                                        for a in range(16)), s.zeros(4)), e)
            dE = clean(s.kronecker_product(s.sign(e.det())*sum(
                (s.I*dadj[0, a]*GAMMA[a] for a in range(4)), s.zeros(4)), s.eye(63)))
            dchi.append(clean(s.I*dp[mu]*data['inverse_E']-chi*dE*data['inverse_E']))
        return chi, dpsi, dchi


def generic_Lorentz_invariance(model):
    common = model.common
    native = common.coframe.lorentz
    e = common.coframe.e
    C = native.curvature_coefficient(e)
    adj = e.adjugate()
    principals = [sum((s.I*adj[mu, b]*GAMMA[b] for b in range(4)), s.zeros(4)) for mu in range(4)]
    for a, (T, S) in enumerate(zip(native.basis, native.spin)):
        equal(T.T*s.diag(-1, 1, 1, 1)+s.diag(-1, 1, 1, 1)*T, s.zeros(4))
        direction = (T*e).reshape(16, 1)
        ad = s.Matrix(6, 6, lambda i, j: native.structure.get((i, a, j), 0))
        dC = sum((direction[b]*C.diff(e[b]) for b in range(16)), s.zeros(6))
        equal(dC+ad.T*C, s.zeros(6))
        ddet = sum(direction[b]*s.diff(common.coframe.det, e[b]) for b in range(16))
        assert s.expand(ddet) == 0
        for mu in range(4):
            derivative = sum((direction[b]*principals[mu].diff(e[b]) for b in range(16)), s.zeros(4))
            equal(derivative-S*principals[mu]+principals[mu]*S, s.zeros(4))
        equal(S*s.diag(0, 0, 1, 1)-s.diag(0, 0, 1, 1)*S, s.zeros(4))
        gauge_direction = dict(zip(e, common.gauge.e))
        dK = sum((direction[b].xreplace(gauge_direction)*common.gauge.dkernel[b]
                  for b in range(16)), s.zeros(6))
        equal(dK, s.zeros(6))
    # The original four temporal coframe coordinates have identically zero
    # momenta, even before imposing matter equations or choosing multipliers.
    equal(common.coframe.G[:, [0, 4, 8, 12]], s.zeros(24, 4))
    # The full252 trace is an exact tensor identity, not a mode projection.
    V = s.Matrix(4, 4, s.symbols('V0:16'))
    psi = s.Matrix(s.symbols('psi0:4'))
    chi = s.Matrix(1, 4, s.symbols('chi0:4'))
    assert s.expand((chi*V*psi)[0]-s.trace(V*psi*chi)) == 0
    return {'six_Lorentz_generators': 6, 'generic_coframe_coordinates': 16,
            'gravity_curvature_coefficient_covariance': True,
            'all24_temporal_and_spatial_Dirac_principal_commutators': True,
            'original_full70_Yukawa_spin_covariance': True,
            'original_scalar_metric_and_gauge_Hodge_invariance': True,
            'four_temporal_coframe_momenta_identically_zero': True,
            'all63_internal_current_entries_retained_by_exact_tensor_trace': True}


def main():
    started = time.monotonic()
    model = SourceCoframeConstraints()
    generic = generic_Lorentz_invariance(model)
    print('PASS generic16 coframe Lorentz covariance, full Dirac/Yukawa and gauge/scalar invariance', flush=True)
    e = s.Matrix([[2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    e, de, phi, dphi, A, dA, psi, dpsi, chi = example_fields(e)
    p = clean(-s.I*chi*model.common.matter_data(e, phi, A)['E'])
    spatial_p = [s.zeros(1, 252) for _ in range(3)]
    chi, dpsi, dchi = model.on_matter_flow(e, de, phi, A, psi, p, dpsi[1:], spatial_p)
    dde = s.Matrix(4, 64, lambda mu, j: s.Rational((mu+j//16+1)*((j % 16) % 5-2), 71))
    result = model.euler(e, de, dde, phi, dphi, A, dA, psi, dpsi, chi, dchi)
    matter = model.common.matter_euler(e, de, phi, A, psi, chi, dpsi, dchi, result['connection'])
    equal(matter['primal'], s.zeros(252, 1))
    equal(matter['dual'], s.zeros(1, 252))
    equal(result['Lorentz_projection'], s.zeros(6, 1))
    # These entries were independently obtained using the frozen full252
    # Kronecker Euler API before the exact trace implementation was installed.
    original_temporal = s.Matrix([
        s.Rational(1195342188063870995180596002410949, 9533197473020403374941928852524),
        s.Rational(-550869137003074886934085186856609, 9533197473020403374941928852524),
        s.Rational(11005367351822660473627146891303, 560776321942376669114231108972),
        s.Rational(-74792296508996597041581459, 4714361256606374752031084)])
    equal(result['temporal_coframe'], original_temporal)
    print('PASS six Lorentz projections vanish on the actual full252 matter flow; four temporal constraints retained', flush=True)
    off_dpsi = [v.copy() for v in dpsi]
    off_dchi = [v.copy() for v in dchi]
    off_dpsi[0][5] += 1
    off_dchi[0][130] += s.I
    off = model.euler(e, de, dde, phi, dphi, A, dA, psi, off_dpsi, chi, off_dchi)
    off_matter = model.common.matter_euler(e, de, phi, A, psi, chi, off_dpsi, off_dchi, off['connection'])
    noether = []
    for S in model.common.coframe.lorentz.spin:
        spin = s.kronecker_product(S, s.eye(63))
        noether.append(real((off_matter['dual']*spin*psi-chi*spin*off_matter['primal'])[0]))
    equal(off['Lorentz_projection']+s.Matrix(noether), s.zeros(6, 1))
    assert off['Lorentz_projection'].todok()
    print('PASS complete off-shell Lorentz Noether identity with nonzero matter Euler terms', flush=True)
    paths = [HERE/name for name in ('source_coframe_constraints.py', 'source_common_hamiltonian.py',
        'source_common_hamiltonian.json', 'source_coframe_legendre.py', 'source_coframe_legendre.json',
        'source_lorentz_contact.py', 'source_lorentz_contact.json', 'source_gauge_legendre.py',
        'source_gauge_legendre.json', 'source_scalar_legendre.py', 'source_scalar_legendre.json')]
    output = {'root': ROOT_ID, 'source_sha256': model.common.scalar.exchange.vertices['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'scope': 'ORIGINAL_COMMON_COFRAME_PRIMARY_PRESERVATION_LORENTZ_NOETHER_AND_FOUR_TEMPORAL_CONSTRAINTS',
        'actual_API': 'SourceCoframeConstraints.{remaining_stress,lorentz_euler,euler,on_matter_flow}',
        'generic_source_identities': generic,
        'whole_Euler': 'original reduced gravity/Lorentz Euler plus all16 scalar, native gauge and remaining Omega=0 full252 Dirac density variations',
        'fixed_p_identity': 'the common fixed-p correction is proportional to the original independent-dual Euler; it vanishes on the generated matter flow used here',
        'Lorentz_Noether': '(T_a e).EL_e + Re(EL_psi S_a psi-chi S_a EL_chi)=0 after exact original Lorentz auxiliary elimination',
        'generic_Noether_derivation': 'the verified curvature coefficient covariance, original Dirac/spin commutators, Yukawa chirality commutation and scalar/gauge invariance cancel every constant local Lorentz term; the derivative-of-parameter term is exactly cancelled by the original connection variation delta Omega=[T,Omega]-dT. Integrating the original density by parts then gives the displayed Euler identity; the eliminated auxiliary Euler is identically zero.',
        'actual_all252_primal_and_dual_Euler_zero': True,
        'actual_all6_Lorentz_projection_zero': True,
        'off_shell_matter_terms_nonzero_and_exact': True,
        'temporal_constraints': encode(result['temporal_coframe']),
        'temporal_constraint_domain': 'these are four generated equations on initial canonical data; the deliberately arbitrary test data do not satisfy them',
        'coframe_acceleration_absent_from_temporal_constraints': True,
        'BF_boundary_flux': encode(result['boundary_flux']),
        'all_four_secondary_constraints_solved_or_preserved': False,
        'full_joint_Cauchy_or_quantum_spectrum_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_coframe_constraints.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')


if __name__ == '__main__':
    main()
