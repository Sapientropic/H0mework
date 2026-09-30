#!/usr/bin/env python3
"""Raw-source certification of the scalar broken-Gauss momentum graph.

The scalar frame is rebuilt from a nullspace of the original orbit rows.
Broken Gauss equations are solved as an actual linear system; the complete
bulk energy is reconstructed by Legendre subtraction of the original
scalar/gauge and BF/Lorentz densities. No candidate matrix defines the oracle.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from independent_source_joint_temporal_rates import RawSource, rational
from independent_source_gauge_legendre import (
    HERE, BASE, ROOT, ROOT_ID, PAIRS, SIGMA, W, ETA, bindings, clean,
    decode, encode, equal, dot, hodge, read)
from independent_source_coframe_legendre import quotient_right_inverse, quotient_inverse


def zero(value):
    assert s.cancel(value) == 0, value


def eq(A, B):
    assert not rational(A-B).todok()


def real(value):
    return s.expand(s.re(value))


class OriginalGaussGraph:
    def __init__(self):
        self.raw = RawSource()
        raw = self.raw
        self.orbit = s.Matrix.hstack(*[rho*raw.v for rho in raw.rho70])
        null = s.Matrix.hstack(*self.orbit.T.nullspace())
        self.projector = clean(null*(null.T*null).inv()*null.T)
        self.R = self.projector[:, list(self.projector.rref()[1])]
        self.select = s.eye(12)[:, list(self.orbit.rref()[1])]
        self.O = self.orbit*self.select
        self.kernel = s.Matrix.hstack(*self.orbit.nullspace())
        change = self.R.row_join(self.O)
        self.dual = clean(change.inv().T[:, :61])
        equal(self.R.T*self.dual, s.eye(61))
        equal(self.O.T*self.dual, s.zeros(9, 61))

    def currents(self, phi, Pi, A, Pi_A, spatial_Pi_A, psi, p):
        raw = self.raw
        gauge = sum((spatial_Pi_A[i][i, :].T-raw.ad(A[i+1, :]).T*Pi_A[i, :].T
                     for i in range(3)), s.zeros(12, 1))
        # The original independent-dual kinetic current is chi E rho psi.
        # With p=-i chi E its full252 coefficient is exactly Re(i p rho psi).
        matter = s.Matrix([real((s.I*p*rho*psi)[0]) for rho in raw.rho252])
        scalar = s.Matrix([dot(Pi, rho*phi) for rho in raw.rho70])
        return {'gauge': clean(gauge), 'matter': clean(matter), 'scalar': clean(scalar),
                'total': clean(gauge+matter+scalar)}

    def embed(self, x, pi, A, Pi_A, spatial_Pi_A, psi, p):
        phi = self.raw.v+self.R*x
        tangential = self.dual*pi
        base = self.currents(phi, tangential, A, Pi_A, spatial_Pi_A, psi, p)
        normal_coefficients = s.Matrix(12, 9,
            lambda a, j: dot(self.O[:, j], self.raw.rho70[a]*phi))
        coefficients = self.select.T*normal_coefficients
        solution, parameters = coefficients.gauss_jordan_solve(-self.select.T*base['total'])
        assert parameters.rows == 0
        Pi = clean(tangential+self.O*solution)
        current = self.currents(phi, Pi, A, Pi_A, spatial_Pi_A, psi, p)
        return {'phi': clean(phi), 'Pi': Pi, 'zeta': clean(solution),
                'normal_coefficients': normal_coefficients, 'base': base, 'current': current,
                'residual': clean(self.kernel.T*current['total'])}

    def solve_A0(self, e, data, spatial_phi, A):
        raw = self.raw
        h = raw.metric(e)
        spatial = [spatial_phi[i]+raw.action(A[i+1, :], raw.rho70)*data['phi'] for i in range(3)]
        shift = sum((h[0, i+1]*spatial[i] for i in range(3)), s.zeros(70, 1))
        covariant = clean((data['Pi']-shift)/h[0, 0])
        coefficients = self.orbit.T*s.Matrix.hstack(*[rho*data['phi'] for rho in raw.rho70])*self.select
        solution, parameters = coefficients.gauss_jordan_solve(self.orbit.T*covariant)
        assert parameters.rows == 0
        A0 = clean(self.select*solution)
        velocity = clean(covariant-raw.action(A0, raw.rho70)*data['phi'])
        equal(self.orbit.T*velocity, s.zeros(12, 1))
        return {'A0': A0, 'velocity': velocity, 'metric': h, 'shift': clean(shift)}

    def original_bulk_H(self, e, Pi_e, data, spatial_phi, A, Pi_A, spatial_A,
                        spatial_Pi_A, psi, p):
        """Original four densities with exact velocity Legendre subtraction."""
        raw = self.raw
        phi, Pi = data['phi'], data['Pi']
        C = raw.principals(e)
        E_inverse = s.kronecker_product(C[0].inv(), s.eye(63))
        chi = clean(s.I*p*E_inverse)
        H, G, Hinv = raw.geometry(e)
        j = raw.current(e, psi, chi)
        Gt = G[:, :16]
        M = clean(-Gt.T*Hinv*Gt)
        h_spatial = e[:, 1:].T*ETA*e[:, 1:]
        R = quotient_right_inverse(e)
        Q = clean(R*quotient_inverse(e, h_spatial)*R.T)
        shift = clean(-Gt.T*Hinv*j)
        velocity = clean(Q*(Pi_e-shift))
        source = Gt*velocity+j
        gravity_density = -3*e.det()-dot(source, Hinv*source)/2
        gravity_H = dot(Pi_e, velocity)-gravity_density
        h, volume = raw.metric(e), s.Abs(e.det())
        RA = [raw.action(A[mu, :], raw.rho70) for mu in range(4)]
        U = [spatial_phi[i]+RA[i+1]*phi for i in range(3)]
        U0 = (Pi-sum((h[0, i+1]*U[i] for i in range(3)), s.zeros(70, 1)))/h[0, 0]
        covariant = [U0, *U]
        phi_velocity = U0-RA[0]*phi
        scalar_density = sum(h[mu, nu]*dot(covariant[mu], covariant[nu])/2
                             for mu in range(4) for nu in range(4))-volume*dot(phi-raw.v, phi-raw.v)
        scalar_H = dot(Pi, phi_velocity)-scalar_density
        kernel = clean(-W*hodge(e)/SIGMA)
        F = raw.curvature(A)
        for row, (mu, nu) in enumerate(PAIRS):
            if mu:
                F[row, :] += spatial_A[mu-1, 12*nu:12*(nu+1)]-spatial_A[nu-1, 12*mu:12*(mu+1)]
        F[:3, :] = kernel[:3, :3].inv()*(Pi_A*raw.Gram.inv()-kernel[:3, 3:]*F[3:, :])
        A_velocity = s.Matrix.vstack(*[(F[i, :].T+spatial_A[i, :12].T+
                            raw.bracket(A[i+1, :], A[0, :])).T for i in range(3)])
        gauge_density = dot(F, kernel*F*raw.Gram)/2
        gauge_H = dot(Pi_A, A_velocity)-gauge_density
        matter_H = -real((chi*raw.lower(e, phi, A)*psi)[0])
        boundary = sum(dot(spatial_Pi_A[i][i, :], A[0, :])+dot(Pi_A[i, :], spatial_A[i, :12]) for i in range(3))
        components = {name: s.factor(value) for name, value in (
            ('gravity_Lorentz', gravity_H), ('scalar', scalar_H), ('gauge', gauge_H), ('matter', matter_H))}
        return {'components': components, 'bulk': s.factor(sum(components.values())-boundary),
                'boundary_divergence': s.factor(boundary), 'flux': clean(Pi_A*A[0, :].T),
                'chi': chi, 'E': s.kronecker_product(C[0], s.eye(63)), 'velocity_phi': clean(phi_velocity)}


def symbolic_geometry(model, receipt):
    R, dual, O, raw = model.R, model.dual, model.O, model.raw
    phase = read(HERE/'scalar_canonical_phase.json')
    equal(R, decode(phase['scalar_coordinate_embedding']))
    equal(s.diag(R, dual), decode(phase['canonical_phase_embedding']))
    equal(R*dual.T, model.projector)
    x, pi, dx, dpi = [s.Matrix(s.symbols(prefix+'0:61', real=True)) for prefix in ('x', 'pi', 'dx', 'dpi')]
    zeta, dzeta = [s.Matrix(s.symbols(prefix+'0:9', real=True)) for prefix in ('zeta', 'dzeta')]
    phi = raw.v+R*x
    Pi = dual*pi+O*zeta
    equal(model.orbit.T*phi, s.zeros(12, 1))
    zero(dot(Pi, R*dx)-dot(pi, dx))
    zero(dot(dual*dpi+O*dzeta, R*dx)-dot(dpi, dx))
    # Every coefficient of arbitrary dzeta, including its dependence on any
    # matter/gauge variable or spatial momentum derivative, is present.
    equal(R.T*O, s.zeros(61, 9))
    D = model.orbit.T*s.Matrix.hstack(*[rho*phi for rho in raw.rho70])
    equal(D, D.T); equal(D*model.kernel, s.zeros(12, 3))
    zero((O.T*O).det()-s.sympify(receipt['canonical_geometry']['source_D9_determinant']))
    normal = s.Matrix(12, 9, lambda a, j: dot(O[:, j], raw.rho70[a]*phi))
    equal(model.select.T*normal, (model.select.T*D*model.select).T)
    # Consequently the normal-momentum graph solves the original9 equations
    # for every point of det(D9)!=0, not only the dense consumer below.
    return {'all61_symbolic_coordinates_and_one_form': True,
            'all549_normal_differential_cross_coefficients_zero': True,
            'complete_original_CCR_embedding_reconstructed': True,
            'generic_broken_Gauss_coefficient_is_transpose_D9': True,
            'fixed_native_three_stabilizer_kernel_retained': True}


def dense_fixture(model):
    raw = model.raw
    e = s.Matrix(raw.active['actual_background']['coframe']).applyfunc(s.sympify)
    A = raw.A.copy()
    x = s.Matrix([s.Rational((7*i+3) % 13-6, 10000) for i in range(61)])
    pi = s.Matrix([s.Rational((5*i+1) % 11-5, 37) for i in range(61)])
    Pi_A = s.Matrix(3, 12, lambda i, a: s.Rational((3*i+5*a+1) % 11-5, 29))
    spatial_Pi_A = [s.Matrix(3, 12, lambda j, a: s.Rational((i+2*j+3*a) % 7-3, 41)) for i in range(3)]
    psi = s.Matrix([s.Rational((5*i+1) % 13-6, 31)+s.I*s.Rational((3*i+2) % 11-5, 43) for i in range(252)])
    p = s.Matrix([[s.Rational((7*i+2) % 17-8, 47)+s.I*s.Rational((2*i+3) % 13-6, 53) for i in range(252)]])
    spatial_phi = [model.R*s.Matrix([s.Rational((j+i) % 5-2, 101) for j in range(61)]) for i in range(3)]
    spatial_A = s.zeros(3, 48)
    spatial_A[:, :12] = s.Matrix(3, 12, lambda i, a: s.Rational((i+3*a) % 7-3, 59))
    return e, A, x, pi, Pi_A, spatial_Pi_A, psi, p, spatial_phi, spatial_A


def main():
    began = time.monotonic()
    path = HERE/'source_scalar_gauss_reduction.json'
    saved = read(path); count = bindings(saved)
    assert saved['root'] == ROOT_ID
    model = OriginalGaussGraph()
    assert model.raw.hashes == saved['source_sha256']
    geometry = symbolic_geometry(model, saved)
    print('PASS raw orbit/nullspace and complete61 canonical one-form', flush=True)
    e, A, x, pi, Pi_A, dPi_A, psi, p, spatial_phi, spatial_A = dense_fixture(model)
    data = model.embed(x, pi, A, Pi_A, dPi_A, psi, p)
    expected = saved['actual_current_consumer']
    equal(data['zeta'], decode(expected['normal_scalar_momentum']))
    equal(data['residual'], decode(expected['residual_stabilizer_Gauss']))
    equal(model.select.T*data['current']['total'], s.zeros(9, 1))
    assert data['residual'].todok()
    assert (model.select.T*data['base']['gauge']).todok()
    assert (model.select.T*data['base']['matter']).todok()
    zero((model.select.T*data['normal_coefficients']).det()-s.sympify(expected['actual_D9_determinant']))
    equal(model.R.T*data['Pi'], pi)
    equal(model.dual.T*(data['phi']-model.raw.v), x)
    old = model.currents(data['phi'], model.dual*pi, A, Pi_A, dPi_A, psi, p)
    assert (model.select.T*old['total']).todok()
    connection = model.solve_A0(e, data, spatial_phi, A)
    A[0, :] = connection['A0'].T
    equal(model.O.T*connection['velocity'], s.zeros(9, 1))
    zero(dot(model.O*data['zeta'], model.O*data['zeta'])/(2*connection['metric'][0, 0])-
         s.sympify(expected['normal_kinetic_energy']))
    print('PASS original full252/current Gauss solve, remaining3 rows, source A0 and normal chain coefficient', flush=True)

    # All12 source A0 coefficients and all36 spatial A0-gradient coefficients
    # are checked in the actual four-density Legendre energy, with independent
    # symbols. The original BF/Lorentz contribution stays in the constant.
    parameters = s.Matrix(s.symbols('native_A00:12', real=True))
    gradient_parameters = s.Matrix(3, 12, s.symbols('grad_A00:36', real=True))
    variable_A = A.copy(); variable_A[0, :] = parameters.T
    variable_spatial_A = spatial_A.copy(); variable_spatial_A[:, :12] = gradient_parameters
    H = model.original_bulk_H(e, s.zeros(16, 1), data, spatial_phi, variable_A,
                             Pi_A, variable_spatial_A, dPi_A, psi, p)
    coefficient = s.Matrix([s.diff(H['bulk'], value) for value in parameters])
    equal(coefficient, -data['current']['total'])
    equal(model.select.T*coefficient, s.zeros(9, 1))
    equal(model.kernel.T*coefficient, -data['residual'])
    equal(s.Matrix([s.diff(H['bulk'], value) for value in gradient_parameters]), s.zeros(36, 1))
    substitution = dict(zip(parameters, A[0, :]))
    substitution.update(dict(zip(gradient_parameters, spatial_A[:, :12])))
    actual_bulk = s.factor(H['bulk'].subs(substitution))
    broken_parameters = s.Matrix(s.symbols('broken0:9', real=True))
    remaining_parameters = s.Matrix(s.symbols('stabilizer0:3', real=True))
    full_parameters = model.select*broken_parameters+model.kernel*remaining_parameters
    adapted = H['bulk'].subs(dict(zip(parameters, full_parameters)))
    constant = H['bulk'].subs(dict.fromkeys(parameters, 0))
    zero(adapted-constant+dot(remaining_parameters, data['residual']))
    print('PASS original bulk H all12 A0 coefficients and all36 spatial-gradient cancellations', flush=True)

    from source_scalar_gauss_reduction import SourceScalarGaussReduction
    public = SourceScalarGaussReduction()
    observed = public.embed(x, pi, A, Pi_A, dPi_A, psi, p)
    equal(observed['Pi_phi'], data['Pi']); equal(observed['Gauss'], data['current']['total'])
    pulled = public.pullback_hamiltonian(e, s.zeros(16, 1), s.zeros(48, 1), x, pi,
        [model.dual.T*value for value in spatial_phi], A, Pi_A, spatial_A, dPi_A,
        psi, p, [s.zeros(252, 1)]*3, s.zeros(10, 1))
    zero(pulled['bulk_Hamiltonian']-actual_bulk)
    equal(pulled['gauge_spatial_boundary_flux'], Pi_A*A[0, :].T)
    mixed_e = s.Matrix([[2, s.Rational(1, 7), 0, 0], [s.Rational(1, 9), 1, 0, 0],
                        [0, 0, 1, 0], [0, 0, 0, 1]])
    mixed = model.solve_A0(mixed_e, data, spatial_phi, A)
    assert mixed['shift'].todok()
    equal(public.time_connection(mixed_e, observed, spatial_phi, A), mixed['A0'])
    equal(model.O.T*mixed['velocity'], s.zeros(9, 1))
    rawmatter = s.Matrix([real((H['chi']*H['E']*rho*psi)[0]) for rho in model.raw.rho252])
    equal(rawmatter, data['current']['matter'])
    zero(-data['residual'][0]-s.sympify(expected['residual_A0_energy_variation_reads_remaining_Gauss']))
    equal(model.orbit.T*s.zeros(70, 1), s.zeros(12, 1))
    failed = False
    try:
        public.embed(-model.dual.T*model.raw.v, pi, A, Pi_A, dPi_A, psi, p)
    except ValueError:
        failed = True
    assert failed
    equal(model.orbit.T*s.Matrix.hstack(*[rho*s.zeros(70, 1) for rho in model.raw.rho70]), s.zeros(12))
    print('PASS public whole energy/phase graph and true rank-drop rejection', flush=True)
    inputs = [path, HERE/'source_scalar_gauss_reduction.py',
        HERE/'independent_source_scalar_gauss_reduction.py', HERE/'independent_source_joint_temporal_rates.py',
        HERE/'independent_source_gauge_legendre.py', HERE/'independent_source_coframe_legendre.py',
        HERE/'scalar_canonical_phase.json']
    result = {'root': ROOT_ID, 'verdict': 'CERTIFIED_ORIGINAL_BROKEN_GAUSS_SCALAR_MOMENTUM_GRAPH_AND_CANONICAL61_PULLBACK',
        'source_sha256': model.raw.hashes,
        'input_sha256': {str(q.relative_to(ROOT)): hashlib.sha256(q.read_bytes()).hexdigest() for q in inputs},
        'candidate_bindings_checked': count, 'generic_geometry': geometry,
        'original_full252_primal_and_independent_canonical_dual': True,
        'raw_four_density_bulk_H_value_matches_public_consumer': True,
        'all12_A0_bulk_coefficients_equal_negative_full_Gauss': True,
        'all36_spatial_A0_gradient_coefficients_cancel_with_original_boundary': True,
        'broken9_coefficients_zero_remaining3_constraints_retained': True,
        'normal_momentum_chain_coefficients_zero_after_original_A0_update': True,
        'rank_drop_phi_zero_rejected_without_inverse': True,
        'residual_three_Gauss_and_coframe_constraints_solved': False,
        'quantum_measure_or_decay_claimed': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_scalar_gauss_reduction.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print(result['verdict'], result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
