#!/usr/bin/env python3
"""Raw Palatini/torsion certification of the18 spatial Lorentz time rows.

The forcing is assembled by differentiating the original torsion with
independent symmetric second spatial jets, plus direct coframe variations of
the original densities. A single direct18-row solve replaces the candidate's
right-inverse/kernel decomposition.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from independent_source_spatial_time_coframe import RawCoordinateDensity
from independent_source_lorentz_contact import (
    torsion_maps, exterior, J, WEDGE, GENERATORS, SIGNS, geometric_load)
from independent_source_coframe_legendre import (
    original_geometry, quotient_right_inverse, quotient_inverse, metric_coordinates)
from independent_source_joint_temporal_rates import (
    HERE, BASE, ROOT, ROOT_ID, PAIRS, SIGMA, ETA, bindings, clean, decode, encode, equal, eq, zero, dot, read)

SPATIAL_ROWS = [6*a+p for a in range(4) for p in range(3, 6)]


def diff_at(M, variables, e, direction):
    result = sum((direction[j]*M.diff(variables[j]) for j in range(16)), s.zeros(*M.shape))
    return clean(result.xreplace(dict(zip(variables, e))))


class OriginalLorentzTime:
    def __init__(self):
        self.coordinate = RawCoordinateDensity()
        self.raw = self.coordinate.raw
        self.e = self.raw.eg
        self.T, self.curl = torsion_maps(self.e)
        self.C = J*exterior(self.e)*WEDGE

    def at(self, M, e):
        return clean(M.xreplace(dict(zip(self.e, e))))

    def geometry(self, e):
        H, G, inverse = self.raw.geometry(e)
        T = self.at(self.T, e)
        R = quotient_right_inverse(e)
        # Direct differentiation of the original B(e) wedge dOmega density.
        # Its18 time-curvature columns are independent of candidate Gt.
        E = s.Matrix(16, 18, lambda j, column:
            s.diff(self.C[column % 6, column//6], self.e[j]).xreplace(dict(zip(self.e, e))))
        L = clean(R.T*E)
        Tsp = T.extract(SPATIAL_ROWS, range(6, 24))
        M = clean(Tsp.col_join(L))
        inverse18 = clean(M.inv(method='DM'))
        return {'H': H, 'G': G, 'Hinv': inverse, 'T': T, 'R': R,
                'Euler_time_coefficient': E, 'L': L, 'Tsp': Tsp, 'M': M, 'inverse': inverse18}

    def current_and_derivative(self, e, psi, chi, direction=None, dpsi=None, dchi=None):
        C = self.raw.principals(e)
        density = self.raw.density(psi, chi)
        current = s.Matrix([s.re(s.trace(C[mu]*S*density)).expand() for mu in range(4) for S in self.raw.spin])
        if direction is None:
            return clean(current)
        _, dC, _ = self.raw.coefficient_derivatives(e, direction)
        ddensity = self.raw.density(dpsi, chi)+self.raw.density(psi, dchi)
        derivative = s.Matrix([s.re(s.trace(dC[mu]*S*density+C[mu]*S*ddensity)).expand()
                                for mu in range(4) for S in self.raw.spin])
        return clean(derivative)

    def torsion_source(self, e, psi, chi, direction=None, dpsi=None, dchi=None):
        H, _, _ = self.raw.geometry(e)
        T = self.at(self.T, e)
        j = self.current_and_derivative(e, psi, chi)
        omega_current, free = H.gauss_jordan_solve(-j)
        assert free.rows == 0
        if direction is None:
            return clean(T*omega_current)
        dH = diff_at(self.raw.Hsymbol, self.e, e, direction)
        dT = diff_at(self.T, self.e, e, direction)
        dj = self.current_and_derivative(e, psi, chi, direction, dpsi, dchi)
        rate, free = H.gauss_jordan_solve(-dj-dH*omega_current)
        assert free.rows == 0
        return clean(dT*omega_current+T*rate)

    @staticmethod
    def pair(source, mu, nu):
        if (mu, nu) in PAIRS:
            p, sign = PAIRS.index((mu, nu)), 1
        else:
            p, sign = PAIRS.index((nu, mu)), -1
        return s.Matrix([sign*source[6*a+p] for a in range(4)])

    @staticmethod
    def matrices(omega):
        return [clean(sum((omega[6*mu+a]*GENERATORS[a] for a in range(6)), s.zeros(4))) for mu in range(4)]

    def matter_time(self, e, de, phi, A, omega, psi, chi, dpsi_space, dchi_space):
        C4 = self.raw.principals(e)
        C = [s.kronecker_product(M, s.eye(63)) for M in C4]
        K = self.raw.lower(e, phi, A, omega)
        inverse = s.kronecker_product(C4[0].inv(), s.eye(63))
        psi_dot = clean(inverse*(-K*psi-sum((C[i+1]*dpsi_space[i] for i in range(3)), s.zeros(252, 1))))
        divergence = sum((s.kronecker_product(self.raw.coefficient_derivatives(e, de[mu])[1][mu], s.eye(63))
                          for mu in range(4)), s.zeros(252))
        rhs = chi*K-chi*divergence-sum((dchi_space[i]*C[i+1] for i in range(3)), s.zeros(1, 252))
        chi_dot = clean(rhs*inverse)
        eq(C[0]*psi_dot+K*psi+sum((C[i+1]*dpsi_space[i] for i in range(3)), s.zeros(252, 1)), s.zeros(252, 1))
        eq(chi*K-chi*divergence-chi_dot*C[0]-sum((dchi_space[i]*C[i+1] for i in range(3)), s.zeros(1, 252)), s.zeros(1, 252))
        return clean(psi_dot), chi_dot

    def Euler(self, e, phi, U, A, F, omega, domega_space, omega_time, psi, chi, dpsi):
        Om = self.matrices(omega)
        curv = s.zeros(6)
        for column, (mu, nu) in enumerate(PAIRS):
            bracket = Om[mu]*Om[nu]-Om[nu]*Om[mu]
            curv[:, column] = s.Matrix([SIGNS[a]*bracket[a, b] for a, b in PAIRS])
            curv[:, column] += (omega_time[6*nu:6*(nu+1), :] if mu == 0 else domega_space[mu-1][6*nu:6*(nu+1), :])
            curv[:, column] -= (omega_time[6*mu:6*(mu+1), :] if nu == 0 else domega_space[nu-1][6*mu:6*(mu+1), :])
        covariant = []
        for mu in range(4):
            spin = sum((omega[6*mu+a]*self.raw.spin[a] for a in range(6)), s.zeros(4))
            covariant.append(dpsi[mu]+(s.kronecker_product(spin, s.eye(63))+
                self.raw.action(A[mu, :], self.raw.rho252))*psi)
        density = [self.raw.density(v, chi) for v in covariant]
        yukawa = s.re((chi*self.raw.yukawa(phi)*psi)[0]).expand()
        rows = []
        for j in range(16):
            direction = s.zeros(4); direction[j] = 1
            dvol, dC, dh = self.raw.coefficient_derivatives(e, direction)
            ddet = e.adjugate()[j % 4, j//4]
            dBF = self.at(self.C.diff(self.e[j]), e)
            gravity = -3*ddet+dot(dBF, curv)
            scalar = sum(dh[mu, nu]*dot(U[mu], U[nu])/2 for mu in range(4) for nu in range(4))
            # Keep the original potential and its independent matter source.
            scalar -= dvol*dot(phi-self.raw.v, phi-self.raw.v)
            gauge = dot(F, self.coordinate.kernel_dot(e, direction)*F*self.raw.Gram)/2
            matter = dvol*yukawa+sum(s.re(s.trace(dC[mu]*density[mu])) for mu in range(4))
            rows.append(s.expand(gravity+scalar+gauge+matter))
        return clean(s.Matrix(rows))

    def evolve(self, e, spatial_e, omega, spatial_omega, phi, U, A, F, spatial_F,
               psi, chi, spatial_psi, spatial_chi):
        equal(omega[:6, :], s.zeros(6, 1))
        for value in spatial_omega: equal(value[:6, :], s.zeros(6, 1))
        data = self.geometry(e)
        S = self.torsion_source(e, psi, chi)
        torsion_connection = data['T']*omega
        velocity = s.zeros(4)
        for a in range(4):
            for i in range(1, 4):
                row = 6*a+PAIRS.index((0, i))
                velocity[a, i] = S[row]-torsion_connection[row]+spatial_e[i-1][a, 0]
        clock = self.coordinate.solve(e, velocity, spatial_e, A, F, spatial_F, phi, U, psi, chi)
        velocity[:, 0] = clock['rates']
        de = [velocity, *spatial_e]
        psi_dot, chi_dot = self.matter_time(e, de, phi, A, omega, psi, chi, spatial_psi, spatial_chi)
        dpsi, dchi = [psi_dot, *spatial_psi], [chi_dot, *spatial_chi]
        dS = [self.torsion_source(e, psi, chi, de[mu], dpsi[mu], dchi[mu]) for mu in range(4)]
        O, dO = self.matrices(omega), [self.matrices(v) for v in spatial_omega]
        # Do not cancel the symmetric second jets by hand: insert all24
        # independent ones before differentiating the original torsion rows.
        second = {(a, i, j): s.Symbol(f'd2etime_{a}_{i}_{j}', real=True)
                  for a in range(4) for i in range(1, 4) for j in range(i, 4)}
        dv = [s.zeros(4) for _ in range(3)]
        for i in range(1, 4):
            for j in range(1, 4):
                value = (-dO[i-1][0]*e[:, j]-O[0]*spatial_e[i-1][:, j]+
                         dO[i-1][j]*e[:, 0]+O[j]*spatial_e[i-1][:, 0]+self.pair(dS[i], 0, j))
                value += s.Matrix([second[a, min(i, j), max(i, j)] for a in range(4)])
                dv[i-1][:, j] = value
        unknown = s.Matrix(s.symbols('original_Omega_space_rate0:18', real=True))
        dotomega = s.zeros(6, 1).col_join(unknown); Otime = self.matrices(dotomega)
        torsion_derivative = []
        for a in range(4):
            for i, j in PAIRS[3:]:
                row = dv[i-1][:, j]-dv[j-1][:, i]+Otime[i]*e[:, j]-Otime[j]*e[:, i]
                row += O[i]*velocity[:, j]-O[j]*velocity[:, i]-self.pair(dS[0], i, j)
                torsion_derivative.append(s.expand(row[a]))
        for value in torsion_derivative:
            assert not value.has(*second.values())
        force = self.Euler(e, phi, U, A, F, omega, spatial_omega, dotomega, psi, chi, dpsi)
        equations = torsion_derivative+list(data['R'].T*force)
        matrix, rhs = s.linear_eq_to_matrix(equations, list(unknown))
        eq(matrix, data['M'])
        solution, free = matrix.gauss_jordan_solve(rhs)
        assert free.rows == 0
        replacement = dict(zip(unknown, solution))
        full_Euler = clean(force.subs(replacement))
        equal(s.Matrix(torsion_derivative).subs(replacement), s.zeros(12, 1))
        equal(data['R'].T*full_Euler, s.zeros(6, 1))
        initial = clean(data['T']*omega+self.curl*s.Matrix.vstack(*[v.reshape(16, 1) for v in de])-S)
        for i in range(3):
            dT = diff_at(self.T, self.e, e, spatial_e[i])
            prolonged = clean(dT*omega+data['T']*spatial_omega[i]-dS[i+1])
            equal(prolonged[SPATIAL_ROWS, :], s.zeros(12, 1))
        return {'rate': clean(solution), 'e_rate': clean(velocity), 'psi_rate': psi_dot, 'chi_rate': chi_dot,
                'matrix': clean(matrix), 'rhs': clean(rhs), 'Euler': full_Euler,
                'torsion': initial, 'time4': clock, 'second_spatial_symbols_cancelled': len(second)}


def verify_generic(model, saved):
    e = model.e
    det = s.expand(e.det())
    X = exterior(e)
    flat = model.at(model.T, s.eye(4))
    equal(model.T*s.kronecker_product(e.T, s.eye(6)), s.kronecker_product(s.eye(4), X.T)*flat)
    assert flat.det() != 0
    assert str(flat.det()) == saved['generic_original_principal_inverse']['original_flat_torsion_determinant']
    equal(X.T*exterior(e.adjugate().T), det**2*s.eye(6))
    equal(model.T.extract(SPATIAL_ROWS, range(6)), s.zeros(12, 6))
    transform = s.kronecker_product(e, s.eye(6))
    Knum = clean(transform.T*model.raw.flat_inverse*transform)
    G = model.raw.Gsymbol; Gt = G[:, :16]
    equal(model.T*Knum*G, det*model.curl)
    equal(model.curl.extract(SPATIAL_ROWS, range(16)), s.zeros(12, 16))
    equal(Gt[:6, :], s.zeros(6, 16))
    h = e[:, 1:].T*ETA*e[:, 1:]
    Dh = metric_coordinates(h).jacobian(list(e))
    hs = s.Matrix(s.symbols('metric0:6', real=True))
    from independent_source_coframe_legendre import metric_matrix, metric_covector
    Hmetric = metric_matrix(hs)
    Hessian = s.hessian(Hmetric.det(), list(hs))
    inv_num = s.Matrix.hstack(*[metric_coordinates(s.trace(metric_covector(s.eye(6)[:, j])*Hmetric)*Hmetric/2-
                                      Hmetric*metric_covector(s.eye(6)[:, j])*Hmetric) for j in range(6)])
    equal(Hessian*inv_num, Hmetric.det()*s.eye(6))
    zero(Hessian.det()+16*Hmetric.det()**2)
    Bnum = clean(Hessian.xreplace(dict(zip(hs, metric_coordinates(h)))))
    equal(-4*Gt.T*Knum*Gt, Dh.T*Bnum*Dh)
    Rnum = s.Matrix.hstack(*[(s.zeros(4, 1).row_join(ETA*e.adjugate()[1:, :].T*metric_matrix(s.eye(6)[:, j])/2)).reshape(16, 1) for j in range(6)])
    equal(Dh*Rnum, det*s.eye(6))
    for j in range(16):
        coeff = s.Matrix([s.diff(model.C[a, i], e[j]) for i in range(3) for a in range(6)])
        equal(coeff, -Gt[6:, j])
    return {'all16_raw_coframe_variables': True, 'original_epsilon_torsion_covariance': True,
            'cofactor_wedge_inverse_identity': True, 'full_Cartan_identity_without_denominators': True,
            'original_metric_Hessian_and_its_inverse_numerator': True,
            'metric_right_inverse_and_full18_principal_bridge': True,
            'generic_inverse_argument': 'The original full torsion covariance gives a right inverse for Tsp because its Omega0 columns vanish. The Cartan identity puts (-H^-1 Gt Rh)_sp in ker Tsp, and the checked metric identity gives L times this kernel=-B6. det B6!=0 when det h!=0, so the displayed18-row inverse follows on the whole original noncharacteristic chart.'}


def homogeneous_fixture(model):
    old = read(HERE/'source_homogeneous_canonical_flow.json')
    f = {k: decode(v) for k, v in old['datum'].items()}
    raw = model.raw
    e, phi, A, psi = [f[k] for k in ('e', 'phi', 'A', 'psi')]
    C0 = s.kronecker_product(raw.principals(e)[0], s.eye(63))
    chi = clean(s.I*f['p']*C0.inv())
    omega = decode(old['source_Lorentz_connection'])
    K = model.coordinate.kernel(e)
    F = raw.curvature(A)
    F[:3, :] = clean(K[:3, :3].inv()*(f['Pi_A']*raw.Gram.inv()-K[:3, 3:]*F[3:, :]))
    h = raw.metric(e)
    Usp = [raw.action(A[i+1, :], raw.rho70)*phi for i in range(3)]
    U0 = clean((f['Pi_phi']-sum((h[0, i+1]*Usp[i] for i in range(3)), s.zeros(70, 1)))/h[0, 0])
    args = (e, [s.zeros(4)]*3, omega, [s.zeros(24, 1)]*3, phi, [U0, *Usp], A, F,
            [s.zeros(6, 12)]*3, psi, chi, [s.zeros(252, 1)]*3, [s.zeros(1, 252)]*3)
    return old, f, args


def main():
    began = time.monotonic()
    path = HERE/'source_spatial_lorentz_time.json'; saved = read(path); count = bindings(saved)
    assert saved['root'] == ROOT_ID and saved['general_spatial_Cauchy_closed'] is False
    model = OriginalLorentzTime()
    generic = verify_generic(model, saved)
    actual_inverse = []
    for row in saved['actual_inverse_consumers']:
        e = decode(row['coframe']); data = model.geometry(e)
        equal(data['M'], decode(row['time_matrix'])); equal(data['inverse'], decode(row['time_inverse']))
        equal(data['M']*data['inverse'], s.eye(18)); equal(data['inverse']*data['M'], s.eye(18))
        zero(data['M'].det()-s.sympify(row['determinant']))
        h = e[:, 1:].T*ETA*e[:, 1:]
        B_inv = quotient_inverse(e, h)
        Gt = data['G'][:, :16]
        B = clean(-data['R'].T*Gt.T*data['Hinv']*Gt*data['R'])
        equal(B*B_inv, s.eye(6)); equal(B_inv*B, s.eye(6))
        actual_inverse.append({'determinant': str(data['M'].det()), 'all18_direct_linear_solve_columns': True})
    print('PASS original generic Tor/Cartan/B6 and direct18 inverse at both frames', flush=True)
    old, f, args = homogeneous_fixture(model)
    actual = model.evolve(*args)
    expected = saved['actual_original_flow_consumer']
    equal(actual['rate'], decode(expected['Omega_spatial_rate']))
    equal(actual['time4']['rates'], decode(expected['time4_rates']))
    rates = {k: decode(v) for k, v in old['complete_rates'].items()}
    equal(actual['e_rate'], rates['e']); equal(actual['psi_rate'], rates['psi'])
    e, _, omega, _, phi, U, A, F, _, psi, chi, _, _ = args
    dE = s.kronecker_product(model.raw.coefficient_derivatives(e, rates['e'])[1][0], s.eye(63))
    Einv = s.kronecker_product(model.raw.principals(e)[0].inv(), s.eye(63))
    expected_chi = clean((s.I*rates['p']-chi*dE)*Einv)
    equal(actual['chi_rate'], expected_chi)
    equal(actual['Euler'], s.zeros(16, 1)); equal(actual['torsion'], s.zeros(24, 1))
    H, G, _ = model.raw.geometry(e)
    dH = diff_at(model.raw.Hsymbol, model.e, e, rates['e'])
    dG = diff_at(model.raw.Gsymbol, model.e, e, rates['e'])
    dj = model.current_and_derivative(e, psi, chi, rates['e'], rates['psi'], expected_chi)
    acceleration = decode(old['original_Euler_consumer']['nonzero_spatial_coframe_acceleration'])
    de = rates['e'].reshape(16, 1).col_join(s.zeros(48, 1))
    dde = acceleration.col_join(s.zeros(48, 1))
    omega_derivative, free = H.gauss_jordan_solve(-dH*omega-dG*de-G*dde-dj)
    assert free.rows == 0
    equal(omega_derivative[6:, :], actual['rate'])
    print('PASS independent original homogeneous flow, full252 dual chain, all16 Euler and differentiated18 auxiliary rates', flush=True)
    record = saved['actual_spatial_first_jet_consumer']
    fields = {k: [decode(x) for x in v] if isinstance(v, list) else decode(v) for k, v in record['fields'].items()}
    keys = ('e', 'spatial_e', 'Omega', 'spatial_Omega', 'phi', 'U', 'A', 'F', 'spatial_F', 'psi', 'chi', 'spatial_psi', 'spatial_chi')
    spatial = model.evolve(*[fields[k] for k in keys])
    equal(spatial['rate'], decode(record['Omega_spatial_rate']))
    equal(spatial['time4']['rates'], decode(record['time4_rates']))
    residual4 = spatial['Euler'].extract([0, 4, 8, 12], [0])
    equal(residual4, decode(record['remaining_original_time_coframe_Euler']))
    assert residual4.todok()
    equal(spatial['torsion'], s.zeros(24, 1))
    e = fields['e']; data = model.geometry(e)
    Z = s.Matrix.hstack(*[(T*e).reshape(16, 1) for T in GENERATORS])
    equal(Z.T*spatial['Euler'], s.zeros(6, 1))
    frame = s.eye(16)[[0, 4, 8, 12], :].col_join(data['R'].T).col_join(Z.T)
    assert frame.det() != 0
    full_expected, free = frame.gauss_jordan_solve(residual4.col_join(s.zeros(12, 1)))
    assert free.rows == 0
    equal(full_expected, spatial['Euler'])
    de = spatial['e_rate'].reshape(16, 1).col_join(s.Matrix.vstack(*[value.reshape(16, 1) for value in fields['spatial_e']]))
    equal(data['H']*fields['Omega']+data['G']*de+model.current_and_derivative(e, fields['psi'], fields['chi']), s.zeros(24, 1))
    dS = [model.torsion_source(e, fields['psi'], fields['chi'], fields['spatial_e'][i], fields['spatial_psi'][i], fields['spatial_chi'][i]) for i in range(3)]
    omitted = s.Matrix([model.pair(dS[i-1], 0, j)[a]-model.pair(dS[j-1], 0, i)[a]
                        for a in range(4) for i, j in PAIRS[3:]])
    assert clean(omitted).todok()
    print('PASS nonzero spatial whole jets: original24 Lorentz/6Spin, all18 rates,36 spatial+12 time torsion rows and retainedtime4 residual', flush=True)
    paths = [path, HERE/'source_spatial_lorentz_time.py', HERE/'independent_source_spatial_lorentz_time.py',
        HERE/'independent_source_spatial_time_coframe.py', HERE/'independent_source_spatial_time_coframe.json',
        HERE/'independent_source_joint_temporal_rates.py', HERE/'independent_source_lorentz_contact.py',
        HERE/'independent_source_coframe_legendre.py', HERE/'source_homogeneous_canonical_flow.json']
    result = {'root': ROOT_ID,
        'verdict': 'CERTIFIED_ORIGINAL_SPATIAL_LORENTZ18_INVERSE_AND_ACTUAL_FIRST_SPATIAL_JET_UPDATE',
        'source_sha256': model.raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'candidate_bindings_checked': count, 'generic_original_geometry': generic,
        'actual_direct_inverse_consumers': actual_inverse,
        'homogeneous_original_flow': {'all16_coframe_Euler_zero': True, 'full252_primal_and_dual_correct': True,
            'original_auxiliary_time_derivative_equals_all18_generated_rates': True},
        'nonzero_spatial_first_jet': {'all18_spatial_Lorentz_rates_from_direct_original_equations': True,
            'all24_original_Lorentz_Euler_and6_Spin_Noether_zero': True,
            'all36_spatial_and12_time_torsion_derivatives_zero': True,
            'all16_coframe_Euler_consumed_with_four_initial_residuals_retained': True,
            'time4_residual': encode(residual4), 'second_spatial_etime_symbols_cancelled': spatial['second_spatial_symbols_cancelled'],
            'omitted_spatial_contorsion_derivative_control_nonzero': True},
        'Spin_representative': 'Actual Omega0=0 and its spatial gradients0; no replacement by canonical lambda0 coordinates.',
        'general_PDE_Cauchy_or_quantum_measure_claimed': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_spatial_lorentz_time.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print(result['verdict'], result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
