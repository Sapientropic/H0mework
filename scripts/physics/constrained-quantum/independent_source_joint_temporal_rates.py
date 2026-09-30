#!/usr/bin/env python3
"""Independent complete canonical tangent and original second-jet audit.

No candidate constructor is imported. The Hamiltonian state tangent is the
epsilon coefficient of the original densities on state+epsilon*actual_rate.
All accelerations are recovered from full original momentum equations.
"""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import time

import sympy as s

from independent_source_gauge_legendre import (
    HERE, BASE, ROOT, ROOT_ID, PAIRS, SIGMA, W, ETA, source, bindings, clean,
    decode, equal, dot, exterior, hodge, hodge_field_jet,
    matrix_coordinates, read, read_gamma, realify)
from independent_source_lorentz_contact import (
    original_hessian, geometric_load, original_density_ports,
    exterior as lorentz_exterior, J as INTERNAL_J, WEDGE, GENERATORS)
from independent_source_constraint_preservation import wedge_yukawa


def rational(A): return s.SparseMatrix(A).applyfunc(s.cancel)
def zero(value): assert s.cancel(value) == 0
def eq(A, B): assert not rational(A-B).todok()


def encode(A):
    A = s.SparseMatrix(A)
    return {'shape': [int(A.rows), int(A.cols)],
            'entries': [[int(i), int(j), str(value)] for (i, j), value in sorted(A.todok().items())]}


class RawSource:
    def __init__(self):
        _, vacuum, degrees, self.hashes = source.parse_source(ROOT)
        raw = source.generators([(0, 1, 2), (3, 4)])
        self.fundamental = [s.Matrix(M)*(s.I if imaginary else 1) for _, imaginary, M in raw]
        self.rho70 = [realify(exterior(T, 4)) for T in self.fundamental]
        self.rho63 = [clean(s.diag(*(exterior(T, degree) for degree in degrees))) for T in self.fundamental]
        self.rho252 = [clean(s.kronecker_product(s.SparseMatrix.eye(4), T)) for T in self.rho63]
        self.adjoint = []
        for T in self.fundamental:
            self.adjoint.append(s.Matrix.hstack(*(matrix_coordinates(T*S-S*T) for S in self.fundamental)))
        self.Gram = s.Matrix(12, 12, lambda a, b: s.re(-s.trace(self.fundamental[a][:3, :3]*self.fundamental[b][:3, :3])-
            s.trace(self.fundamental[a][3:5, 3:5]*self.fundamental[b][3:5, 3:5])-
            self.fundamental[a][5, 5]*self.fundamental[b][5, 5]))
        self.words = list(itertools.combinations(range(7), 4))
        self.v = s.Matrix([vacuum.get(word, 0) for word in self.words]+[0]*35)
        self.O = clean(s.Matrix.hstack(*(R*self.v for R in self.rho70)))
        self.broken = list(self.O.rref()[1]); self.S = s.eye(12)[:, self.broken]
        self.Ob = self.O*self.S
        self.P61 = clean(s.eye(70)-self.Ob*(self.Ob.T*self.Ob).inv()*self.Ob.T)
        self.Y = []
        for word in self.words:
            small = s.MutableSparseMatrix.zeros(63, 63)
            small[:7, 7:28] = wedge_yukawa(word)
            self.Y.append(clean(s.kronecker_product(s.diag(0, 0, 1, 1), small)))
        self.Y += [s.I*Y for Y in self.Y.copy()]
        self.gamma = read_gamma()
        self.spin = [self.gamma[a]*self.gamma[b]/2 for a, b in PAIRS]
        self.eg = s.Matrix(4, 4, s.symbols('raw_e0:16', real=True))
        self.Hsymbol = original_hessian(self.eg); self.Gsymbol = geometric_load(self.eg)
        self.flat_inverse = original_hessian(s.eye(4)).inv()
        self.active = read(BASE/'active-gauge/receipt.json')
        self.occupied = read(BASE/'occupied-response/receipt.json')
        self.A = s.Matrix(self.active['actual_background']['gauge_connection']).applyfunc(s.sympify)
        self.psi0 = decode(self.occupied['occupied_frame'])*s.Matrix(self.active['actual_background']['primal_H']).applyfunc(s.sympify)
        self.chi0 = s.sympify(self.active['actual_background']['dual_multiple'])*self.psi0.T

    def ad(self, A): return clean(sum((x*T for x, T in zip(A, self.adjoint)), s.zeros(12)))
    def bracket(self, A, B): return clean(self.ad(A)*s.Matrix(list(B)))
    def action(self, A, representation): return clean(sum((x*R for x, R in zip(A, representation)), s.zeros(representation[0].rows)))
    def yukawa(self, phi): return clean(sum((x*Y for x, Y in zip(phi, self.Y) if x), s.SparseMatrix.zeros(252, 252)))
    def density(self, psi, chi): return clean(psi.reshape(4, 63)*chi.reshape(4, 63).T)

    def geometry(self, e):
        change = dict(zip(self.eg, e))
        H = clean(self.Hsymbol.xreplace(change)); G = clean(self.Gsymbol.xreplace(change))
        transform = s.kronecker_product(e, s.SparseMatrix.eye(6))
        inverse = rational(transform.T*self.flat_inverse*transform/e.det())
        return H, G, inverse

    def principals(self, e):
        return [clean(s.Abs(e.det())*sum((s.I*e.inv()[mu, a]*self.gamma[a] for a in range(4)), s.zeros(4))) for mu in range(4)]

    def current(self, e, psi, chi):
        C = self.principals(e); density = self.density(psi, chi)
        return s.Matrix([s.expand(s.re(s.trace(C[mu]*spin*density))) for mu in range(4) for spin in self.spin])

    def lower(self, e, phi, A, omega=None):
        C = self.principals(e)
        result = s.Abs(e.det())*self.yukawa(phi)
        for mu in range(4):
            result += s.kronecker_product(C[mu], s.SparseMatrix.eye(63))*self.action(A[mu, :], self.rho252)
            if omega is not None:
                result += sum((omega[6*mu+a]*s.kronecker_product(C[mu]*self.spin[a], s.SparseMatrix.eye(63)) for a in range(6)), s.SparseMatrix.zeros(252, 252))
        return clean(result)

    def curvature(self, A, electric=None):
        return clean(s.Matrix.vstack(*((self.bracket(A[mu, :], A[nu, :]).T+
            (electric[nu-1, :] if mu == 0 and electric is not None else s.zeros(1, 12))) for mu, nu in PAIRS)))

    def metric(self, e): return clean(s.Abs(e.det())*(e.T*ETA*e).inv())

    def coefficient_derivatives(self, e, direction):
        volume = s.Abs(e.det()); inverse = e.inv()
        dvolume = volume*s.trace(inverse*direction); dinverse = -inverse*direction*inverse
        dC = [clean(sum((s.I*(dvolume*inverse[mu, a]+volume*dinverse[mu, a])*self.gamma[a] for a in range(4)), s.zeros(4))) for mu in range(4)]
        metric = e.T*ETA*e; dg = direction.T*ETA*e+e.T*ETA*direction
        dh = clean(dvolume*metric.inv()-volume*metric.inv()*dg*metric.inv())
        return dvolume, dC, dh

    def forces(self, e, phi, phi_dot, A, F, psi, psi_dot, chi, omega):
        H, G, inverse = self.geometry(e)
        C = self.principals(e); density = self.density(psi, chi)
        h = self.metric(e)
        RA = [self.action(A[mu, :], self.rho70) for mu in range(4)]
        matter_A = [self.action(A[mu, :], self.rho252) for mu in range(4)]
        cov = [phi_dot+RA[0]*phi, *[RA[i+1]*phi for i in range(3)]]
        scalar_momenta = [sum((h[mu, nu]*cov[nu] for nu in range(4)), s.zeros(70, 1)) for mu in range(4)]
        scalar_current = s.Matrix(4, 12, lambda mu, a: dot(scalar_momenta[mu], self.rho70[a]*phi))
        matter_current = s.Matrix(4, 12, lambda mu, a: s.expand(s.re((chi*s.kronecker_product(C[mu], self.rho63[a])*psi)[0])))
        traces = [self.density((psi_dot if mu == 0 else s.zeros(252, 1))+matter_A[mu]*psi, chi) for mu in range(4)]
        Yvalue = s.re((chi*self.yukawa(phi)*psi)[0]).expand()
        force = []
        for index in range(16):
            direction = s.zeros(4); direction[index//4, index % 4] = 1
            dv, dC, dh = self.coefficient_derivatives(e, direction)
            dj = s.Matrix([s.expand(s.re(s.trace(dC[mu]*spin*density))) for mu in range(4) for spin in self.spin])
            dH = self.Hsymbol.diff(self.eg[index]).xreplace(dict(zip(self.eg, e)))
            gravity = -3*dv+dot(omega, dH*omega)/2+dot(omega, dj)
            scalar = sum(dh[mu, nu]*dot(cov[mu], cov[nu])/2 for mu in range(4) for nu in range(4))-dv*dot(phi-self.v, phi-self.v)
            _, star_dot = hodge_field_jet(e, direction, F, s.zeros(6, 12))
            gauge = -dot(F, W*star_dot*self.Gram)/(2*SIGMA)
            matter = dv*Yvalue+sum(s.re(s.trace(dC[mu]*traces[mu])) for mu in range(4))
            force.append(s.expand(gravity+scalar+gauge+matter))
        Yforce = s.Matrix([s.expand(s.Abs(e.det())*s.re((chi*Y*psi)[0])) for Y in self.Y])
        phi_force = clean(-sum((RA[mu]*scalar_momenta[mu] for mu in range(4)), s.zeros(70, 1))-
            2*s.Abs(e.det())*(phi-self.v)+Yforce)
        return clean(s.Matrix(force)), clean(phi_force), clean(scalar_current), clean(matter_current), cov, Yforce


def ordered(F, mu, nu):
    if mu == nu: return s.zeros(12, 1)
    if (mu, nu) in PAIRS: return F[PAIRS.index((mu, nu)), :].T
    return -F[PAIRS.index((nu, mu)), :].T


def main():
    began = time.monotonic()
    candidate_path = HERE/'source_joint_temporal_rates.json'
    candidate = read(candidate_path); count = bindings(candidate)
    raw = RawSource(); assert raw.hashes == candidate['source_sha256'] and candidate['root'] == ROOT_ID
    saved = candidate['all_canonical_rates']
    initial_audit_path = HERE/'independent_source_coframe_initial_constraints.json'
    prior = read(initial_audit_path); count += bindings(prior)
    n = s.Symbol('temporal_n', positive=True)
    shift = s.Matrix(s.symbols('temporal_shift1:4', real=True))
    gamma = s.Symbol('gamma', real=True)
    evar = s.Matrix([[n, 0, 0, 0], [shift[0], 1, 0, 0], [shift[1], 0, 1, 0], [shift[2], 0, 0, 1]])
    Qvar = rational(-W*hodge(evar)/SIGMA)
    magnetic = raw.curvature(raw.A)[3:, :]
    c0 = s.simplify(s.trace(magnetic*raw.Gram*magnetic.T)/(6*SIGMA))
    ce = s.simplify(SIGMA*dot(raw.A[1:, :], raw.A[1:, :]*raw.Gram)/6)
    assert c0 == s.Rational(162, 625) and ce == s.Rational(9, 100)
    X = gamma*raw.A[1:, :]-Qvar[:3, 3:]*magnetic
    generic_gauge_H = s.factor((dot(X, Qvar[:3, :3].inv()*X*raw.Gram)-dot(magnetic, Qvar[3:, 3:]*magnetic*raw.Gram))/2)
    gauge_coefficient = c0+ce*gamma**2
    zero(generic_gauge_H-gauge_coefficient*(3*n**2-dot(shift, shift))/(n*(n**2-dot(shift, shift))))
    u, alpha, beta, radial = s.symbols('u alpha beta radial', real=True)
    clock_coefficient = s.sympify(prior['clock_coefficient'], locals={str(x): x for x in (u, alpha, beta, radial)})
    family_symbols = {str(x): x for x in (u, alpha, beta, radial, gamma)}
    assert s.expand(clock_coefficient-(s.Rational(9, 5)-alpha*beta*u/2+u**2*(s.Rational(73, 200)-radial**2/4))) == 0
    zero(gauge_coefficient-s.sympify(candidate['source_family']['full_gauge_coefficient'], locals=family_symbols))
    numerical_parameters = {u: s.Rational(1, 4), alpha: 1, beta: 1, radial: s.Rational(1, 3), gamma: s.Rational(1, 5)}
    coefficient = clock_coefficient.subs(numerical_parameters)
    c_actual = gauge_coefficient.subs(numerical_parameters)
    n2 = s.factor(3*c_actual/coefficient)
    assert n2 == s.sympify(candidate['generated_clock_squared']) == s.Rational(567648, 1221175)
    lapse = s.sqrt(n2); e = s.diag(lapse, 1, 1, 1)
    phi = raw.v+raw.P61[:, 23]/4; Pi_phi = raw.P61[:, 23]/12
    psi, chi = raw.psi0.copy(), raw.chi0.copy(); psi[135] += 1; chi[126] += 1
    A = raw.A
    Pi_A = clean(A[1:, :]*raw.Gram/5)
    for row in range(3): equal(raw.ad(A[row+1, :]).T*Pi_A[row, :].T, s.zeros(12, 1))
    H, G, inverse = raw.geometry(e); Gt = G[:, :16]
    current = raw.current(e, psi, chi); omega = clean(-inverse*current)
    equal(Gt.T*omega, s.zeros(16, 1))
    E = clean(s.kronecker_product(raw.principals(e)[0], s.SparseMatrix.eye(63)))
    p = clean(-s.I*chi*E)
    lower = raw.lower(e, phi, A, omega)
    psi_dot = clean(-E.inv()*lower*psi); chi_dot = clean(chi*lower*E.inv()); p_dot = clean(-s.I*chi_dot*E)
    h = raw.metric(e); phi_dot = clean(Pi_phi/h[0, 0])
    Q = clean(-W*hodge(e)/SIGMA)
    A_dot = clean(Q[:3, :3].inv()*(Pi_A*raw.Gram.inv()-Q[:3, 3:]*magnetic))
    F = raw.curvature(A, A_dot); field_P = clean(Q*F*raw.Gram)
    equal(field_P[:3, :], Pi_A)
    Pi_e_dot, Pi_phi_dot, jscalar, jmatter, cov, Yforce = raw.forces(e, phi, phi_dot, A, F, psi, psi_dot, chi, omega)
    Pi_A_dot = s.Matrix.vstack(*(sum((raw.ad(A[mu, :]).T*ordered(field_P, mu, i+1) for mu in range(4)), s.zeros(12, 1)).T for i in range(3)))
    Pi_A_dot = clean(Pi_A_dot+jscalar[1:, :]+jmatter[1:, :])
    rates = {'coframe_spatial_rate': s.zeros(16, 1), 'coframe_momentum_rate': Pi_e_dot,
        'scalar_rate': phi_dot, 'scalar_momentum_rate': Pi_phi_dot, 'gauge_spatial_rate': A_dot,
        'gauge_momentum_rate': Pi_A_dot, 'primal_rate': psi_dot, 'canonical_dual_rate': p_dot,
        'dual_rate_at_fixed_spatial_coframe': chi_dot, 'connection': omega,
        'actual_scalar_current': jscalar, 'actual_matter_current': jmatter}
    for name, value in rates.items(): eq(value, decode(saved[name]))
    print('PASS source native-dual gamma momentum/clock family and every original canonical Hamilton rate', flush=True)

    # Extract an actual state-direction coefficient from the raw densities.
    # The frozen vector is not a derivative within the initial family.
    eps = s.Symbol('state_variation', real=True)
    phi_eps, Pi_eps = phi+eps*phi_dot, Pi_phi+eps*Pi_phi_dot
    psi_eps, chi_eps = psi+eps*psi_dot, chi+eps*chi_dot
    A_eps = A.copy(); A_eps[1:, :] += eps*A_dot
    Pi_A_eps = Pi_A+eps*Pi_A_dot
    Hq, Gq, inverse_q = raw.geometry(evar)
    j_base = raw.current(evar, psi, chi)
    equal(Gq[:, :16].T*inverse_q*j_base, s.zeros(16, 1))
    # The original velocity derivative dH/dPi_e is identically zero for
    # every time-column value here, so its entire sixteen-rate contribution
    # is zero; the rate itself was reconstructed above and is retained.
    j_eps = raw.current(evar, psi_eps, chi_eps)
    Hcf_eps = 3*n+dot(j_eps, inverse_q*j_eps)/2
    hq = raw.metric(evar)
    spatial_eps = [raw.action(A_eps[i+1, :], raw.rho70)*phi_eps for i in range(3)]
    temporal_eps = (Pi_eps-sum((hq[0, i+1]*spatial_eps[i] for i in range(3)), s.zeros(70, 1)))/hq[0, 0]
    cov_eps = [temporal_eps, *spatial_eps]
    Lscalar_eps = sum(hq[mu, nu]*dot(cov_eps[mu], cov_eps[nu])/2 for mu in range(4) for nu in range(4))-n*dot(phi_eps-raw.v, phi_eps-raw.v)
    Hscalar_eps = dot(Pi_eps, temporal_eps)-Lscalar_eps
    B_eps = raw.curvature(A_eps)[3:, :]
    E_eps = Qvar[:3, :3].inv()*(Pi_A_eps*raw.Gram.inv()-Qvar[:3, 3:]*B_eps)
    F_eps = E_eps.col_join(B_eps)
    Hgauge_eps = dot(Pi_A_eps, E_eps)-dot(F_eps, Qvar*F_eps*raw.Gram)/2
    Hmatter_eps = -s.re((chi_eps*raw.lower(evar, phi_eps, A_eps)*psi_eps)[0])
    tangent_components = {name: s.factor(s.diff(value, eps).subs(eps, 0)) for name, value in
        [('coframe', Hcf_eps), ('scalar', Hscalar_eps), ('gauge', Hgauge_eps), ('remaining_matter', Hmatter_eps)]}
    temporal_symbols = {str(x): x for x in [n, *shift]}
    for name, value in tangent_components.items():
        zero(value-s.sympify(candidate['actual_Hamiltonian_state_tangent_components'][name], locals=temporal_symbols))
    tangent = s.factor(sum(tangent_components.values()))
    zero(tangent-s.sympify(candidate['actual_Hamiltonian_state_tangent'], locals=temporal_symbols))
    at_point = {n: lapse, **dict.fromkeys(shift, 0)}
    zero(tangent.subs(at_point))
    forcing = rational(s.Matrix([-s.diff(tangent, x).subs(at_point) for x in [n, *shift]]))
    family_H = n*coefficient+c_actual*(3*n**2-dot(shift, shift))/(n*(n**2-dot(shift, shift)))
    J4 = rational(-s.hessian(family_H, [n, *shift]).subs(at_point))
    temporal_rate = rational(J4.inv()*(-forcing))
    assert forcing != s.zeros(4, 1) and temporal_rate[0] == s.Rational(103923, 244235)
    for name, value in [('constraint_forcing', forcing), ('temporal_Jacobian', J4), ('time_coframe_rate', temporal_rate)]:
        eq(value, decode(saved[name]))
    eq(J4*temporal_rate+forcing, s.zeros(4, 1))
    e_dot = s.zeros(4)
    e_dot[:, 0] = temporal_rate
    _, C_dot, h_dot = raw.coefficient_derivatives(e, e_dot)
    equal(C_dot[0], s.zeros(4))
    RA = [raw.action(A[mu, :], raw.rho70) for mu in range(4)]
    dRA_spatial = [raw.action(A_dot[i, :], raw.rho70) for i in range(3)]
    cov_dot_without_phi00 = [s.zeros(70, 1), *[dRA_spatial[i]*phi+RA[i+1]*phi_dot for i in range(3)]]
    momentum_offset = sum((h_dot[0, mu]*cov[mu]+h[0, mu]*cov_dot_without_phi00[mu] for mu in range(4)), s.zeros(70, 1))
    phi00_without_A0 = clean((Pi_phi_dot-momentum_offset)/h[0, 0])
    D = clean(raw.O.T*s.Matrix.hstack(*(R*phi for R in raw.rho70)))
    A0_coefficients, free = (D*raw.S).gauss_jordan_solve(raw.O.T*phi00_without_A0)
    assert free.rows == 0
    A0_dot = clean(raw.S*A0_coefficients)
    phi00 = clean(phi00_without_A0-raw.action(A0_dot, raw.rho70)*phi)
    equal(raw.O.T*phi00, s.zeros(12, 1))
    eq(A0_dot, decode(saved['time_connection_rate']))
    assert A0_dot[2] == -s.Rational(283824, 1221175)
    B = s.zeros(9, 4)
    for column in range(4):
        delta = s.zeros(4); delta[column, 0] = 1
        _, _, dh = raw.coefficient_derivatives(e, delta)
        B[:, column] = raw.Ob.T*sum((dh[0, mu]*cov[mu] for mu in range(4)), s.zeros(70, 1))/h[0, 0]
    eq(B, decode(saved['lower_left']))
    base_phi00 = Pi_phi_dot/h[0, 0]
    eq(B*temporal_rate+raw.S.T*D*A0_dot, raw.Ob.T*base_phi00)
    print('PASS original state+epsilon*whole-rate derivative, nonzero f4/coframe rate and original scalar-Euler A0 consistency', flush=True)

    # Coframe acceleration: solve all sixteen raw momentum derivative rows
    # on an independent symmetric-spatial six-dimensional section.
    geometry_change = dict(zip(raw.eg, e))
    H_dot = clean(sum((e_dot[k]*raw.Hsymbol.diff(raw.eg[k]).xreplace(geometry_change) for k in range(16)), s.zeros(24)))
    G_dot = clean(sum((e_dot[k]*raw.Gsymbol.diff(raw.eg[k]).xreplace(geometry_change) for k in range(16)), s.zeros(24, 64)))
    density = raw.density(psi, chi)
    density_dot = raw.density(psi_dot, chi)+raw.density(psi, chi_dot)
    C = raw.principals(e)
    j_dot = s.Matrix([s.expand(s.re(s.trace(C_dot[mu]*spin*density+C[mu]*spin*density_dot))) for mu in range(4) for spin in raw.spin])
    de = e_dot.reshape(16, 1).col_join(s.zeros(48, 1))
    equal(G*de, s.zeros(24, 1)); equal(G_dot*de, s.zeros(24, 1))
    Omega_part = clean(-inverse*(H_dot*omega+G_dot*de+j_dot))
    shift_rate = clean(G_dot[:, :16].T*omega+Gt.T*Omega_part)
    M = clean(-Gt.T*inverse*Gt)
    section_columns = []
    for i, j in itertools.combinations_with_replacement(range(1, 4), 2):
        column = s.zeros(4); column[i, j] = column[j, i] = 1
        section_columns.append(column.reshape(16, 1))
    section = s.Matrix.hstack(*section_columns)
    coefficients, free = (M*section).gauss_jordan_solve(Pi_e_dot-shift_rate)
    assert free.rows == 0
    e_acc = clean(section*coefficients)
    Z = s.Matrix.hstack(*(s.eye(16)[:, 4*a] for a in range(4)), *((T*e).reshape(16, 1) for T in GENERATORS))
    assert M.rank() == 6 and Z.rank() == 10
    equal(M*Z, s.zeros(16, 10)); equal(Z.T*(Pi_e_dot-shift_rate), s.zeros(10, 1))
    eq(M*e_acc+shift_rate, Pi_e_dot)
    omega_dot = clean(Omega_part-inverse*Gt*e_acc)
    eq(Pi_e_dot-G_dot[:, :16].T*omega-Gt.T*omega_dot, s.zeros(16, 1))

    # Gauge acceleration is solved against the full native36 velocity
    # Hessian. The changing Hodge acts before coefficient extraction.
    A_rate = s.Matrix.vstack(A0_dot.T, A_dot)
    Fdot_offset = s.Matrix.vstack(*((raw.bracket(A_rate[mu, :], A[nu, :])+
                                     raw.bracket(A[mu, :], A_rate[nu, :])).T for mu, nu in PAIRS))
    _, star_dot = hodge_field_jet(e, e_dot, F, Fdot_offset)
    Pdot_offset = clean(-W*star_dot*raw.Gram/SIGMA)
    velocity_Hessian = s.kronecker_product(Q[:3, :3], raw.Gram)
    A_acc = clean(velocity_Hessian.inv()*(Pi_A_dot-Pdot_offset[:3, :]).reshape(36, 1)).reshape(3, 12)
    Fdot = Fdot_offset.copy(); Fdot[:3, :] += A_acc
    _, whole_star_dot = hodge_field_jet(e, e_dot, F, Fdot)
    field_Pdot = clean(-W*whole_star_dot*raw.Gram/SIGMA)
    equal(field_Pdot[:3, :], Pi_A_dot)
    gauge_Euler = s.zeros(4, 12)
    for nu in range(4):
        gauge_Euler[nu, :] = (-ordered(field_Pdot, 0, nu)+sum((raw.ad(A[mu, :]).T*ordered(field_P, mu, nu) for mu in range(4)), s.zeros(12, 1))).T
    equal(gauge_Euler+jscalar+jmatter, s.zeros(4, 12))
    cov_dot = [phi00+raw.action(A0_dot, raw.rho70)*phi, *cov_dot_without_phi00[1:]]
    raw_Pi_phi_dot = clean(sum((h_dot[0, mu]*cov[mu]+h[0, mu]*cov_dot[mu] for mu in range(4)), s.zeros(70, 1)))
    equal(raw_Pi_phi_dot, Pi_phi_dot)
    equal(E*psi_dot+lower*psi, s.zeros(252, 1)); equal(chi*lower-chi_dot*E, s.zeros(1, 252))
    acceleration_claim = candidate['retained_source_accelerations']
    for name, value in [('coframe_acceleration', e_acc), ('gauge_acceleration', A_acc), ('scalar_acceleration', phi00)]:
        eq(value, decode(acceleration_claim[name]))
    print('PASS independent full16 and36 momentum solves, all16/70/48/252+252 original reduced Euler rows and ten primary rates', flush=True)

    # Actual Gauss differentiation uses every generated momentum/field rate.
    gauss_eps = s.zeros(12, 1)
    for i in range(3): gauss_eps -= raw.ad(A_eps[i+1, :]).T*Pi_A_eps[i, :].T
    for a in range(12):
        gauss_eps[a] += dot(Pi_eps, raw.rho70[a]*phi_eps)+s.re((s.I*(p+eps*p_dot)*raw.rho252[a]*psi_eps)[0])
    equal(gauss_eps.subs(eps, 0), s.zeros(12, 1))
    equal(gauss_eps.diff(eps).subs(eps, 0), s.zeros(12, 1))
    equal(raw.O.T*phi, s.zeros(12, 1)); equal(raw.O.T*phi_dot, s.zeros(12, 1))
    equal(raw.O.T*phi00, s.zeros(12, 1))
    Rgravity = s.zeros(6)
    omega_matrix = [sum((omega[6*mu+a]*GENERATORS[a] for a in range(6)), s.zeros(4)) for mu in range(4)]
    omega_matrix_dot = [sum((omega_dot[6*mu+a]*GENERATORS[a] for a in range(6)), s.zeros(4)) for mu in range(4)]
    for pair, (mu, nu) in enumerate(PAIRS):
        curvature_matrix = omega_matrix[mu]*omega_matrix[nu]-omega_matrix[nu]*omega_matrix[mu]
        if mu == 0: curvature_matrix += omega_matrix_dot[nu]
        if nu == 0: curvature_matrix -= omega_matrix_dot[mu]
        for a, (i, j) in enumerate(PAIRS): Rgravity[a, pair] = ETA[i, i]*curvature_matrix[i, j]
    Bg = clean(INTERNAL_J*lorentz_exterior(e))
    pair_metric = s.diag(-1, -1, -1, 1, 1, 1)
    multiplier = clean(INTERNAL_J*Bg-pair_metric*Rgravity)
    Bgauge = clean(-hodge(e)*F/SIGMA)
    equal((Rgravity-pair_metric*INTERNAL_J*Bg+pair_metric*multiplier)*WEDGE, s.zeros(6))
    equal(pair_metric*(Bg-INTERNAL_J*lorentz_exterior(e))*WEDGE, s.zeros(6))
    equal(H*omega+G*de+current, s.zeros(24, 1))
    equal(F-SIGMA*hodge(e)*Bgauge, s.zeros(6, 12))
    beta_form = s.zeros(4, 24); Cform = Bg*WEDGE
    for pair, (mu, nu) in enumerate(PAIRS):
        for a in range(6):
            beta_form[mu, 6*nu+a] += Cform[a, pair]
            beta_form[nu, 6*mu+a] -= Cform[a, pair]
    original = candidate['original_whole_Euler_and_constraint_consumers']
    for name, value in [('gravity_B', Bg), ('simplicity_multiplier', multiplier), ('gauge_B', Bgauge), ('original_BF_boundary_flux', beta_form*omega)]:
        eq(value, decode(original[name]))
    assert 16+70+48+2*(252+252)+168 == original['whole_original_real_field_Euler_rows'] == 1310
    print('PASS all168 original auxiliary equations and complete1310 real Euler lift, Gauss/C first-second rates and retained BF boundary', flush=True)

    # Nonzero lower-left control from the original metric derivative.
    source_N = s.sympify(raw.active['source_lapse']); control_e = s.diag(source_N, 1, 1, 1)
    control_phi, control_Pi = raw.v, raw.Ob[:, 0]
    control_A0 = -source_N*raw.S[:, 0]
    control_h = raw.metric(control_e)
    control_U = [control_Pi/control_h[0, 0], *[s.zeros(70, 1)]*3]
    equal(raw.O.T*(control_U[0]-raw.action(control_A0, raw.rho70)*control_phi), s.zeros(12, 1))
    control = s.zeros(9, 4)
    for a in range(4):
        delta = s.zeros(4); delta[a, 0] = 1
        _, _, dh = raw.coefficient_derivatives(control_e, delta)
        control[:, a] = raw.Ob.T*sum((dh[0, mu]*control_U[mu] for mu in range(4)), s.zeros(70, 1))/control_h[0, 0]
    equal(control[:, 0], (raw.Ob.T*raw.Ob)[:, 0]); equal(control[:, 1:], s.zeros(9, 3))
    assert control != s.zeros(9, 4)
    eq(control, decode(candidate['lower_left_control']['nonzero_lower_left']))
    print('PASS genuine nonzero source lower-left coupling on C=dotC=0; no block-diagonal assumption', flush=True)

    count += bindings(raw.active)+bindings(raw.occupied)
    paths = [candidate_path, HERE/'source_joint_temporal_rates.py', Path(__file__), initial_audit_path,
        HERE/'independent_source_gauge_legendre.py', HERE/'independent_source_lorentz_contact.py',
        HERE/'independent_source_constraint_preservation.py', BASE/'exact_readout.py',
        BASE/'active-gauge/receipt.json', BASE/'occupied-response/receipt.json']
    result = {'verdict': 'CERTIFIED_COMPLETE_SOURCE_CANONICAL_TANGENT_JOINT13_UPDATE_AND_ORIGINAL1310_SECOND_JET',
        'root': ROOT_ID, 'source_sha256': raw.hashes,
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_or_common_Hamiltonian_constructor_imported': False, 'source_binding_checks': count,
        'independent_algorithm': 'original BF/Dirac/scalar/gauge forces for all canonical rates; exact epsilon coefficient of original density Hamiltonians on state+epsilon*whole_rate; full16-row and36-row original momentum-derivative solves; raw Clifford/Lie Euler and auxiliary reconstruction',
        'generic_gauge_coefficient': '162/625+9 gamma^2/100',
        'actual_clock_squared': str(n2), 'actual_constraint_forcing': encode(forcing),
        'actual_time_coframe_rate': encode(temporal_rate), 'actual_time_gauge_connection_rate': encode(A0_dot),
        'nonzero_clock_rate': '103923/244235', 'nonzero_A0_rate_coordinate2': '-283824/1221175',
        'all_original_canonical_rates_rebuilt': ['coframe momentum16', 'scalar coordinate/momentum70+70',
            'gauge coordinate/momentum36+36', 'independent complex matter coordinate/momentum252+252'],
        'coframe_spatial_velocity_zero_from_original_momentum_law': True,
        'all16_coframe_momentum_rates_retained_even_when_Hamiltonian_tangent_coefficient_zero': True,
        'Hamiltonian_tangent': {'frozen_at_actual_initial_state': True, 'all_components_match': True,
            'source_point_energy_derivative_zero': True, 'temporal_constraint_forcing_nonzero': True,
            'restricted_initial_parameter_family_derivative_used': False},
        'raw_acceleration_solve': {'coframe_equations': 16, 'physical_section_dimension': 6,
            'coframe_null_dimension': 10, 'gauge_velocity_equations': 36,
            'same_source_scalar_Euler_and_A0_solution': True},
        'original_Euler_rows': {'coframe_real': 16, 'scalar_real': 70, 'gauge_real': 48,
            'primal_complex': 252, 'independent_dual_complex': 252, 'auxiliary_real': 168, 'total_real': 1310,
            'all_zero_at_generated_second_jet': True},
        'constraint_rates': {'coframe_primary10': True, 'Gauss12': True, 'C_first_and_second': True,
            'time_coframe4': True, 'time_connection12': True},
        'BF_boundary_flux_retained': True,
        'lower_left_control': {'original_metric_derivative_used': True, 'C_and_Cdot_zero': True,
            'strictly_nonzero': True, 'general_block_diagonal_assumed': False},
        'spatial_scope': 'the actual homogeneous canonical field jet, retaining non-Abelian curvature and covariant spatial derivatives',
        'temporal_coframe_or_A0_second_derivative_preservation_claimed': False,
        'all_time_or_inhomogeneous_Cauchy_or_quantum_spectrum_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_joint_temporal_rates.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent complete joint temporal update audit', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
