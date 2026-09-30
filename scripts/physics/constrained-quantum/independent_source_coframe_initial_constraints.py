#!/usr/bin/env python3
"""Independent original-density initial coframe constraint audit.

The candidate/common Hamiltonian constructors are not imported. Raw BF,
Dirac and scalar densities generate the family and its actual momenta; raw
fixed-velocity stresses separately recover the four canonical constraints.
"""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import time

import sympy as s

from independent_source_gauge_legendre import (
    HERE, BASE, ROOT, ROOT_ID, PAIRS, SIGMA, W, source, bindings, clean, decode,
    dot, encode, equal, exterior, hodge, hodge_field_jet, read, read_gamma,
    realify)
from independent_source_lorentz_contact import (
    original_hessian, geometric_load, original_density_ports,
    exterior as lorentz_exterior, J as INTERNAL_J, WEDGE, GENERATORS)
from independent_source_constraint_preservation import wedge_yukawa


def rational(A): return s.SparseMatrix(A).applyfunc(s.cancel)
def zero(value): assert s.cancel(value) == 0
def equal_rational(A, B): assert not rational(A-B).todok()


def main():
    began = time.monotonic()
    candidate_path = HERE/'source_coframe_initial_constraints.json'
    candidate = read(candidate_path)
    assert candidate['root'] == ROOT_ID
    count = bindings(candidate)
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    assert hashes == candidate['source_sha256']
    raw = source.generators([(0, 1, 2), (3, 4)])
    fundamental = [s.Matrix(M)*(s.I if imaginary else 1) for _, imaginary, M in raw]
    rho70 = [realify(exterior(T, 4)) for T in fundamental]
    rho63 = [clean(s.diag(*(exterior(T, degree) for degree in degrees))) for T in fundamental]
    rho252 = [clean(s.kronecker_product(s.SparseMatrix.eye(4), T)) for T in rho63]
    words = list(itertools.combinations(range(7), 4))
    v = s.Matrix([vacuum.get(word, 0) for word in words]+[0]*35)
    orbit = s.Matrix.hstack(*(R*v for R in rho70))
    broken = list(orbit.rref()[1]); orbit_basis = orbit[:, broken]
    projector = clean(s.eye(70)-orbit_basis*(orbit_basis.T*orbit_basis).inv()*orbit_basis.T)
    q = projector[:, 23]
    assert dot(q, q) == s.Rational(1, 2)
    n = s.Symbol('n', positive=True)
    shift = s.Matrix(s.symbols('shift1:4', real=True))
    u, alpha, beta, radial = s.symbols('u alpha beta radial', real=True)
    symbols = {str(x): x for x in [n, *shift, u, alpha, beta, radial]}
    e = s.Matrix([[n, 0, 0, 0], [shift[0], 1, 0, 0], [shift[1], 0, 1, 0], [shift[2], 0, 0, 1]])
    phi, Pi_phi = v+u*q, radial*u*q
    active_path = BASE/'active-gauge/receipt.json'; active = read(active_path)
    occupied_path = BASE/'occupied-response/receipt.json'; occupied = read(occupied_path)
    background = active['actual_background']
    frame = decode(occupied['occupied_frame'])
    psi0 = frame*s.Matrix(background['primal_H']).applyfunc(s.sympify)
    chi0 = s.sympify(background['dual_multiple'])*psi0.T
    psi, chi = psi0.copy(), chi0.copy()
    psi[135] += alpha; chi[126] += beta
    density = clean(psi.reshape(4, 63)*chi.reshape(4, 63).T)
    equal(density, psi0.reshape(4, 63)*chi0.reshape(4, 63).T)
    gamma = read_gamma()
    E4, ports = original_density_ports(e, gamma)
    equal(E4, s.I*gamma[0])
    E = clean(s.kronecker_product(E4, s.SparseMatrix.eye(63)))
    p = clean(-s.I*chi*E)

    generic_e = s.Matrix(4, 4, s.symbols('coframe0:16', real=True))
    Gsymbol = geometric_load(generic_e)
    Hsymbol = original_hessian(generic_e)
    family_sub = dict(zip(generic_e, e))
    G = clean(Gsymbol.xreplace(family_sub))
    Hessian = original_hessian(e)
    flat_inverse = original_hessian(s.eye(4)).inv()
    transform = s.kronecker_product(e, s.SparseMatrix.eye(6))
    inverse = clean(transform.T*flat_inverse*transform/n)
    equal(Hessian*inverse, s.eye(24))
    current = s.Matrix([s.expand(s.re(s.trace(V*density))) for V in ports])
    Omega = clean(-inverse*current)
    coframe_momentum = clean(G[:, :16].T*Omega)
    equal(coframe_momentum, s.zeros(16, 1))
    Hcf = s.factor(3*n+dot(current, inverse*current)/2)
    assert Hcf == 9*n
    for a in (0, 4, 8, 12):
        equal(generic_e.adjugate()[0, :].diff(generic_e[a]), s.zeros(1, 4))
        equal(Gsymbol[:, a], s.zeros(24, 1))

    A = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
    RA = [clean(sum((A[mu, a]*rho70[a] for a in range(12)), s.zeros(70))) for mu in range(4)]
    RA_matter = [clean(sum((A[mu, a]*rho252[a] for a in range(12)), s.zeros(252))) for mu in range(4)]
    h = clean(n*(e.T*s.diag(-1, 1, 1, 1)*e).inv())
    Di = [clean(RA[i+1]*phi) for i in range(3)]
    phi_dot = clean(-n*Pi_phi+sum((shift[i]*Di[i] for i in range(3)), s.zeros(70, 1)))
    covariant = [phi_dot, *Di]
    equal(sum((h[0, mu]*covariant[mu] for mu in range(4)), s.zeros(70, 1)), Pi_phi)
    scalar_potential = dot(phi-v, phi-v)
    Lscalar = sum(h[mu, nu]*dot(covariant[mu], covariant[nu])/2 for mu in range(4) for nu in range(4))-n*scalar_potential
    Hscalar = s.factor(dot(Pi_phi, phi_dot)-Lscalar)
    assert s.expand(Hscalar-n*u**2*(s.Rational(73, 200)-radial**2/4)) == 0
    for R in rho70: zero(dot(Pi_phi, R*phi))

    gauge_path = HERE/'source_gauge_legendre.json'; gauge = read(gauge_path)
    Gram = decode(gauge['native_Lie_algebra']['native_Lie_Gram'])
    magnetic = decode(gauge['original_Euler_currents_Gauss_boundary']['actual_source_curvature'])[3:, :]
    Q = clean(-W*hodge(e)/SIGMA)
    electric = rational(-Q[:3, :3].inv()*Q[:3, 3:]*magnetic)
    curvature = electric.col_join(magnetic)
    equal_rational((Q*curvature*Gram)[:3, :], s.zeros(3, 12))
    Hgauge = s.factor(-dot(curvature, Q*curvature*Gram)/2)
    c = s.simplify(s.trace(magnetic*Gram*magnetic.T)/(6*SIGMA))
    assert c == s.Rational(162, 625)

    Yukawa = s.MutableSparseMatrix.zeros(252, 252)
    scalar_vertices = []
    for index, word in enumerate(words):
        small = s.MutableSparseMatrix.zeros(63, 63)
        small[:7, 7:28] = wedge_yukawa(word)
        Y = clean(s.kronecker_product(s.diag(0, 0, 1, 1), small))
        scalar_vertices.append(Y)
        if phi[index] or phi[index+35]: Yukawa += (phi[index]+s.I*phi[index+35])*Y
    scalar_vertices += [s.I*Y for Y in scalar_vertices.copy()]
    Yukawa = clean(Yukawa)
    principal4 = [clean(n*sum((s.I*e.inv()[mu, a]*gamma[a] for a in range(4)), s.zeros(4))) for mu in range(4)]
    principal = [clean(s.kronecker_product(C, s.SparseMatrix.eye(63))) for C in principal4]
    lower = clean(sum((C*R for C, R in zip(principal, RA_matter)), s.SparseMatrix.zeros(252, 252))+n*Yukawa)
    Hmatter = s.factor(-s.re((chi*lower*psi)[0]))
    zero(Hmatter+n*(s.Rational(36, 5)+alpha*beta*u/2))
    family = candidate['actual_canonical_source_family']
    components = {'coframe_Lorentz_matter': Hcf, 'scalar': Hscalar, 'gauge': Hgauge, 'matter_without_Lorentz': Hmatter}
    for name, value in components.items():
        zero(value-s.sympify(family['common_Hamiltonian_components'][name], locals=symbols))
    for name, value in [('family_coframe', e), ('family_scalar', phi), ('family_scalar_momentum', Pi_phi),
                        ('family_primal', psi), ('family_independent_dual', chi), ('family_canonical_matter_momentum', p)]:
        equal(value, decode(family[name], symbols))
    equal(coframe_momentum, decode(family['original_coframe_momentum']))
    equal((Q*curvature*Gram)[:3, :].applyfunc(s.cancel), decode(family['original_gauge_momentum']))
    total_H = s.factor(sum(components.values()))
    zero(total_H-s.sympify(family['common_Hamiltonian'], locals=symbols))
    clock_coefficient = s.factor((Hcf+Hscalar+Hmatter)/n)
    zero(clock_coefficient-s.sympify(family['generated_clock_coefficient'], locals=symbols))
    print('PASS original four untruncated densities, generic alpha/beta/u/radial canonical family and actual zero coframe/gauge momenta', flush=True)

    # Raw fixed-velocity coframe stresses: differentiate only coefficients,
    # then evaluate the Legendre-generated velocities. Do not freeze a stale
    # raw time jet or differentiate the already substituted velocity itself.
    coordinates = [n, *shift]
    raw_stresses = {name: [] for name in components}
    for x in coordinates:
        raw_stresses['coframe_Lorentz_matter'].append(s.cancel(-3*s.diff(n, x)+
            dot(Omega, Hessian.diff(x)*Omega)/2+dot(Omega, current.diff(x))))
        raw_stresses['scalar'].append(s.cancel(sum(h.diff(x)[mu, nu]*dot(covariant[mu], covariant[nu])/2
            for mu in range(4) for nu in range(4))-s.diff(n, x)*scalar_potential))
        raw_stresses['gauge'].append(s.cancel(dot(curvature, Q.diff(x)*curvature*Gram)/2))
        raw_stresses['matter_without_Lorentz'].append(s.cancel(s.re((chi*lower.diff(x)*psi)[0])))
    for name, values in raw_stresses.items():
        for x, value in zip(coordinates, values): zero(value+s.diff(components[name], x))
    constraints = rational(s.Matrix([sum(raw_stresses[name][i] for name in components) for i in range(4)]))
    equal_rational(constraints, decode(family['four_canonical_temporal_constraints'], symbols))
    N = s.sympify(active['source_lapse'])
    source_point = {n: N, u: 0, alpha: 0, beta: 0, radial: 0, **dict.fromkeys(shift, 0)}
    equal_rational(constraints.subs(source_point), s.zeros(4, 1))
    source_J = rational(constraints.jacobian(coordinates).subs(source_point))
    equal(source_J, decode(family['actual_source_temporal_Jacobian']))
    assert s.simplify(source_J.det()) == s.Rational(800, 3)
    radius = dot(shift, shift)
    for i in range(3): zero(constraints[i+1]+4*c*n*shift[i]/(n**2-radius)**2)
    stationary = rational(constraints.subs(dict.fromkeys(shift, 0)))
    zero(n**2*stationary[0]+clock_coefficient*n**2-3*c)
    branch_J = rational(constraints.jacobian(coordinates).subs(dict.fromkeys(shift, 0)))
    equal_rational(branch_J, s.diag(-6*c/n**3, *[-4*c/n**3]*3))
    zero(branch_J.det()-384*c**4/n**12)
    assert s.simplify((3*c/clock_coefficient).subs({u: 0, alpha: 0, beta: 0, radial: 0})) == s.Rational(54, 125)
    print('PASS raw4 time-coframe stresses equal fixed-canonical derivatives, source determinant800/3 and exact positive nonlinear clock branch', flush=True)

    initial = candidate['nonlinear_constraint_satisfying_initial_jet']
    parameters = {u: s.Rational(1, 4), alpha: 1, beta: 1, radial: s.Rational(1, 3), **dict.fromkeys(shift, 0)}
    coefficient = s.factor(clock_coefficient.subs(parameters))
    square = s.factor((3*c/clock_coefficient).subs(parameters))
    assert coefficient == s.Rational(48847, 28800) and square == s.Rational(559872, 1221175)
    parameters[n] = s.sqrt(square)
    at = lambda A: clean(A.subs(parameters))
    eI, psiI, chiI, phiI, pI = map(at, (e, psi, chi, phi, p))
    omegaI = at(Omega); EI = at(E); lowerI = at(lower)
    spin = [gamma[i]*gamma[j]/2 for i, j in PAIRS]
    complete_lower = clean(lowerI+sum((omegaI[6*mu+a]*s.kronecker_product(at(principal4[mu])*spin[a], s.eye(63))
        for mu in range(4) for a in range(6)), s.SparseMatrix.zeros(252, 252)))
    psi_dot = clean(-EI.inv()*complete_lower*psiI)
    chi_dot = clean(chiI*complete_lower*EI.inv())
    equal(EI*psi_dot+complete_lower*psiI, s.zeros(252, 1))
    equal(chiI*complete_lower-chi_dot*EI, s.zeros(1, 252))
    equal(psi_dot, decode(initial['actual_full252_matter_time_velocity']))
    equal(chi_dot, decode(initial['actual_full252_dual_time_velocity']))
    for name, value in [('coframe', eI), ('scalar', phiI), ('scalar_canonical_momentum', at(Pi_phi)),
                        ('primal', psiI), ('independent_dual', chiI), ('canonical_matter_momentum', pI),
                        ('actual_scalar_time_velocity', at(phi_dot)), ('actual_gauge_time_velocity', at(electric))]:
        equal(value, decode(initial[name]))
    assert at(phi_dot) != s.zeros(70, 1)
    equal_rational(at(constraints), s.zeros(4, 1))
    equal(decode(initial['all64_first_coframe_jets']), s.zeros(64, 1))
    equal(decode(initial['all_symmetric_second_coframe_jets']), s.zeros(4, 64))

    # Direct all16 original Euler readback at this new homogeneous jet.
    # Its only nonzero coefficient derivative is the matter spin-density
    # time derivative; all spatial field jets and e_dot are actually zero.
    densityI = at(density)
    density_dot = clean(psi_dot.reshape(4, 63)*chiI.reshape(4, 63).T+
        psiI.reshape(4, 63)*chi_dot.reshape(4, 63).T)
    EI4, portsI = original_density_ports(eI, gamma)
    current_dot = s.Matrix([s.expand(s.re(s.trace(V*density_dot))) for V in portsI])
    omega_dot = clean(-at(inverse)*current_dot)
    hI = at(h); volume = eI.det(); inv_e = eI.inv(); metric = eI.T*s.diag(-1, 1, 1, 1)*eI
    FI = at(curvature); covI = list(map(at, covariant))
    dpsi = [psi_dot, *[s.zeros(252, 1)]*3]
    matter_cov = [dpsi[mu]+RA_matter[mu]*psiI for mu in range(4)]
    traces = [clean(vector.reshape(4, 63)*chiI.reshape(4, 63).T) for vector in matter_cov]
    yukawa_pair = s.re((chiI*at(Yukawa)*psiI)[0]).expand()
    Euler = []
    for index in range(16):
        delta = s.zeros(4); delta[index//4, index % 4] = 1
        dvolume = volume*s.trace(inv_e*delta)
        dinverse = -inv_e*delta*inv_e
        dC = [clean(sum((s.I*(dvolume*inv_e[mu, a]+volume*dinverse[mu, a])*gamma[a] for a in range(4)), s.zeros(4))) for mu in range(4)]
        dj = s.Matrix([s.expand(s.re(s.trace(dC[mu]*spin[a]*densityI))) for mu in range(4) for a in range(6)])
        dH = Hsymbol.diff(generic_e[index]).xreplace(dict(zip(generic_e, eI)))
        gravity_force = -3*dvolume+dot(omegaI, dH*omegaI)/2+dot(omegaI, dj)-(at(G)[:, :16].T*omega_dot)[index]
        dg = delta.T*s.diag(-1, 1, 1, 1)*eI+eI.T*s.diag(-1, 1, 1, 1)*delta
        dh = dvolume*metric.inv()-volume*metric.inv()*dg*metric.inv()
        scalar_force = sum(dh[mu, nu]*dot(covI[mu], covI[nu])/2 for mu in range(4) for nu in range(4))-dvolume*at(phi-v).dot(at(phi-v))
        _, dstarF = hodge_field_jet(eI, delta, FI, s.zeros(6, 12))
        gauge_force = -dot(FI, W*dstarF*Gram)/(2*SIGMA)
        matter_force = dvolume*yukawa_pair+sum(s.re(s.trace(dC[mu]*traces[mu])) for mu in range(4))
        Euler.append(s.expand(gravity_force+scalar_force+gauge_force+matter_force))
    Euler = clean(s.Matrix(Euler))
    equal(Euler, decode(initial['remaining_initial_Euler_data']))
    equal(Euler.extract([0, 4, 8, 12], [0]), s.zeros(4, 1))
    Lorentz = s.Matrix.hstack(*((T*eI).reshape(16, 1) for T in GENERATORS))
    equal(Lorentz.T*Euler, s.zeros(6, 1))
    beta_form = s.zeros(4, 24)
    Cform = INTERNAL_J*lorentz_exterior(eI)*WEDGE
    for pair, (mu, nu) in enumerate(PAIRS):
        for a in range(6):
            beta_form[mu, 6*nu+a] += Cform[a, pair]
            beta_form[nu, 6*mu+a] -= Cform[a, pair]
    equal(beta_form*omegaI, decode(initial['original_four_BF_boundary_fluxes']))
    print('PASS independent all16 original coframe Euler at nonlinear initial jet, both252 matter equations, all6 Lorentz projections and four BF fluxes', flush=True)

    scalar_charge = s.Matrix([dot(at(Pi_phi), R*phiI) for R in rho70])
    matter_charge = s.Matrix([s.re((chiI*s.kronecker_product(EI4, R)*psiI)[0]).expand() for R in rho63])
    equal(scalar_charge+matter_charge, s.zeros(12, 1))
    equal(orbit.T*phiI, s.zeros(12, 1)); equal(orbit.T*at(phi_dot), s.zeros(12, 1))
    jY = s.Matrix([s.expand(volume*s.re((chiI*Y*psiI)[0])) for Y in scalar_vertices])
    equal(jY, decode(initial['nonzero_full_Yukawa_scalar_source']))
    scalar_rest = clean(-volume*sum((RA[i+1]*RA[i+1]*phiI for i in range(3)), s.zeros(70, 1))-
                        2*volume*(phiI-v))
    equal(orbit.T*scalar_rest, s.zeros(12, 1))
    rhs_rate = clean(orbit.T*jY/hI[0, 0])
    live_D = clean(orbit.T*s.Matrix.hstack(*(R*phiI for R in rho70)))
    solved, free = (live_D*s.eye(12)[:, broken]).gauss_jordan_solve(rhs_rate)
    assert free.rows == 0
    A0dot = clean(s.eye(12)[:, broken]*solved)
    equal(A0dot, decode(initial['nonzero_source_time_gauge_connection_rate']))
    assert A0dot != s.zeros(12, 1)
    equal(decode(initial['generated_time_gauge_connection']), s.zeros(12, 1))
    assert initial['local_initial_data_not_global_Cauchy_solution'] is True
    assert candidate['complete_constraint_preservation_global_Cauchy_or_spectrum_claimed'] is False
    print('PASS total Gauss/C/dotC, actual nonzero scalar velocity and full Yukawa-driven gauge-time response', flush=True)

    count += bindings(active)+bindings(occupied)+bindings(gauge)
    paths = [candidate_path, HERE/'source_coframe_initial_constraints.py', Path(__file__),
        HERE/'independent_source_gauge_legendre.py', HERE/'independent_source_lorentz_contact.py',
        HERE/'independent_source_constraint_preservation.py', active_path, occupied_path, gauge_path,
        BASE/'exact_readout.py', ROOT/'Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean']
    result = {'verdict': 'CERTIFIED_ORIGINAL_NONLINEAR_CANONICAL_COFRAME_INITIAL_BRANCH_AND_FULL_EULER_JET',
        'root': ROOT_ID, 'source_sha256': hashes,
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_or_common_Hamiltonian_constructor_imported': False,
        'independent_algorithm': 'raw Levi-Civita gravity Hessian/load and original independent-dual spin density; raw scalar/gauge Legendre elimination; full252 Gamma/Yukawa density; fixed-velocity coframe stress first, then generated velocities; independent full16 original Euler and both matter equations',
        'source_binding_checks': count,
        'family_canonical_data': 'Pi_e=0,Pi_A=0 are the actual recomputed source momenta; Pi_phi=radial*u*q, q=P61 e23; psi=psi0+alpha e135, chi=chi0+beta e126; p=-i chi E fixed along time-coframe variables',
        'original_source_readback': 'u=alpha=beta=radial=0 and n=N,shift=0',
        'all16_coframe_momenta_and_full_Lorentz_shift_zero': True,
        'all70_scalar_and36_gauge_momenta_recovered_from_raw_density': True,
        'full_H_components': {name: str(value) for name, value in components.items()},
        'clock_coefficient': str(clock_coefficient), 'positive_clock_squared': '486/(625*a)',
        'raw_four_stresses_equal_fixed_canonical_Hamiltonian_derivative': True,
        'actual_source_constraint_Jacobian': {'shape': [int(x) for x in source_J.shape],
            'entries': [[int(i), int(j), str(value)] for (i, j), value in sorted(source_J.todok().items())]},
        'source_Jacobian_determinant': '800/3',
        'family_Jacobian_at_solved_column': 'diag(-6c/n^3,-4c/n^3,-4c/n^3,-4c/n^3), det=384c^4/n^12; c=162/625',
        'branch_domain': 'positive orientation n>0, original gauge electric block n^2-|shift|^2!=0 and a>0; the exact four constraints force shift=0 and the positive clock root in this displayed family',
        'analytic_local_branch': 'finite-jet mathematical implicit-function consequence of the actual nonzero source Jacobian and rational/analytic original canonical constraint map on its primary noncharacteristic chart; not a Lean analytic theorem or a global solution',
        'nonlinear_fixture': {'u': '1/4', 'alpha': 1, 'beta': 1, 'radial': '1/3',
            'a': '48847/28800', 'n_squared': '559872/1221175', 'scalar_velocity': '-n q/12, nonzero',
            'original_all16_coframe_Euler_matches': True, 'original_four_temporal_Euler_zero': True,
            'original_six_Lorentz_projection_zero': True, 'original_primal_and_independent_dual_Euler_zero': True,
            'Gauss_C_and_dotC_zero': True, 'nonzero_Yukawa_and_A0_rate': True, 'four_BF_fluxes_kept': True},
        'temporal_principal_generic_identity': 'adj(e)[0,:] and E have zero derivatives along e[:,0]; G_t has four zero time-coframe columns',
        'fixed_p_temporal_correction_zero_off_shell': True,
        'time_coframe_rates_selected_by_preservation': False,
        'uniform_all_frames_global_Cauchy_or_quantum_spectrum_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    zero(s.sympify(result['clock_coefficient'], locals=symbols)-
         s.sympify(family['generated_clock_coefficient'], locals=symbols))
    (HERE/'independent_source_coframe_initial_constraints.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent nonlinear coframe initial constraints audit', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
