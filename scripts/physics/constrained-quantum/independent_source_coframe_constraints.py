#!/usr/bin/env python3
"""Independent complete coframe Euler and source Lorentz Noether audit.

All internal63 entries are summed. The compact current evaluation below is
an explicit tensor contraction of the already certified original252 density,
without a matter subspace or an adjoint condition.
"""
from __future__ import annotations

import hashlib
import importlib.util
import itertools
import json
import sys
import time

import sympy as s

from independent_source_lorentz_contact import (
    ROOT_ID, HERE, BASE, ROOT, PAIRS, GENERATORS, J, WEDGE,
    original_gamma, clean, equal, matrix, exterior, original_density_ports,
)
from independent_source_coframe_legendre import original_geometry, actual_geometry, source_null_frame
from independent_source_common_hamiltonian import (
    original_inventory, original_boson_inventory, raw_matter,
    original_matter_euler, source_fixture,
)


def spin_contraction(primal, dual):
    return s.Matrix(4, 4, lambda a, b: sum(primal[63*a+m]*dual[63*b+m] for m in range(63)))


def evaluate_spin(matrix, contraction):
    return s.expand(s.re(sum(coefficient*contraction[b, a]
        for (a, b), coefficient in s.SparseMatrix(matrix).todok().items())))


def principals(e, direction=None):
    inverse, volume = e.inv(), s.Abs(e.det())
    if direction is None:
        coefficients = volume*inverse
    else:
        coefficients = volume*(s.trace(inverse*direction)*inverse-inverse*direction*inverse)
    gamma = original_gamma()
    return [clean(s.I*sum((coefficients[mu, a]*gamma[a] for a in range(4)), s.zeros(4)))
            for mu in range(4)]


def lorentz_ports(e, direction=None):
    gamma = original_gamma()
    return [clean(D*gamma[a]*gamma[b]/2) for D in principals(e, direction) for a, b in PAIRS]


def currents(e, psi, chi, direction=None, dpsi=None, dchi=None):
    density = spin_contraction(psi, chi)
    if direction is None:
        return s.Matrix([evaluate_spin(V, density) for V in lorentz_ports(e)])
    d_density = spin_contraction(dpsi, chi)+spin_contraction(psi, dchi) if dpsi is not None else s.zeros(4)
    return s.Matrix([evaluate_spin(dV, density)+evaluate_spin(V, d_density)
        for V, dV in zip(lorentz_ports(e), lorentz_ports(e, direction))])


def original_gravity_euler(e, de, dde, psi, dpsi, chi, dchi):
    variables, _, H, _, G, _, _, _, f = original_geometry()
    substitution = dict(zip(variables, e))
    geometry = actual_geometry(e)
    j = currents(e, psi, chi)
    Omega = clean(-geometry['inverse']*(geometry['G']*de+j))
    force = s.zeros(16, 1)
    dH = [clean(H.diff(value).xreplace(substitution)) for value in variables]
    dG = [clean(G.diff(value).xreplace(substitution)) for value in variables]
    for a in range(16):
        direction = s.zeros(4)
        direction[a] = 1
        dj = currents(e, psi, chi, direction)
        force[a] = s.expand(-3*e.adjugate()[a % 4, a//4]+
            (Omega.T*dH[a]*Omega)[0]/2+(Omega.T*dG[a]*de)[0]+(Omega.T*dj)[0])
    divergence = s.zeros(16, 1)
    derivatives = s.zeros(4, 24)
    for mu in range(4):
        local = de[16*mu:16*(mu+1), :]
        H_mu = clean(sum((local[a]*dH[a] for a in range(16)), s.zeros(24)))
        G_mu = clean(sum((local[a]*dG[a] for a in range(16)), s.zeros(24, 64)))
        dj = currents(e, psi, chi, s.Matrix(4, 4, local), dpsi[mu], dchi[mu])
        derivative = clean(-geometry['inverse']*(H_mu*Omega+G_mu*de+geometry['G']*dde[mu, :].T+dj))
        derivatives[mu, :] = derivative.T
        divergence += G_mu[:, 16*mu:16*(mu+1)].T*Omega+geometry['G'][:, 16*mu:16*(mu+1)].T*derivative
    return {'Euler': clean(force-divergence), 'connection': Omega, 'connection_derivative': derivatives}


def original_remaining_stress(e, phi, dphi, A, dA, psi, dpsi, chi):
    matter = raw_matter(e, phi, A)
    bosons = original_boson_inventory()
    U = [dphi[mu]+sum((A[mu, a]*bosons['scalar'][a]*phi for a in range(12)), s.zeros(70, 1))
         for mu in range(4)]
    covariant = [dpsi[mu]+matter['gauge'][mu]*psi for mu in range(4)]
    contracted = [spin_contraction(value, chi) for value in covariant]
    yukawa = s.expand(s.re((chi*matter['Y']*psi)[0]))
    fluctuation = phi-original_inventory()['vacuum']
    F = s.MutableSparseMatrix.zeros(6, 12)
    for p, (mu, nu) in enumerate(PAIRS):
        F[p, :] = dA[mu, 12*nu:12*(nu+1)]-dA[nu, 12*mu:12*(mu+1)]
        for (a, b, c), coefficient in bosons['structure'].items():
            F[p, c] += coefficient*A[mu, a]*A[nu, b]
    t = s.Symbol('audit_stress_curve', real=True)
    result = {key: [] for key in ('scalar', 'gauge', 'matter_without_Lorentz')}
    # Independent direct density derivatives; all source matter currents are
    # held independent of the varied coframe until the canonical chain is paid.
    for a in range(16):
        delta = s.zeros(4)
        delta[a] = 1
        curve = e+t*delta
        volume = s.sign(e.det())*curve.det()
        metric = volume*curve.inv()*s.diag(-1, 1, 1, 1)*curve.inv().T
        scalar = sum(metric[mu, nu]*(U[mu].T*U[nu])[0]/2 for mu, nu in itertools.product(range(4), repeat=2))-\
            volume*(fluctuation.T*fluctuation)[0]
        X = exterior(curve)
        kernel = -2*X.T*s.diag(-1, -1, -1, 1, 1, 1)*X/curve.det()
        gauge = sum((F*bosons['gram'])[i, b]*(kernel*F)[i, b]/2 for i in range(6) for b in range(12))
        result['scalar'].append(s.cancel(s.diff(scalar, t).subs(t, 0)))
        result['gauge'].append(s.cancel(s.diff(gauge, t).subs(t, 0)))
        dD = principals(e, delta)
        result['matter_without_Lorentz'].append(s.expand(sum(evaluate_spin(D, density)
            for D, density in zip(dD, contracted))+s.sign(e.det())*e.adjugate()[a % 4, a//4]*yukawa))
    return {key: s.Matrix(value) for key, value in result.items()}


def generic_source_invariance():
    e, determinant, H, K, G, _, _, _, _ = original_geometry()
    C = J*exterior(e)*WEDGE
    gamma = original_gamma()
    spin = [gamma[a]*gamma[b]/2 for a, b in PAIRS]
    adjugate = e.adjugate()
    D = [sum((s.I*adjugate[mu, a]*gamma[a] for a in range(4)), s.zeros(4)) for mu in range(4)]
    gauge_kernel_numerator = -2*exterior(e).T*s.diag(-1, -1, -1, 1, 1, 1)*exterior(e)
    for T, S in zip(GENERATORS, spin):
        velocity = s.Matrix(list(T*e))
        equal(T.T*s.diag(-1, 1, 1, 1)+s.diag(-1, 1, 1, 1)*T, s.zeros(4))
        assert s.expand(sum(velocity[a]*s.diff(determinant, e[a]) for a in range(16))) == 0
        adjoint = s.Matrix(6, 6, lambda i, j: s.diag(-1, 1, 1, 1)[PAIRS[i][0], PAIRS[i][0]]*
                           (T*GENERATORS[j]-GENERATORS[j]*T)[PAIRS[i][0], PAIRS[i][1]])
        for j in range(6):
            equal(S*spin[j]-spin[j]*S, sum((adjoint[i, j]*spin[i] for i in range(6)), s.zeros(4)))
        equal(sum((velocity[a]*C.diff(e[a]) for a in range(16)), s.zeros(6))+adjoint.T*C, s.zeros(6))
        for principal in D:
            equal(sum((velocity[a]*principal.diff(e[a]) for a in range(16)), s.zeros(4)), S*principal-principal*S)
        equal(S*s.diag(0, 0, 1, 1), s.diag(0, 0, 1, 1)*S)
        equal(sum((velocity[a]*gauge_kernel_numerator.diff(e[a]) for a in range(16)), s.zeros(6)), s.zeros(6))
    temporal = [0, 4, 8, 12]
    equal(G[:, temporal], s.zeros(24, 4))
    for a in temporal:
        equal(D[0].diff(e[a]), s.zeros(4))
    equal((G[:, :16].T*K*G[:, :16]).extract(temporal, list(range(16))), s.zeros(4, 16))
    return {'generic_coframe_variables': 16, 'Lorentz_generators': 6, 'Dirac_principal_commutators': 24,
        'source_spin_lift_Lie_commutators': 36,
        'original_gauge_and_scalar_spin_invariance': True, 'all70_Yukawa_spin_commutation': True,
        'four_temporal_momenta_zero': True, 'four_temporal_E_derivatives_zero': True,
        'four_temporal_fixed_p_correction_zero_without_matter_equations': True,
        'pure_second_time_coframe_derivative_coefficients_zero': True}


def main():
    began = time.monotonic()
    path = HERE/'source_coframe_constraints.json'
    candidate = json.loads(path.read_bytes())
    assert candidate['root'] == ROOT_ID
    checked_bindings = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in candidate[key].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            checked_bindings += 1
    common_audit = json.loads((HERE/'independent_source_common_hamiltonian.json').read_bytes())
    assert common_audit['verdict'] == 'CERTIFIED_ORIGINAL_COMMON_LOCAL_HAMILTONIAN_WITH_FULL_SOURCE_MATTER_EULER_AND_FIXED_CANONICAL_VARIABLES'
    generic = generic_source_invariance()
    print('PASS original generic16 Lorentz/Dirac/scalar/gauge covariance,36 spin Lie brackets and four temporal principal/acceleration identities', flush=True)

    spec = importlib.util.spec_from_file_location('coframe_constraints_api_under_audit', HERE/'source_coframe_constraints.py')
    api = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = api
    spec.loader.exec_module(api)
    model = api.SourceCoframeConstraints()
    frame = s.Matrix([[2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    e, de, phi, dphi, A, dA, psi, dpsi, chi = source_fixture(frame)
    raw = raw_matter(e, phi, A)
    p = clean(-s.I*chi*raw['E'])
    spatial_p = [s.zeros(1, 252) for _ in range(3)]
    chi, dpsi, dchi = model.on_matter_flow(e, de, phi, A, psi, p, dpsi[1:], spatial_p)
    dde = s.Matrix(4, 64, lambda mu, j: s.Rational((mu+j//16+1)*((j % 16) % 5-2), 71))
    j = currents(e, psi, chi)
    # The independent old 252 formula is evaluated once on the complete
    # internal carrier. Indexed63 contraction then pays all derivative reads.
    full_current = s.Matrix([s.expand(s.re((chi*s.kronecker_product(V, s.eye(63))*psi)[0]))
                            for V in lorentz_ports(e)])
    equal(j, full_current)
    assert chi != psi.H
    assert currents(e, psi, chi) != currents(e, psi, psi.H)
    for mu in range(4):
        direction = s.Matrix(4, 4, de[16*mu:16*(mu+1), :])
        dj = currents(e, psi, chi, direction, dpsi[mu], dchi[mu])
        # This is an ordinary scalar-parameter derivative of the source
        # bilinear, not a differentiation rule supplied by the candidate.
        t = s.Symbol('audit_current_curve', real=True)
        density = spin_contraction(psi+t*dpsi[mu], chi+t*dchi[mu])
        coefficient = []
        for V, dV in zip(lorentz_ports(e), lorentz_ports(e, direction)):
            coefficient.append(s.expand(s.diff(evaluate_spin(V+t*dV, density), t).subs(t, 0)))
        equal(dj, s.Matrix(coefficient))
    print('PASS complete252 direct Kronecker source current equals independent indexed63 contraction, with all96 actual derivative rows and independent dual', flush=True)

    gravity = original_gravity_euler(e, de, dde, psi, dpsi, chi, dchi)
    native_gravity = model.lorentz_euler(e, de, dde, psi, dpsi, chi, dchi)
    for key in ('Euler', 'connection', 'connection_derivative'):
        equal(native_gravity[key], gravity[key])
    remaining = original_remaining_stress(e, phi, dphi, A, dA, psi, dpsi, chi)
    native_remaining = model.remaining_stress(e, phi, dphi, A, dA, psi, dpsi, chi)
    for key, value in remaining.items():
        equal(native_remaining[key], value)
    total = clean(gravity['Euler']+sum(remaining.values(), s.zeros(16, 1)))
    result = model.euler(e, de, dde, phi, dphi, A, dA, psi, dpsi, chi, dchi)
    equal(result['Euler'], total)
    Z = source_null_frame(e)
    equal(Z[:, 4:].T*total, s.zeros(6, 1))
    original_matter = original_matter_euler(e, de, phi, A, psi, chi, dpsi, dchi, gravity['connection'].reshape(4, 6))
    equal(original_matter['primal'], s.zeros(252, 1))
    equal(original_matter['dual'], s.zeros(1, 252))
    temporal = total.extract([0, 4, 8, 12], [0])
    equal(temporal, matrix(candidate['temporal_constraints']))
    equal(temporal, result['temporal_coframe'])
    assert temporal.todok()
    equal(native_gravity['boundary_flux'], matrix(candidate['BF_boundary_flux']))
    print('PASS all16 independently rebuilt gravity+scalar+gauge+remaining Dirac coframe Euler: six Noether directions zero on full matter flow and four exact nonzero initial constraints', flush=True)

    off_dpsi = [value.copy() for value in dpsi]
    off_dchi = [value.copy() for value in dchi]
    off_dpsi[0][5] += 1
    off_dchi[0][130] += s.I
    off_gravity = original_gravity_euler(e, de, dde, psi, off_dpsi, chi, off_dchi)
    off_remaining = original_remaining_stress(e, phi, dphi, A, dA, psi, off_dpsi, chi)
    off_total = clean(off_gravity['Euler']+sum(off_remaining.values(), s.zeros(16, 1)))
    off = model.euler(e, de, dde, phi, dphi, A, dA, psi, off_dpsi, chi, off_dchi)
    equal(off['Euler'], off_total)
    off_matter = original_matter_euler(e, de, phi, A, psi, chi, off_dpsi, off_dchi, gravity['connection'].reshape(4, 6))
    noether = []
    gamma = original_gamma()
    for a, b in PAIRS:
        S = s.kronecker_product(gamma[a]*gamma[b]/2, s.eye(63))
        noether.append(s.expand(s.re((off_matter['dual']*S*psi-chi*S*off_matter['primal'])[0])))
    projection = clean(Z[:, 4:].T*off_total)
    equal(projection+s.Matrix(noether), s.zeros(6, 1))
    assert projection.todok()
    # Neither time matter perturbation changes the four source constraints:
    # delta_e[:,0] E=0 and the temporal coframe momentum is identically zero.
    equal(off_total.extract([0, 4, 8, 12], [0]), temporal)
    print('PASS independent off-shell six Noether identities and four temporal constraints independent of the perturbed matter time jets', flush=True)

    paths = [HERE/name for name in ('source_coframe_constraints.py', 'source_coframe_constraints.json',
        'independent_source_coframe_constraints.py', 'independent_source_common_hamiltonian.py',
        'independent_source_common_hamiltonian.json', 'independent_source_coframe_legendre.py',
        'independent_source_coframe_legendre.json', 'independent_source_lorentz_contact.py')]
    output = {'root': ROOT_ID,
        'verdict': 'CERTIFIED_ORIGINAL_COMPLETE_COFRAME_EULER_LORENTZ_NOETHER_AND_FOUR_TEMPORAL_CONSTRAINTS',
        'scope': candidate['scope'], 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_bindings_verified': checked_bindings,
        'generic_source_identities': generic,
        'complete_internal_trace_consumer': {'complex_matter_dimension': 252, 'internal_summands': 63,
            'independent_dual': True, 'direct_full252_Kronecker_rows': 24, 'current_spacetime_derivative_rows': 96,
            'adjoint_substitution_negative_control_nonzero': True},
        'original_complete_coframe_Euler': {'coordinates': 16,
            'sectors': ['original gravity and full Lorentz current', 'full70 scalar', 'native12 gauge', 'Omega=0 remaining full252 Dirac'],
            'independent_scalar_and_gauge_stress_algorithm': 'direct original density derivatives on every coframe coordinate',
            'independent_matter_stress_algorithm': 'Jacobi inverse/absolute-volume derivative of all four original principals and full Yukawa density',
            'on_matter_flow_primal_and_dual_rows_zero': [252, 252],
            'six_Lorentz_projections_zero': True, 'off_shell_six_Noether_matter_terms_nonzero_and_exact': True},
        'uniform_Noether_argument': 'The verified source so(1,3) lift respects all36 brackets; all24 principal commutators and gravity coefficient covariance cancel constant parameters. The connection variation [T,Omega]-dT cancels every parameter derivative in curvature and the original matter covariant derivative. Auxiliary Euler is identically zero after exact elimination; the original Euler identity follows with the already retained BF boundary.',
        'temporal_constraints': candidate['temporal_constraints'],
        'four_time_fixed_p_corrections_zero_off_shell': True,
        'temporal_constraints_independent_of_matter_time_jets': True,
        'pure_coframe_acceleration_coefficients_zero': True,
        'boundary_flux_preserved': True,
        'actual_producer_API': candidate['actual_API'],
        'all_four_secondary_constraints_solved_or_preserved': False,
        'full_joint_Cauchy_or_quantum_spectrum_claimed': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_coframe_constraints.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS independent full coframe constraint certification', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
