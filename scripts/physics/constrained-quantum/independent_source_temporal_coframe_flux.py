#!/usr/bin/env python3
"""Independent source flux, multiplier transport and primary-field jet audit.

The momentum jet is differentiated on the original Legendre graph. Spatial
primary tangency is verified separately from its value at the base point.
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
    original_gamma, clean, equal, matrix, exterior,
)
from independent_source_coframe_legendre import (
    original_geometry, actual_geometry, quotient_right_inverse, quotient_inverse, source_null_frame,
)
from independent_source_common_hamiltonian import raw_matter, original_inventory, original_boson_inventory
from independent_source_coframe_constraints import spin_contraction, evaluate_spin, principals, lorentz_ports

TIME = (0, 4, 8, 12)
INJECTION = s.SparseMatrix(16, 12, {(4*a+i+1, 4*i+a): 1 for i in range(3) for a in range(4)})


def split(spatial):
    retained = spatial.copy()
    values = []
    for i, a in itertools.product(range(3), range(4)):
        values.append(spatial[16*i+4*a])
        retained[16*i+4*a] = 0
    return retained, s.Matrix(values)


def current_and_derivative(e, psi, p, direction=None):
    E = principals(e)[0]
    inverse = E.inv()
    density = spin_contraction(psi, p)
    V = lorentz_ports(e)
    current = s.Matrix([evaluate_spin(s.I*inverse*value, density) for value in V])
    if direction is None:
        return current
    dE = principals(e, direction)[0]
    dV = lorentz_ports(e, direction)
    return s.Matrix([evaluate_spin(s.I*(-inverse*dE*inverse*value+inverse*change), density)
                     for value, change in zip(V, dV)])


def source_H(fields, spatial, momentum, multipliers):
    e = fields['e']
    geometry = actual_geometry(e)
    R, Z = quotient_right_inverse(e), source_null_frame(e)
    Q = clean(R*quotient_inverse(e, geometry['h'])*R.T)
    q = geometry['Gs']*spatial+current_and_derivative(e, fields['psi'], fields['p'])
    shift = -geometry['Gt'].T*geometry['inverse']*q
    changed = momentum-shift
    return s.expand((changed.T*Q*changed)[0]/2+3*e.det()+
        (q.T*geometry['inverse']*q)[0]/2+(multipliers.T*Z.T*changed)[0])


def raw_four_forces(e, de, phi, dphi, A, dA, psi, dpsi, chi):
    """Original densities differentiated at fixed independent chi and raw jets."""
    coordinates, _, _, K, G, _, _, _, _ = original_geometry()
    matter, inventory = raw_matter(e, phi, A), original_boson_inventory()
    U = [dphi[mu]+sum((A[mu, a]*inventory['scalar'][a]*phi for a in range(12)), s.zeros(70, 1))
         for mu in range(4)]
    covariant = [dpsi[mu]+matter['gauge'][mu]*psi for mu in range(4)]
    matter_contractions = [spin_contraction(value, chi) for value in covariant]
    yukawa = s.expand(s.re((chi*matter['Y']*psi)[0]))
    density = spin_contraction(psi, chi)
    fluctuation = phi-original_inventory()['vacuum']
    F = s.zeros(6, 12)
    for p, (mu, nu) in enumerate(PAIRS):
        F[p, :] = dA[mu, 12*nu:12*(nu+1)]-dA[nu, 12*mu:12*(mu+1)]
        for (a, b, c), coefficient in inventory['structure'].items():
            F[p, c] += coefficient*A[mu, a]*A[nu, b]
    FG = F*inventory['gram']
    gamma = original_gamma()
    t = s.Symbol('audit_time_column', real=True)
    output = []
    for a in range(4):
        delta = s.zeros(4)
        delta[a, 0] = 1
        curve = e+t*delta
        substitution = dict(zip(coordinates, curve))
        adj = curve.adjugate()
        D = [s.sign(e.det())*s.I*sum((adj[mu, b]*gamma[b] for b in range(4)), s.zeros(4)) for mu in range(4)]
        j = s.Matrix([evaluate_spin(value*gamma[b]*gamma[c]/2, density) for value in D for b, c in PAIRS])
        current = G.xreplace(substitution)*de+j
        gravity = -3*curve.det()-(current.T*K.xreplace(substitution)*current)[0]/(2*curve.det())
        volume = s.sign(e.det())*curve.det()
        metric = volume*curve.inv()*s.diag(-1, 1, 1, 1)*curve.inv().T
        scalar = sum(metric[mu, nu]*(U[mu].T*U[nu])[0]/2 for mu, nu in itertools.product(range(4), repeat=2))-\
            volume*(fluctuation.T*fluctuation)[0]
        X = exterior(curve)
        KF = -2*X.T*s.diag(-1, -1, -1, 1, 1, 1)*X*F/curve.det()
        gauge = sum(FG[i, b]*KF[i, b]/2 for i in range(6) for b in range(12))
        dirac = volume*yukawa+sum(evaluate_spin(value, contraction) for value, contraction in zip(D, matter_contractions))
        output.append(s.cancel(s.diff(gravity+scalar+gauge+dirac, t).subs(t, 0)))
    return s.Matrix(output)


def main():
    began = time.monotonic()
    path = HERE/'source_temporal_coframe_flux.json'
    candidate = json.loads(path.read_bytes())
    assert candidate['root'] == ROOT_ID
    count = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in candidate[key].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            count += 1
    evars, _, H, _, G, _, Dh, _, f = original_geometry()
    Z = source_null_frame(evars)[:, 4:]
    equal(G[:, :16]*Z, H[:, :6])
    equal(G[:6, :16], s.zeros(6, 16))
    equal(G[:, list(TIME)], s.zeros(24, 4))
    gradient_columns = [16*(i+1)+4*a for i in range(3) for a in range(4)]
    equal(G[:, gradient_columns], -G[:, :16]*INJECTION)
    for a in TIME:
        equal(G[:6, 16:].diff(evars[a]), s.zeros(6, 48))
        equal(f.diff(evars[a]), s.zeros(24, 1))
    for i in range(3):
        equal(G[:6, 16*(i+1):16*(i+2)], f[6*(i+1):6*(i+2), :].jacobian(list(evars)))
    print('PASS independent original curl, Lorentz/BF momentum and temporal-independent primary coefficients', flush=True)

    spec = importlib.util.spec_from_file_location('temporal_flux_api_under_audit', HERE/'source_temporal_coframe_flux.py')
    api = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = api
    spec.loader.exec_module(api)
    model = api.SourceTemporalCoframeFlux()
    fields, spatial, retained, v, momentum = api.example_fields(model)
    e, psi, p = fields['e'], fields['psi'], fields['p']
    original = actual_geometry(e)
    retained0, gradient0 = split(spatial)
    equal(retained, retained0)
    equal(model.J, INJECTION)
    R, Z0 = quotient_right_inverse(e), source_null_frame(e)
    Q = clean(R*quotient_inverse(e, original['h'])*R.T)
    null_reader = R.row_join(Z0).inv()[6:, :]
    gradient = s.Matrix(s.symbols('audit_gradient0:12', real=True))
    Pi = s.Matrix(s.symbols('audit_Pi0:16', real=True))
    lam = s.Matrix(s.symbols('audit_lambda0:10', real=True))
    translated = null_reader*(R*original['Dh']-s.eye(16))*INJECTION*gradient
    equal(Z0*translated, (R*original['Dh']-s.eye(16))*INJECTION*gradient)
    equal(model.multiplier_translation(e, gradient), translated)
    shifted_spatial = retained.copy()
    for i, a in itertools.product(range(3), range(4)):
        shifted_spatial[16*i+4*a] = gradient[4*i+a]
    first = source_H(fields, shifted_spatial, Pi, lam)
    second = source_H(fields, retained, Pi, lam+translated)
    flux_density = (Pi.T*INJECTION*gradient)[0]
    assert s.expand(first-second-flux_density) == 0
    without = source_H(fields, retained, Pi, lam)
    defect = s.expand(first-without-flux_density)
    assert defect != 0
    q = original['Gs']*retained+current_and_derivative(e, psi, p)
    b = -original['Gt'].T*original['inverse']*q
    constraints = Z0.T*(Pi-b)
    assert s.expand(defect-(translated.T*constraints)[0]) == 0
    equal(momentum, original['M']*v+b)
    equal(Z0.T*(momentum-b), s.zeros(10, 1))
    substitute = dict(zip(Pi, momentum))
    assert s.expand((first-without-flux_density).xreplace(substitute)) == 0
    equal(s.Matrix([s.diff(first.xreplace(substitute), value) for value in gradient]), INJECTION.T*momentum)
    # Actual common API consumes the same coefficient; the other original
    # blocks have no coframe spatial-derivative argument at all.
    actual_first = model.common_H(fields, shifted_spatial, Pi, lam)
    actual_second = model.common_H(fields, retained, Pi, lam+translated)
    assert s.expand(actual_first['value']-actual_second['value']-flux_density) == 0
    equal(actual_first['coframe_primary'], constraints)
    equal(actual_second['coframe_primary'], constraints)
    for key in ('scalar', 'gauge', 'matter_without_Lorentz'):
        assert s.expand(actual_first['components'][key]-actual_second['components'][key]) == 0
    print('PASS complete off-primary common Hamiltonian for arbitrary Pi16/gradient12/lambda10, source multiplier translation and nonzero omitted-translation defect', flush=True)

    # Generate a genuine local Legendre graph field, with constant p and psi,
    # affine e and constant first e jets. No primary derivative is supplied.
    full_v = v+INJECTION*gradient0
    de = full_v.col_join(spatial)
    total = original['G']*de+current_and_derivative(e, psi, p)
    Omega = clean(-original['inverse']*total)
    equal(original['Gt'].T*Omega, momentum)
    point_sub = dict(zip(evars, e))
    spatial_Pi = s.zeros(3, 16)
    for i in range(3):
        direction = spatial[16*i:16*(i+1), :]
        dH = clean(sum((direction[a]*H.diff(evars[a]) for a in range(16)), s.zeros(24)).xreplace(point_sub))
        dG = clean(sum((direction[a]*G.diff(evars[a]) for a in range(16)), s.zeros(24, 64)).xreplace(point_sub))
        dj = current_and_derivative(e, psi, p, s.Matrix(4, 4, direction))
        dS = -original['inverse']*dH*original['inverse']
        spatial_Pi[i, :] = clean(-dG[:, :16].T*original['inverse']*total-
            original['Gt'].T*dS*total-original['Gt'].T*original['inverse']*(dG*de+dj)).T
    jet = candidate['actual_primary_field_Euler_consumer']
    equal(spatial_Pi, matrix(jet['spatial_canonical_coframe_momentum_jets']))
    equal(model.primary_rows(e, momentum, spatial, psi, p), s.zeros(10, 1))
    prolongation = model.primary_prolongations(e, momentum, spatial, spatial_Pi,
        [s.zeros(48, 1)]*3, psi, p, fields['spatial_psi'], fields['spatial_p'])
    equal(prolongation, s.zeros(3, 10))
    equal(prolongation, matrix(jet['all30_primary_spatial_prolongations']))
    # A point on the primary surface with an incompatible momentum jet is not
    # a primary field; the required spatial predicate detects it immediately.
    incompatible = spatial_Pi.copy()
    incompatible[0, 0] += 1
    bad = model.primary_prolongations(e, momentum, spatial, incompatible,
        [s.zeros(48, 1)]*3, psi, p, fields['spatial_psi'], fields['spatial_p'])
    assert bad.todok()
    print('PASS all30 primary spatial prolongations from the differentiated original momentum field; single-point-primary substitution rejected', flush=True)

    base_multiplier = null_reader*(v-Q*(momentum-b))
    multiplier = base_multiplier-model.multiplier_translation(e, gradient0)
    velocities = model.common.boson_velocities(e, momentum, spatial, fields['phi'], fields['Pi_phi'],
        fields['spatial_phi'], fields['A'], fields['Pi_A'], fields['spatial_A'], psi, p, multiplier)
    equal(velocities['coframe'], full_v)
    chi, dpsi, dchi = model.full.on_matter_flow(e, de, fields['phi'], fields['A'], psi, p,
        fields['spatial_psi'], fields['spatial_p'])
    dphi = [velocities['scalar'], *fields['spatial_phi']]
    dA = s.zeros(4, 48)
    dA[1:, :] = fields['spatial_A']
    dA[0, 12:] = velocities['gauge_spatial'].reshape(1, 36)
    force = raw_four_forces(e, de, fields['phi'], dphi, fields['A'], dA, psi, dpsi, chi)
    divergence = s.Matrix([sum(spatial_Pi[i, 4*a+i+1] for i in range(3)) for a in range(4)])
    original_Euler = clean(force+divergence)
    equal(original_Euler, matrix(jet['original_full_four_temporal_Euler']))
    equal(-force, matrix(jet['point_Hamiltonian_time_gradient']))
    equal(divergence, matrix(jet['actual_canonical_momentum_divergence']))
    assert all(value != 0 for value in divergence)
    point = model.temporal_constraints(fields, momentum, spatial, spatial_Pi, base_multiplier)
    equal(point['Hamiltonian_time_column_gradient'], -force)
    equal(point['temporal_constraints'], original_Euler)
    spatial_flux = s.Matrix([sum(momentum[4*a+i+1]*e[a, 0] for a in range(4)) for i in range(3)])
    equal(model.flux(e, momentum), spatial_flux)
    equal(spatial_flux, matrix(jet['Hamiltonian_spatial_flux']))
    print('PASS all4 original complete Euler equal the canonical point gradient plus four nonzero momentum divergences; public constraint API and spatial flux matched', flush=True)

    paths = [HERE/name for name in ('source_temporal_coframe_flux.py', 'source_temporal_coframe_flux.json',
        'independent_source_temporal_coframe_flux.py', 'independent_source_coframe_legendre.py',
        'independent_source_common_hamiltonian.py', 'independent_source_coframe_constraints.py',
        'independent_source_coframe_constraints.json')]
    output = {'root': ROOT_ID,
        'verdict': 'CERTIFIED_SOURCE_TEMPORAL_COFRAME_FLUX_OFF_PRIMARY_MULTIPLIER_TRANSPORT_AND_PRIMARY_FIELD_EULER',
        'scope': candidate['scope'], 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_bindings_verified': count,
        'generic_source_coefficients': {'coframe_variables': 16, 'curl_columns': 12,
            'Lorentz_connection_columns': 6, 'primary_time_and_gradient_independence': True},
        'off_primary_Hamiltonian': {'arbitrary_momenta': 16, 'arbitrary_gradients': 12,
            'arbitrary_primary_multipliers': 10,
            'identity': 'H(g,lambda)=H0(lambda+deltaLambda)+Pi.Jg',
            'transport': 'Z deltaLambda=(R Dh-I)Jg',
            'independent_algorithm': 'full source null-frame coordinates, original quadratic reduced density inverse and complete common API',
            'omitted_translation_defect_nonzero': True},
        'actual_primary_field_jet': {'complex_primal_entries': 252, 'complex_independent_momentum_entries': 252,
            'spatial_primary_prolongations': 30,
            'momentum_jet_generated_from_original_Legendre_graph': True,
            'point_primary_zero_does_not_imply_spatial_primary_tangency': True,
            'incompatible_spatial_momentum_jet_negative_control_nonzero': True},
        'original_complete_Euler_readback': {'temporal_rows': 4,
            'algorithm': 'direct original gravity/scalar/gauge/remaining-Dirac density derivatives plus original momentum-jet divergence',
            'Euler': jet['original_full_four_temporal_Euler'],
            'momentum_divergence': jet['actual_canonical_momentum_divergence'],
            'all_four_flux_divergence_entries_nonzero': True,
            'point_formula': '-partial_eTime H0+div_spatial Pi'},
        'boundary_scope': 'Original BF four-flux is retained by the earlier action elimination; the present Hamiltonian spatial flux sum_a Pi_ai e_a0 is the velocity-translation divergence. These are separate exact boundary identities.',
        'actual_constraint_domain': 'primary fields with all required spatial prolongations; primary_prolongations checks that domain separately from temporal_constraints',
        'public_producer_API': candidate['public_API'],
        'temporal_coframe_spatial_differential_operator_remaining': False,
        'temporal_preservation_rates_or_global_Cauchy_claimed': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_temporal_coframe_flux.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS independent original temporal coframe flux certification', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
