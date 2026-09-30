#!/usr/bin/env python3
"""Independent assembly audit of the common original-source Hamiltonian.

The matter oracle constructs the original position-space density, retaining
the independent dual. It does not consume a stationary Fourier generator or
an occupied matter restriction.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import time

import sympy as s

from independent_source_lorentz_contact import (
    ROOT_ID, HERE, BASE, ROOT, PAIRS, J, WEDGE, original_gamma, clean, equal, matrix, exterior,
    real_bilinear, real_linear,
)
from independent_spectral_splice import source
from independent_source_coframe_legendre import actual_geometry


@lru_cache(None)
def original_inventory():
    _, vacuum, degrees, source_hashes = source.parse_source(ROOT)
    internal = [(degree, word) for degree in degrees for word in itertools.combinations(range(7), degree)]
    index = {word: i for i, (_, word) in enumerate(internal)}
    scalar_words = tuple(itertools.combinations(range(7), 4))
    gamma = original_gamma()
    gauge = []
    for _, imaginary, value in source.generators([(0, 1, 2), (3, 4)]):
        internal_matrix = s.diag(*[s.SparseMatrix(source.exterior_action(value, degree)) for degree in degrees])
        gauge.append(clean(s.kronecker_product(s.eye(4), internal_matrix)*(s.I if imaginary else 1)))
    scalar = []
    # General wedge multiplication, with no vacuum-specific Gram condition.
    for word in scalar_words:
        current = s.MutableSparseMatrix.zeros(63, 63)
        for incoming in itertools.combinations(range(7), 2):
            if set(incoming).isdisjoint(word):
                joined = incoming+word
                parity = (-1)**sum(joined[i] > joined[j] for i in range(6) for j in range(i+1, 6))
                current[index[tuple(sorted(joined))], index[incoming]] = parity
        scalar.append(clean(s.kronecker_product(s.diag(0, 0, 1, 1), current)))
    return {'gamma': gamma, 'gauge': gauge, 'scalar': scalar,
            'degrees': degrees, 'internal_basis': internal, 'source_hashes': source_hashes,
            'vacuum': s.Matrix([vacuum.get(word, 0) for word in scalar_words]+[0]*35)}


def raw_matter(e, phi, A):
    inventory = original_inventory()
    inverse, volume = e.inv(), s.Abs(e.det())
    gamma = inventory['gamma']
    D4 = [clean(s.I*volume*sum((inverse[mu, a]*gamma[a] for a in range(4)), s.zeros(4)))
          for mu in range(4)]
    D = [clean(s.kronecker_product(value, s.eye(63))) for value in D4]
    gauge = [clean(sum((A[mu, a]*inventory['gauge'][a] for a in range(12)), s.zeros(252)))
             for mu in range(4)]
    Y = clean(sum(((phi[a]+s.I*phi[35+a])*inventory['scalar'][a] for a in range(35)), s.zeros(252)))
    lower = clean(sum((D[mu]*gauge[mu] for mu in range(4)), s.zeros(252))+volume*Y)
    E_inverse = clean(s.kronecker_product(D4[0].inv(), s.eye(63)))
    equal(D[0]*E_inverse, s.eye(252))
    return {'D': D, 'E': D[0], 'E_inverse': E_inverse, 'gauge': gauge,
            'Y': Y, 'lower': lower, 'volume': volume, 'inverse_e': inverse}


def density_principal_derivative(e, direction):
    inventory = original_inventory()
    inverse, volume = e.inv(), s.Abs(e.det())
    dinverse = -inverse*direction*inverse
    dvolume = volume*s.trace(inverse*direction)
    return [clean(s.kronecker_product(s.I*sum(((dvolume*inverse[mu, a]+volume*dinverse[mu, a])*
        inventory['gamma'][a] for a in range(4)), s.zeros(4)), s.eye(63))) for mu in range(4)]


def original_matter_euler(e, de, phi, A, psi, chi, dpsi, dchi, connection):
    raw = raw_matter(e, phi, A)
    gamma = original_inventory()['gamma']
    spin = [clean(s.kronecker_product(gamma[a]*gamma[b]/2, s.eye(63))) for a, b in PAIRS]
    total_lower = clean(raw['lower']+sum((connection[mu, a]*raw['D'][mu]*spin[a]
        for mu in range(4) for a in range(6)), s.zeros(252)))
    primal = clean(sum((raw['D'][mu]*dpsi[mu] for mu in range(4)), s.zeros(252, 1))+total_lower*psi)
    dual = chi*total_lower
    for mu in range(4):
        direction = s.Matrix(4, 4, de[16*mu:16*(mu+1), 0])
        derivative = density_principal_derivative(e, direction)[mu]
        dual -= dchi[mu]*raw['D'][mu]+chi*derivative
    return {'primal': primal, 'dual': clean(dual), 'raw': raw, 'lower_with_Lorentz': total_lower}


def fixed_p_correction(e, p, primal_euler):
    zero_phi = s.zeros(70, 1)
    zero_A = s.zeros(4, 12)
    raw = raw_matter(e, zero_phi, zero_A)
    chi = s.I*p*raw['E_inverse']
    values = []
    for a in range(16):
        direction = s.zeros(4)
        direction[a] = 1
        dE = density_principal_derivative(e, direction)[0]
        values.append(s.expand(s.re((-chi*dE*raw['E_inverse']*primal_euler)[0])))
    return s.Matrix(values)


@lru_cache(None)
def original_boson_inventory():
    generators = source.generators([(0, 1, 2), (3, 4)])
    fundamental = [s.Matrix(value)*(s.I if imaginary else 1) for _, imaginary, value in generators]
    def native_pair(A, B):
        return s.expand(s.re(-s.trace(A[:3, :3]*B[:3, :3])-
                             s.trace(A[3:5, 3:5]*B[3:5, 3:5])-A[5, 5]*B[5, 5]))
    gram = s.Matrix(12, 12, lambda a, b: native_pair(fundamental[a], fundamental[b]))
    scalar = [real_linear(s.Matrix(source.exterior_action(value, 4))*(s.I if imaginary else 1))
              for _, imaginary, value in generators]
    structure = {}
    for a, b in itertools.product(range(12), repeat=2):
        bracket = fundamental[a]*fundamental[b]-fundamental[b]*fundamental[a]
        coefficients = gram.inv()*s.Matrix([native_pair(value, bracket) for value in fundamental])
        equal(sum((coefficients[c]*fundamental[c] for c in range(12)), s.zeros(7)), bracket)
        for c, value in enumerate(coefficients):
            if value:
                structure[a, b, c] = value
    return {'gram': gram, 'scalar': scalar, 'structure': structure}


def original_scalar_density(e, phi, dphi, A):
    inventory = original_boson_inventory()
    covariant = [dphi[mu]+sum((A[mu, a]*inventory['scalar'][a]*phi for a in range(12)), s.zeros(70, 1))
                 for mu in range(4)]
    metric = s.Abs(e.det())*e.inv()*s.diag(-1, 1, 1, 1)*e.inv().T
    fluctuation = phi-original_inventory()['vacuum']
    return s.expand(sum(metric[mu, nu]*(covariant[mu].T*covariant[nu])[0]/2
                        for mu, nu in itertools.product(range(4), repeat=2))-
                    s.Abs(e.det())*(fluctuation.T*fluctuation)[0])


def original_gauge_density(e, A, dA):
    inventory = original_boson_inventory()
    curvature = s.MutableSparseMatrix.zeros(6, 12)
    for p, (mu, nu) in enumerate(PAIRS):
        curvature[p, :] = dA[mu, 12*nu:12*(nu+1)]-dA[nu, 12*mu:12*(mu+1)]
        for (a, b, c), coefficient in inventory['structure'].items():
            curvature[p, c] += coefficient*A[mu, a]*A[nu, b]
    X = exterior(e)
    hodge = X.inv()*J*X
    kernel = -2*WEDGE*hodge
    return s.expand(sum((curvature*inventory['gram'])[i, a]*(kernel*curvature)[i, a]/2
                        for i in range(6) for a in range(12)))


def certify_generic_temporal_change():
    coefficients = s.symbols('density_temporal0:4', real=True)
    gamma = original_inventory()['gamma']
    E = s.I*sum((a*matrix for a, matrix in zip(coefficients, gamma)), s.zeros(4))
    norm = coefficients[0]**2-sum(value**2 for value in coefficients[1:])
    equal(E*E, norm*s.eye(4))
    for value in coefficients:
        derivative = E.diff(value)
        inverse_derivative_numerator = norm*derivative-norm.diff(value)*E
        # Multiplication clears q^2, so this is a polynomial identity on all
        # four actual principal coefficients, not a coframe sample.
        equal(E*inverse_derivative_numerator+norm*derivative*E, s.zeros(4))
        equal(inverse_derivative_numerator+E*derivative*E, s.zeros(4))
    return {
        'actual_generic_temporal_coefficients': 4,
        'full252_lift': 'Clifford spin4 tensor I63',
        'inverse_derivative': 'delta(E^-1)=-E^-1 delta(E) E^-1',
        'canonical_dual': 'chi=i p E^-1',
        'canonical_one_form': 'Re(chi E delta psi)=Re(i p delta psi)',
        'extra_coframe_momentum_shift': '0: primal psi and the constant real/complex branch transform are unchanged',
        'fixed_p_coframe_chain': 'EL_e_at_p[delta e]=EL_e_at_chi[delta e]-Re(chi delta(E) E^-1 R_chi)',
        'chain_uses_complete_original_primal_Euler': True,
    }


def original_total_density(e, de, phi, dphi, A, dA, psi, dpsi, chi):
    raw = raw_matter(e, phi, A)
    geometry = actual_geometry(e)
    gamma = original_inventory()['gamma']
    current = s.Matrix([s.expand(s.re((chi*raw['D'][mu]*s.kronecker_product(
        gamma[a]*gamma[b]/2, s.eye(63))*psi)[0])) for mu in range(4) for a, b in PAIRS])
    total_source = geometry['G']*de+current
    reduced_gravity = -3*e.det()-(total_source.T*geometry['inverse']*total_source)[0]/2
    remainder = raw['lower']*psi+sum((raw['D'][mu]*dpsi[mu] for mu in range(4)), s.zeros(252, 1))
    matter = s.expand(s.re((chi*remainder)[0]))
    return s.expand(reduced_gravity+matter+original_scalar_density(e, phi, dphi, A)+
                    original_gauge_density(e, A, dA))


def source_fixture(e):
    phi = s.Matrix([s.Rational(j+1, 71) for j in range(70)])
    dphi = [s.Matrix([s.Rational((mu+1)*(j % 7-3), 19) for j in range(70)]) for mu in range(4)]
    A = s.Matrix(4, 12, lambda mu, a: s.Rational((mu+1)*(a-5), 17))
    dA = s.Matrix(4, 48, lambda mu, a: s.Rational((mu+2)*(a % 11-5), 23))
    de = s.Matrix([s.Rational((j % 13)-6, 29) for j in range(64)])
    psi = s.Matrix([s.Rational(j % 17-8, 31)+s.I*s.Rational(j % 7-3, 37) for j in range(252)])
    chi = s.Matrix(1, 252, lambda _, j: s.Rational(j % 11-5, 41)+s.I*s.Rational(j % 13-6, 43))
    dpsi = [s.Matrix([s.Rational((mu+1)*(j % 5-2), 47)+s.I*s.Rational(j % 3-1, 53)
                     for j in range(252)]) for mu in range(4)]
    return e, de, phi, dphi, A, dA, psi, dpsi, chi


def main():
    began = time.monotonic()
    candidate_path = HERE/'source_common_hamiltonian.json'
    candidate = json.loads(candidate_path.read_bytes())
    assert candidate['root'] == ROOT_ID
    bindings = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in candidate[key].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            bindings += 1
    generic_change = certify_generic_temporal_change()
    assert not candidate['full_constraint_consistency_closed']
    inventory = original_inventory()
    spec = importlib.util.spec_from_file_location('common_source_api_under_audit', HERE/'source_common_hamiltonian.py')
    api = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = api
    spec.loader.exec_module(api)
    model = api.SourceCommonHamiltonian()
    for actual, expected in zip(model.rho, inventory['gauge']):
        equal(actual, expected)
    for actual, expected in zip(model.yukawa_basis, inventory['scalar']):
        equal(actual, expected)
    frames = [s.Matrix([[2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
              s.Matrix([[-2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])]
    density_reports = []
    for index, frame in enumerate(frames):
        fields = source_fixture(frame)
        e, de, phi, dphi, A, dA, psi, dpsi, chi = fields
        raw = raw_matter(e, phi, A)
        generated = model.matter_data(e, phi, A)
        for key, original_key in (('E', 'E'), ('inverse_E', 'E_inverse'),
                                 ('lower_without_Lorentz', 'lower'), ('Y', 'Y')):
            equal(generated[key], raw[original_key])
        for actual, expected in zip(generated['principal'], raw['D']):
            equal(actual, expected)
        native_L = original_total_density(*fields)
        assert s.simplify(model.lagrangian(*fields)-native_L) == 0
        momenta = model.momenta(e, de, phi, dphi, A, dA, psi, chi)
        p = -s.I*chi*raw['E']
        equal(momenta['matter'], p)
        equal(model.canonical_dual(generated, p), chi)
        _, multipliers = model.coframe.velocity_coordinates(e, de[:16, :])
        args = (e, momenta['coframe'], de[16:, :], phi, momenta['scalar'], dphi[1:],
                A, momenta['gauge'], dA[1:, :], psi, p)
        result = model.hamiltonian(*args, dpsi[1:], multipliers)
        pairing = (momenta['coframe'].T*de[:16, :])[0]+(momenta['scalar'].T*dphi[0])[0]+\
            sum(a*b for a, b in zip(momenta['gauge'], dA[0, 12:].reshape(3, 12)))+\
            s.re((s.I*p*dpsi[0])[0])
        assert s.simplify(result['value']-pairing+native_L) == 0
        equal(result['coframe_primary'], s.zeros(10, 1))
        equal(momenta['gauge_temporal'], s.zeros(1, 12))
        velocities = model.boson_velocities(*args, multipliers)
        equal(velocities['coframe'], de[:16, :])
        equal(velocities['scalar'], dphi[0])
        equal(velocities['gauge_spatial'], dA[0, 12:].reshape(3, 12))
        if index == 0:
            ve, vf = s.Matrix(s.symbols('audit_ve0:16', real=True)), s.Matrix(s.symbols('audit_vf0:70', real=True))
            va = s.Matrix(3, 12, s.symbols('audit_va0:36', real=True))
            varied_de = ve.col_join(de[16:, :])
            varied_dA = dA.copy()
            varied_dA[0, 12:] = va.reshape(1, 36)
            L = original_total_density(e, varied_de, phi, [vf, *dphi[1:]], A, varied_dA, psi, dpsi, chi)
            measured = model.momenta(e, varied_de, phi, [vf, *dphi[1:]], A, varied_dA, psi, chi)
            for coordinates, key in ((ve, 'coframe'), (vf, 'scalar'), (va, 'gauge')):
                equal(s.Matrix([s.diff(L, value) for value in coordinates]), s.Matrix(list(measured[key])))
            # Realification is evaluated on position-space matrices before any
            # Fourier operation, and the dual is an independent row.
            E4 = raw['E'].extract([0, 63, 126, 189], [0, 63, 126, 189])
            equal(real_bilinear(E4), s.diag(s.eye(4), -s.eye(4))*real_linear(E4))
        current = model.coframe.lorentz.matter_current(e, psi, chi)
        Omega = model.coframe.lorentz.eliminate(e, de, psi, chi)['connection']
        duplicate = s.simplify(-(current.T*Omega)[0])
        assert duplicate != 0
        density_reports.append({'determinant': str(e.det()), 'original_whole_density_identity': True,
            'original122_bosonic_momentum_coefficients': index == 0,
            'full_real_matter_kinetic_matrix': index == 0,
            'all122_bosonic_velocities': True, 'duplicate_Lorentz_term': str(duplicate)})
    print('PASS independently assembled original whole action, full70/full252/native12 coefficients, all122 bosonic momenta and both orientations', flush=True)

    e, de, phi, dphi, A, dA, psi, dpsi, chi = source_fixture(frames[0])
    raw = raw_matter(e, phi, A)
    p = clean(-s.I*chi*raw['E'])
    dp = [s.Matrix(1, 252, lambda _, j: s.Rational((mu+1)*(j % 7-3), 59)+
                  s.I*s.Rational((mu+2)*(j % 5-2), 61)) for mu in range(4)]
    dchi = []
    for mu in range(4):
        direction = s.Matrix(4, 4, de[16*mu:16*(mu+1), 0])
        dE = density_principal_derivative(e, direction)[0]
        dchi.append(clean(s.I*dp[mu]*raw['E_inverse']-chi*dE*raw['E_inverse']))
        equal(dchi[-1]*raw['E']+chi*dE, s.I*dp[mu])
    Omega = model.coframe.lorentz.eliminate(e, de, psi, chi)['connection']
    original = original_matter_euler(e, de, phi, A, psi, chi, dpsi, dchi, Omega.reshape(4, 6))
    generated = model.matter_euler(e, de, phi, A, psi, chi, dpsi, dchi, Omega)
    equal(generated['primal'], original['primal'])
    equal(generated['dual'], original['dual'])
    flow = model.matter_canonical_flow(e, de, phi, A, psi, p, dpsi[1:], dp[1:], Omega)
    equal(original['primal'], raw['E']*(dpsi[0]-flow['primal_velocity']))
    equal(original['dual'], s.I*(flow['canonical_dual_velocity']-dp[0]))
    assert flow['spatial_coefficient_divergence'].todok()
    correction = fixed_p_correction(e, p, original['primal'])
    equal(correction, model.fixed_p_coframe_correction(e, chi, original['primal']))
    equal(correction, matrix(candidate['actual_matter_Euler']['freeze_chi_negative_control']))
    assert correction.todok()
    # The fixed-p versus fixed-chi difference can be differentiated without
    # differentiating the common explicit e dependence, which cancels.
    geometry = actual_geometry(e)
    gamma = inventory['gamma']
    ports = [raw['D'][mu]*s.kronecker_product(gamma[a]*gamma[b]/2, s.eye(63))
             for mu in range(4) for a, b in PAIRS]
    j = s.Matrix([s.re((chi*V*psi)[0]) for V in ports])
    total = geometry['G']*de+j
    complete_remainder = raw['lower']*psi+sum((raw['D'][mu]*dpsi[mu] for mu in range(4)), s.zeros(252, 1))
    for a in range(16):
        direction = s.zeros(4)
        direction[a] = 1
        dE = density_principal_derivative(e, direction)[0]
        delta_chi = -chi*dE*raw['E_inverse']
        delta_j = s.Matrix([s.re((delta_chi*V*psi)[0]) for V in ports])
        direct = s.re((delta_chi*complete_remainder)[0])-(total.T*geometry['inverse']*delta_j)[0]
        assert s.simplify(direct-correction[a]) == 0
    print('PASS independent full252 primal and dual Euler, live coefficient divergence and all16 off-shell fixed-p coframe corrections', flush=True)

    # Uniform current envelope: coefficients of arbitrary Pi, q and lambda.
    native = model.coframe.geometry(e)
    S, Gt, Q, Z = geometry['inverse'], geometry['Gt'], native['velocity_inverse'], native['null_frame']
    Pi, q, lam = s.Matrix(s.symbols('audit_Pi0:16', real=True)), s.Matrix(s.symbols('audit_q0:24', real=True)), s.Matrix(s.symbols('audit_lam0:10', real=True))
    shifted = Pi+Gt.T*S*q
    energy = s.expand((shifted.T*Q*shifted)[0]/2+(q.T*S*q)[0]/2+(lam.T*Z.T*shifted)[0])
    velocity = Q*shifted+Z*lam
    equal(s.Matrix([s.diff(energy, value) for value in q]), S*(Gt*velocity+q))
    assert clean(S*Gt*Z).todok()
    print('PASS all24 Lorentz current envelope coefficients recover the full connection, including arbitrary10 primary multipliers', flush=True)

    # Common Gauss uses the same original scalar and matter coefficients.
    canonical = model.momenta(e, de, phi, dphi, A, dA, psi, chi)
    dPi = [s.Matrix(3, 12, lambda i, a: s.Rational((mu+1)*(i+a-3), 67)) for mu in range(3)]
    gauss = model.gauss(e, phi, canonical['scalar'], A, canonical['gauge'], dPi, psi, p)
    bosons = original_boson_inventory()
    scalar_current = s.Matrix([(canonical['scalar'].T*R*phi)[0] for R in bosons['scalar']])
    matter_current = s.Matrix([s.re((chi*raw['E']*R*psi)[0]) for R in inventory['gauge']])
    equal(gauss['scalar'], scalar_current)
    equal(gauss['matter'], matter_current)
    equal(gauss['total'], gauss['pure']+scalar_current+matter_current)
    equal(gauss['spatial_boundary_flux'], canonical['gauge']*A[0, :].T)
    A0 = s.Matrix(s.symbols('audit_A0:12', real=True))
    varied_A = A.copy()
    varied_A[0, :] = A0.T
    Hamilton = model.hamiltonian(e, canonical['coframe'], de[16:, :], phi, canonical['scalar'], dphi[1:],
        varied_A, canonical['gauge'], dA[1:, :], psi, p, dpsi[1:], s.zeros(10, 1))['value']
    divergence = sum((dPi[mu][mu, :].T for mu in range(3)), s.zeros(12, 1))
    equal(s.Matrix([s.diff(Hamilton, value) for value in A0])-divergence, -gauss['total'])
    bad = [s.Matrix([[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
           s.Matrix([[1, 0, 0, 0], [1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])]
    characteristic_controls = []
    for frame in bad:
        g = frame.T*s.diag(-1, 1, 1, 1)*frame
        assert (g[0, 0] == 0) != (g.inv()[0, 0] == 0)
        try:
            model.chart(frame)
        except AssertionError:
            rejected = True
        else:
            rejected = False
        assert rejected
        characteristic_controls.append({'g_00': str(g[0, 0]), 'g_inverse_00': str(g.inv()[0, 0])})
    print('PASS common native12 Gauss with both source currents and spatial boundary; independent characteristic chart controls', flush=True)

    paths = [HERE/name for name in ('source_common_hamiltonian.py', 'source_common_hamiltonian.json',
        'independent_source_common_hamiltonian.py', 'independent_source_lorentz_contact.py',
        'independent_source_coframe_legendre.py', 'independent_source_coframe_legendre.json',
        'independent_source_scalar_legendre.json')]
    output = {'root': ROOT_ID,
        'verdict': 'CERTIFIED_ORIGINAL_COMMON_LOCAL_HAMILTONIAN_WITH_FULL_SOURCE_MATTER_EULER_AND_FIXED_CANONICAL_VARIABLES',
        'scope': candidate['scope'], 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_bindings_verified': bindings,
        'generic_temporal_change': generic_change, 'whole_density_consumers': density_reports,
        'matter_source_inventory': {'native_gauge_ports': 48, 'real_scalar_Yukawa_ports': 70,
            'complex_primal_dimension': 252, 'independent_dual_dimension': 252,
            'Yukawa_generated_by_original_wedge_and_right_chirality': True,
            'stationary_generator_used_in_original_chart0': False},
        'actual_original_matter_Euler': {'full_primal_entries': 252, 'full_dual_entries': 252,
            'complete_live_principal_jets': True, 'spatial_coefficient_divergence_nonzero': True,
            'fixed_p_coframe_chain_components': 16, 'freeze_chi_rejected': True},
        'current_envelope': {'Lorentz_current_coordinates': 24, 'arbitrary_canonical_momenta': 16,
            'arbitrary_primary_multipliers': 10, 'derivative': 'd_j H_total=-Omega*(Q(Pi-b)+Zlambda)',
            'full_Lorentz_matter_equations_restored_without_repeating_energy': True,
            'omitting_primary_multiplier_rejected': True},
        'common_Gauss': {'original_temporal_coordinates': 12, 'same_full70_scalar_and_full252_independent_dual_currents': True,
            'functional_Hamiltonian_derivative_is_negative_Gauss': True, 'spatial_boundary_retained': True},
        'domain': {'same_original_chart_intersection': 'det e!=0, g^00!=0, independently g_00!=0',
            'mutually_independent_characteristic_controls': characteristic_controls},
        'canonical_pairing': candidate['canonical_pairing'], 'boundary': candidate['boundary'],
        'actual_producer_API': candidate['actual_API'],
        'generic_composition_argument': candidate['generic_composition_argument'],
        'full_constraint_consistency_closed': False,
        'operator_ordering_or_quantum_domain_selected': False,
        'four_block_quantum_spectrum_or_decay_generated': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_common_hamiltonian.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS independent common original Hamiltonian certification', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
