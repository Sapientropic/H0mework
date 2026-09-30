#!/usr/bin/env python3
"""Constrained Cauchy response to the actual stationary on-shell currents.

The current exists throughout the Cauchy interval. No Heaviside cutoff is
applied to its Ward identity. Zero initial physical response coexists with
the source-generated affine field and constraint data.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_full_linear_split import decode, P
from source_lorentz_contact import clean, equal, encode
from source_spatial_active_phase_splice import dm, mul, DOMAIN
from source_forced_hamiltonian_reduction import poly, Z, POLY
from source_onshell_phase_forcing import CommonOnshellForcing
from source_common_retarded_phase import read_bound, load_common_fiber
from source_common_phase_time import OriginalCanonicalPhase, absolute_coefficient_bound, norm_bound, compact
from source_gauge_legendre import realify


def zero(A):
    if isinstance(A, DM): assert A.is_zero_matrix
    else: equal(clean(A), s.zeros(*A.shape))


def at(matrix, z=0):
    return dm(matrix.to_Matrix().subs(Z, s.sympify(z)))


def polynomial_coefficients(matrix):
    M = matrix.to_Matrix()
    degree = max((s.degree(v, Z) for v in M.todok().values()), default=0)
    return [dm(M.applyfunc(lambda v: s.expand(v).coeff(Z, n))) for n in range(degree+1)]


def right_divide(matrix, A):
    coefficients = polynomial_coefficients(matrix)
    remainder = coefficients[-1]
    quotient = DM.zeros(matrix.shape, POLY)
    for n in range(len(coefficients)-2, -1, -1):
        quotient = quotient.scalarmul(POLY.gens[0])+poly(remainder)
        remainder = coefficients[n]+remainder*A
    pencil = poly(DM.eye(A.shape, DOMAIN)).scalarmul(POLY.gens[0])-poly(A)
    zero(matrix-poly(remainder)-quotient*pencil)
    return remainder, quotient


class OnshellCauchyResponse:
    def __init__(self):
        self.ingress = read_bound('source_onshell_phase_forcing.json')
        read_bound('independent_source_onshell_phase_forcing.json')
        self.reduction = read_bound('source_forced_hamiltonian_reduction.json')
        read_bound('independent_source_forced_hamiltonian_reduction.json')
        self.maps = CommonOnshellForcing()
        self.spatial = self.maps.spatial
        self.orbit = OriginalCanonicalPhase()
        self.inverse = read_bound('source_active_retarded_inverse.json')
        read_bound('independent_source_active_retarded_inverse.json')

    def build(self, sign):
        source = self.ingress['currents'][0 if sign == 1 else 1]
        old = self.ingress['common_phase_consumers'][0 if sign == 1 else 1]
        fiber = load_common_fiber(sign)
        k, A = fiber['k'], dm(fiber['active_A'])
        record = next(row for row in self.reduction['source_momenta'] if tuple(map(s.sympify, row['momentum'])) == k)
        parsed = lambda key: poly(decode(record[key]))
        j = dm(decode(source['scaled_current289']))
        factor = s.sympify(source['physical_current_factor'])
        equal(clean(j.to_Matrix()*factor), decode(source['current289']))
        spatial = self.spatial
        slice_reader = poly(spatial.native_slice_reader(k))
        ward = poly(spatial.ward.subs(dict(zip(P, [Z, *[s.I*v for v in k]]))))
        W = slice_reader*ward
        assert len(polynomial_coefficients(W)) == 1
        Wi = poly(at(W).inv())
        fixed = lambda value: value-ward*Wi*slice_reader*value
        L = fixed(parsed('full289_field_lift'))
        particular = fixed(parsed('full289_field_particular')*poly(j))
        forcing = parsed('physical_forcing')*poly(j)
        f = at(forcing)
        assert not f.is_zero_matrix
        B, Q = right_divide(L, A)
        affine_polynomial = particular+Q*forcing
        initial_field = at(affine_polynomial)
        assert not initial_field.is_zero_matrix
        field_rate = B*f
        assert not field_rate.is_zero_matrix
        M = polynomial_coefficients(self.maps.canonical_reader)
        assert len(M) <= 2
        M += [DM.zeros(M[0].shape, DOMAIN)]*(2-len(M))
        X = dm(fiber['X'][:, :A.shape[0]])
        zero(M[0]*B+M[1]*B*A-X)
        initial_phase = M[0]*initial_field+M[1]*field_rate
        zero(initial_phase-dm(decode(old['factored_affine_phase_polynomial']).subs(Z, 0)))
        tree = dm(decode(old['factored_physical_response126']))
        zero(-A*tree-f)
        zero(B*tree+initial_field-dm(decode(old['factored_full289_source_response'])))
        # Complete operator identities imply every Taylor coefficient of the
        # original differential Euler system, not just the recorded order.
        original = poly(spatial.raw_action.subs(dict(zip(P, [Z, *[s.I*v for v in k]]))))
        H = polynomial_coefficients(original)
        zero(sum((H[n]*B*(A**n) for n in range(len(H))), DM.zeros((289, A.shape[0]), DOMAIN)))
        initial_euler = H[0]*initial_field
        for n in range(1, len(H)): initial_euler += H[n]*B*(A**(n-1))*f
        zero(initial_euler-j)
        assert not (H[0]*initial_field).is_zero_matrix
        assert not initial_euler.is_zero_matrix

        print('PASS full289 all-order operator identities and source-affine initial field', sign, flush=True)
        order = 20
        derivatives = [DM.zeros((A.shape[0], 1), DOMAIN), f]
        for _ in range(order+len(H)+1): derivatives.append(A*derivatives[-1])
        fields = [initial_field]+[B*value for value in derivatives[1:]]
        phases = [initial_phase]+[X*value for value in derivatives[1:]]
        scalar = polynomial_coefficients(self.maps.scalar_momentum_reader)
        assert len(scalar) == 2
        gauss0 = dm(spatial.model.at(spatial.model.matter_current, k))
        for direction in range(3):
            c = spatial.c
            matrix = gauss0.to_Matrix()
            matrix[:, c.n+67+12*direction:c.n+79+12*direction] = s.I*k[direction]*s.eye(12)-c.gauge.ad(c.A0[direction+1, :]).T
            gauss0 = dm(matrix)
        orbit_transpose = dm(spatial.split.orbit.T)
        source_A0 = dm(self.maps.gauge_A0_selector)*j
        normal = dm(spatial.model.at(spatial.model.broken_map, k))
        scalar_shift = dm(mul(spatial.c.graph.O, spatial.c.graph.constraints.gram.inv(), spatial.c.graph.select.T))*source_A0
        assert not scalar_shift.is_zero_matrix
        scalar_dynamic = scalar[0]*B+scalar[1]*B*A
        scalar_initial = scalar[0]*initial_field+scalar[1]*field_rate
        zero(gauss0*X+orbit_transpose*scalar_dynamic)
        zero(scalar_dynamic-normal*X)
        zero(gauss0*initial_phase+orbit_transpose*scalar_initial-source_A0)
        zero(scalar_initial-normal*initial_phase-scalar_shift)
        for n in range(order+1):
            original_euler = sum((H[r]*fields[n+r] for r in range(len(H))), DM.zeros((289, 1), DOMAIN))
            zero(original_euler-(j if n == 0 else DM.zeros(j.shape, DOMAIN)))
            Pi_phi = scalar[0]*fields[n]+scalar[1]*fields[n+1]
            zero(gauss0*phases[n]+orbit_transpose*Pi_phi-(source_A0 if n == 0 else DM.zeros(source_A0.shape, DOMAIN)))
            zero(Pi_phi-normal*phases[n]-(scalar_shift if n == 0 else DM.zeros(scalar_shift.shape, DOMAIN)))
            zero(M[0]*fields[n]+M[1]*fields[n+1]-phases[n])
        zero(dm(spatial.native_slice_reader(k))*B)
        zero(dm(spatial.native_slice_reader(k))*initial_field)

        inverse_row = next(row for row in self.inverse['source_fibres'] if tuple(map(s.sympify, row['momentum'])) == fiber['k'] or tuple(-s.sympify(v) for v in row['momentum']) == fiber['k'])
        bounds = inverse_row['actual_consumer']['source_norm_bound']
        beta = s.Integer(bounds['integer_upper'])
        assert beta >= s.sympify(bounds['beta']) > 0
        elapsed = 1/(2*beta)
        partial = DM.zeros(f.shape, DOMAIN)
        for n in range(1, order+1): partial += derivatives[n].scalarmul(DOMAIN.convert(elapsed**n/s.factorial(n)))
        partial_field, partial_phase = initial_field+B*partial, initial_phase+X*partial
        force_bound = sum(absolute_coefficient_bound(v) for v in f.to_Matrix())
        # At beta*h=1/2, exp(beta*h)<2. The inhomogeneous series
        # remainder is <= ||f|| exp(beta*h) beta^m h^(m+1)/(m+1)!.
        remainder = s.simplify(2*force_bound*s.Rational(1, 2)**(order+1)/(beta*s.factorial(order+1)))
        field_bound = norm_bound(B.to_Matrix())
        phase_bound = norm_bound(X.to_Matrix())
        field_error = s.simplify(factor*field_bound['integer']*remainder)
        phase_error = s.simplify(factor*phase_bound['integer']*remainder)
        assert field_error > 0 and phase_error > 0
        orbit = self.phase_consumer(partial_field, partial_phase, fields, k, elapsed)
        print('PASS actual inhomogeneous126 Cauchy series, all289 differential Euler coefficients and source12Gauss', sign, flush=True)
        return {'momentum': list(map(str, k)), 'source_factor': str(factor),
            'physical_initial126_is_zero': True,
            'factored_initial_source_field289': encode(initial_field.to_Matrix()),
            'factored_initial_source_phase1214': compact(initial_phase),
            'factored_initial_field_rate289': encode(field_rate.to_Matrix()),
            'factored_nonzero_source_Gauss12': encode(source_A0.to_Matrix()),
            'factored_normal_scalar_momentum_shift70': encode(scalar_shift.to_Matrix()),
            'full12_Gauss_and_normal_scalar_graph_all_order_operator_identities': True,
            'whole_Euler_and_Gauss_checked_derivative_orders': list(range(order+1)),
            'whole_operator_identity': 'sum_r H_r B A^r=0 and H_0 affine + sum_{r>=1} H_r B A^(r-1) f=j; hence every Taylor coefficient satisfies the full original289 differential Euler equation.',
            'initial_total_field_not_zero': True, 'initial_dynamic_field_rate_not_zero': True,
            'drop_initial_affine_changes_original_Euler': True,
            'tree_comparison': '(-A) w_tree=f; B*w_tree+affine equals the signed elastic meromorphic289 response. This is an independent stationary solution, not the chosen zero-physical-initial Cauchy solution.',
            'actual_time_consumer': {'elapsed_source_time': str(elapsed), 'Taylor_order': order,
                'source_generator_norm_upper': str(beta), 'source_force_norm_upper': str(force_bound),
                'field_embedding_norm_upper': field_bound['integer'], 'phase_embedding_norm_upper': phase_bound['integer'],
                'physical_field_remainder_upper': str(field_error), 'physical_phase_remainder_upper': str(phase_error),
                'factored_partial_field289': compact(partial_field), 'factored_partial_phase1214': compact(partial_phase)},
            'original_orbit_phase': orbit}, {'A': A, 'f': f, 'B': B, 'initial_field': initial_field,
                'initial_phase': initial_phase, 'field_derivatives': fields, 'phase_derivatives': phases,
                'partial_field': partial_field, 'partial_phase': partial_phase, 'H': H, 'j': j}

    def phase_consumer(self, field, phase, derivatives, momentum, elapsed):
        spatial, orbit = self.spatial, self.orbit
        unit = s.Rational(12, 13)+s.I*s.Rational(5, 13)
        S, Up, Ud = orbit.phase_at_unit(unit)
        frame = spatial.current_real_frame
        full_phase = s.eye(289)
        full_generator = s.zeros(289)
        for label, phase252, rates in (('primal_H', Up, orbit.Rp), ('dual_H', Ud, orbit.Rd)):
            phase504 = realify(phase252)
            generator504 = realify(s.I*orbit.omega*rates)
            small_phase = mul(frame.T, phase504, frame)
            small_generator = mul(frame.T, generator504, frame)
            zero(mul(phase504, frame)-mul(frame, small_phase))
            zero(mul(generator504, frame)-mul(frame, small_generator))
            ids = [spatial.index[label, (im, spin, color)] for im in range(2) for spin in range(4) for color in range(3)]
            for i, row in enumerate(ids):
                for j, column in enumerate(ids):
                    full_phase[row, column] = small_phase[i, j]
                    full_generator[row, column] = small_generator[i, j]
        zero(full_phase.T*full_phase-s.eye(289))
        zero(full_generator.T+full_generator)
        coframe_rows = [spatial.index['coframe', (a, mu)] for a in range(4) for mu in range(4)]
        de = field.extract(coframe_rows, [0]).to_Matrix().reshape(4, 4)
        chain = orbit.actual_momentum_chain(phase, unit, de)
        moved = dm(full_phase)*field
        current = self.ingress['currents'][0 if momentum[0] < 0 else 1]
        original_j = dm(decode(current['scaled_current289']))
        zero(dm(full_phase)*original_j-original_j)
        # The paid original density conjugacy is exercised on all289 field
        # jets at a nonzero source time, including its temporal phase terms.
        raw = poly(spatial.raw_action.subs(dict(zip(P, [Z, *[s.I*k for k in momentum]]))))
        H = polynomial_coefficients(raw)
        U, K = dm(full_phase), dm(full_generator)
        shifted = []
        for r in range(len(H)):
            shifted.append(sum(((H[n]*(K**(n-r))).scalarmul(DOMAIN.convert(s.binomial(n, r)*(-1)**(n-r)))
                                for n in range(r, len(H))), DM.zeros((289, 289), DOMAIN)))
        actual_jets = []
        for r in range(len(H)):
            jet = DM.zeros((289, 1), DOMAIN)
            for l in range(r+1): jet += ((K**(r-l))*derivatives[l]).scalarmul(DOMAIN.convert(s.binomial(r, l)))
            actual_jets.append(U*jet)
        result = sum((U*shifted[r]*U.transpose()*actual_jets[r] for r in range(len(H))), DM.zeros((289, 1), DOMAIN))
        zero(result-original_j)
        phase_rows = compact(phase)['source_rows']
        return {'representation': 'Stationary Cauchy interval with the original nonzero-time phase restored by the paid source-density conjugacy.',
            'source_unit_phase': str(unit), 'source_initial_time': 'arg('+str(unit)+')/('+str(orbit.omega)+')',
            'proper_clock': 'tau=N*t; N='+str(orbit.N),
            'all289_original_phase_Euler_jets_at_nonzero_time': True,
            'whole_field_phase_source_current_invariant': True,
            'whole_primal_and_independent_dual_phase_subspace_invariance': True,
            'full_delta_chi_E_and_source_chi_deltaE_chain': chain,
            'factored_phase_rotated_field': compact(moved),
            'exact_original_endpoint_readout': orbit.endpoint_readout(dm(S)*phase, elapsed, phase_rows)}


def main():
    started = time.monotonic()
    model = OnshellCauchyResponse()
    print('Built original on-shell ingress, affine source reduction and canonical readers', flush=True)
    consumers = []
    for sign in (1, -1):
        consumer, _ = model.build(sign)
        consumers.append(consumer)
    paths = [HERE/name for name in ('source_onshell_cauchy_response.py', 'source_onshell_phase_forcing.py',
        'source_onshell_phase_forcing.json', 'independent_source_onshell_phase_forcing.json',
        'source_forced_hamiltonian_reduction.py', 'source_forced_hamiltonian_reduction.json',
        'independent_source_forced_hamiltonian_reduction.json', 'source_common_phase_time.py',
        'source_common_phase_time.json', 'independent_source_common_phase_time.json',
        'source_stationary_cauchy_orbit.json', 'independent_source_stationary_cauchy_orbit.json')]
    output = {'root': ROOT_ID, 'source_sha256': model.ingress['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'scope': 'ACTUAL_ONSHELL_CURRENT_CONSTRAINED_COMMON_CAUCHY_RESPONSE_WITH_SOURCE_AFFINE_INITIAL_DATA',
        'consumers': consumers,
        'entire_inhomogeneous_solution': 'w(h)=sum_{n>=1} A^(n-1) f h^n/n!, w(0)=0, dot(w)=A*w+f. Source coefficient norm gives local uniform convergence with all derivatives and uniqueness in this finite actual126 system.',
        'full_source_solution': 'field(h)=B*w(h)+affine_field, canonical(h)=Xactive*w(h)+affine_phase; the two affine values are generated by the original descriptor and right polynomial division.',
        'current_not_switched_off_before_initial_time': True,
        'zero_total_initial_field_or_Theta_truncated_Ward_current_used': False,
        'zero_frequency_Laplace_convergence_claimed': False,
        'quantum_spectrum_or_proton_pole_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_onshell_cauchy_response.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS actual on-shell constrained Cauchy response', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
