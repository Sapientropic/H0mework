#!/usr/bin/env python3
"""Actual source 2-to-2 exchange with nonzero energy transfer and time forcing.

All energies come from the full252 action. A monochromatic source is kept
throughout its Cauchy interval; its nonzero time derivatives feed the entire
affine descriptor polynomial, rather than a frozen zero-frequency source.
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
from source_spatial_active_phase_splice import dm, mul, DOMAIN, field_element
from source_onshell_phase_forcing import ActualOnshellPhaseSources, CommonOnshellForcing
from source_forced_hamiltonian_reduction import poly, Z
from source_common_retarded_phase import read_bound, SourceCommonRetardedPhase
from source_common_phase_time import absolute_coefficient_bound, norm_bound, compact
from source_onshell_cauchy_response import at, polynomial_coefficients, right_divide, zero


class NonzeroFrequencyOnshellSources(ActualOnshellPhaseSources):
    def leg_at_momentum(self, degree, momentum):
        momentum = s.Matrix(momentum)
        self.radius = s.simplify(s.sqrt((momentum.T*momentum)[0]))
        assert self.radius > 0
        result = self.leg(degree, clean(momentum/self.radius))
        equal(result['momentum'], momentum)
        return result

    def sources(self):
        # The source momentum belongs to the already certified common fiber.
        fixed = read_bound('source_spatial_active_phase_splice.json')['fibers'][0]
        k = s.Matrix(list(map(s.sympify, fixed['momentum'])))
        a = -k[0]
        equal(k, s.Matrix([-a, 0, 2*a]))
        high, low = [-a, 0, 4*a/3], [0, 0, -2*a/3]
        legs = [self.leg_at_momentum(4, high), self.leg_at_momentum(4, low),
                self.leg_at_momentum(2, low), self.leg_at_momentum(2, high)]
        zero(legs[0]['momentum']+legs[2]['momentum']-legs[1]['momentum']-legs[3]['momentum'])
        assert s.simplify(legs[0]['energy']+legs[2]['energy']-legs[1]['energy']-legs[3]['energy']) == 0
        currents = []
        for incoming, outgoing in ((legs[0], legs[1]), (legs[2], legs[3])):
            j = self.current(outgoing, incoming)
            transfer = clean(incoming['derivative']-outgoing['derivative'])
            z = transfer[0]
            assert z != 0 and s.simplify(s.re(z)) == 0
            at_transfer = dict(zip(P, transfer))
            for matrix in (self.null_map, self.scalar_contact_map, self.dual_map):
                zero(clean(matrix.subs(at_transfer)*j))
            scalar_sources = []
            for vertex in self.vertices['primitive_vertices']:
                if vertex['group'] != 'scalar': continue
                V = decode(vertex['operator'])
                left = V.subs(dict(zip(P, incoming['derivative'])))
                right = V.subs(dict(zip(P, outgoing['derivative'])))
                scalar_sources.append(s.simplify((outgoing['action_vector'].H*(self.S*left+right.H*self.S)*incoming['action_vector'])[0]))
            assert len(scalar_sources) == 70 and all(v == 0 for v in scalar_sources)
            # The unit Pauli spinor is (3,-1)/sqrt(10), while the other
            # direction is a coordinate vector. Its factor is restored in
            # every physical current, field and bilinear below.
            factor = 1/s.sqrt(10)
            factored = clean(j/factor).applyfunc(s.simplify)
            dm(factored)
            equal(clean(factor*factored), j)
            source289 = mul(self.injection, factored)
            zero(self.current(legs[3], legs[0])); zero(self.current(legs[1], legs[2]))
            currents.append({'transfer': transfer, 'current97': j,
                'current289': clean(self.injection*j), 'factored_current97': factored,
                'factored_current289': source289, 'physical_current_factor': factor,
                'scalar70_sources': s.Matrix(scalar_sources)})
        zero(currents[0]['transfer']+currents[1]['transfer'])
        equal(currents[0]['transfer'][1:, :]/s.I, k)
        return legs, currents

    def four_block_response(self, source):
        point = dict(zip(P, source['transfer']))
        j = source['factored_current97']
        A = decode(self.exchange['canonical_operator']).subs(point)
        J = decode(self.exchange['canonical_source_map']).subs(point)
        force = mul(J, j)
        num, den = dm(A).solve_den(dm(force), method='rref')
        response = clean((num.to_Matrix()/DOMAIN.to_sympy(den)).applyfunc(s.simplify))
        equal(mul(A, response), force)
        local = mul(decode(self.exchange['contact_field_response']).subs(point), j)
        propagated = mul(decode(self.exchange['canonical_field_lift']).subs(point), response)
        return {'field': clean(local+propagated), 'local': local, 'propagated': propagated}


class NonzeroFrequencyCommonResponse:
    def __init__(self):
        self.source = NonzeroFrequencyOnshellSources()
        self.maps = CommonOnshellForcing()
        self.reduction = read_bound('source_forced_hamiltonian_reduction.json')
        read_bound('independent_source_forced_hamiltonian_reduction.json')

    def response(self, sign, source, reference):
        common = SourceCommonRetardedPhase(sign)
        fiber, spatial = common.fiber, self.maps.spatial
        k, A = fiber['k'], common.active.A
        z = s.simplify(source['transfer'][0]); z_field = field_element(z)
        equal(s.Matrix(k), source['transfer'][1:, :]/s.I)
        row = next(record for record in self.reduction['source_momenta'] if tuple(map(s.sympify, record['momentum'])) == k)
        parsed = lambda name: poly(decode(row[name]))
        j = dm(source['factored_current289'])
        zero(at(parsed('original_Ward_map'), z)*j)
        wrong_ward = at(parsed('original_Ward_map'), 0)*j
        assert not wrong_ward.is_zero_matrix
        forcing_polynomial = parsed('physical_forcing')*poly(j)
        f = at(forcing_polynomial, z)
        wrong_force = at(forcing_polynomial, 0)
        assert not (f-wrong_force).is_zero_matrix
        assert not f.is_zero_matrix
        X = common.X.extract(range(1214), range(A.shape[0]))
        physical_force = X*f
        zero(common.T*physical_force-physical_force)
        response = common.resolvent(physical_force, z)
        xi = common.R*response
        zero(xi.extract(range(A.shape[0], xi.shape[0]), [0]))
        xi = xi.extract(range(A.shape[0]), [0])
        zero(xi.scalarmul(z_field)-A*xi-f)
        slice_reader = poly(spatial.native_slice_reader(k))
        ward = poly(spatial.ward.subs(dict(zip(P, [Z, *[s.I*v for v in k]]))))
        Wi = poly(at(slice_reader*ward).inv())
        fixed = lambda value: value-ward*Wi*slice_reader*value
        L = fixed(parsed('full289_field_lift'))
        particular = fixed(parsed('full289_field_particular')*poly(j))
        B, Q = right_divide(L, A)
        affine = at(particular+Q*forcing_polynomial, z)
        full = B*xi+affine
        zero(full-at(L, z)*xi-at(particular, z))
        raw = poly(spatial.raw_action.subs(dict(zip(P, [Z, *[s.I*v for v in k]]))))
        zero(at(raw, z)*full-j)
        zero(full-at(fixed(poly(reference['field'])), z))
        M = polynomial_coefficients(self.maps.canonical_reader)
        M += [DM.zeros(M[0].shape, DOMAIN)]*(2-len(M))
        zero(M[0]*B+M[1]*B*A-X)
        affine_phase = (M[0]+M[1].scalarmul(z_field))*affine+M[1]*B*f
        phase = response+affine_phase
        zero(at(self.maps.canonical_reader, z)*full-phase)
        time = self.time_consumer(k, A, B, X, f, affine, affine_phase, raw, j, z, source['physical_current_factor'])
        factor = source['physical_current_factor']
        equal(clean(at(raw, z).to_Matrix()*(full.to_Matrix()*factor)), source['current289'])
        print('PASS nonzero-frequency source Ward/affine forcing, full289 exchange and common Cauchy recurrence', sign, flush=True)
        return {'momentum': list(map(str, k)), 'actual_time_frequency': str(z), 'physical_source_factor': str(factor),
            'factored_source_forcing126': encode(f.to_Matrix()),
            'factored_source_response126': encode(xi.to_Matrix()),
            'factored_affine_phase1214': compact(affine_phase),
            'factored_full289_response': encode(full.to_Matrix()),
            'factored_common_phase1214_response': compact(phase),
            'actual_frequency_Ward_zero': True, 'wrong_zero_frequency_Ward_nonzero': True,
            'wrong_zero_frequency_forcing_nonzero_defect': compact(f-wrong_force),
            'all289_original_forced_Euler_checked': True,
            'same_Ward_slice_matches_independent_four_block_inverse': True,
            'time_consumer': time}, full.to_Matrix()*factor

    def time_consumer(self, k, A, B, X, f, affine, affine_phase, raw, j, z, factor):
        spatial = self.maps.spatial
        zf = field_element(z)
        H = polynomial_coefficients(raw)
        zero(sum((H[r]*B*(A**r) for r in range(len(H))), DM.zeros(B.shape, DOMAIN)))
        order = 20
        rates = [DM.zeros(f.shape, DOMAIN)]
        for n in range(order+len(H)+1): rates.append(A*rates[-1]+f.scalarmul(zf**n))
        fields = [B*w+affine.scalarmul(zf**n) for n, w in enumerate(rates)]
        phases = [X*w+affine_phase.scalarmul(zf**n) for n, w in enumerate(rates)]
        assert not fields[0].is_zero_matrix and not fields[1].is_zero_matrix
        initial = sum((H[r]*fields[r] for r in range(len(H))), DM.zeros(j.shape, DOMAIN))
        zero(initial-j)
        # Together with sum H_r B A^r=0, the generated source-jet recurrence
        # makes this initial identity the full all-order Euler identity.
        scalar = polynomial_coefficients(self.maps.scalar_momentum_reader)
        scalar += [DM.zeros(scalar[0].shape, DOMAIN)]*(2-len(scalar))
        base = spatial.model.at(spatial.model.matter_current, k)
        c = spatial.c
        for i in range(3): base[:, c.n+67+12*i:c.n+79+12*i] = s.I*k[i]*s.eye(12)-c.gauge.ad(c.A0[i+1, :]).T
        base = dm(base); orbitT = dm(spatial.split.orbit.T)
        normal = dm(spatial.model.at(spatial.model.broken_map, k))
        source_A0 = dm(self.maps.gauge_A0_selector)*j
        expected_shift = dm(mul(c.graph.O, c.graph.constraints.gram.inv(), c.graph.select.T))*source_A0
        scalar_dynamic = scalar[0]*B+scalar[1]*B*A
        scalar_affine = (scalar[0]+scalar[1].scalarmul(zf))*affine+scalar[1]*B*f
        zero(base*X+orbitT*scalar_dynamic); zero(scalar_dynamic-normal*X)
        zero(base*affine_phase+orbitT*scalar_affine-source_A0)
        zero(scalar_affine-normal*affine_phase-expected_shift)
        for n in range(order+1):
            euler = sum((H[r]*fields[n+r] for r in range(len(H))), DM.zeros(j.shape, DOMAIN))
            zero(euler-j.scalarmul(zf**n))
            Pi = scalar[0]*fields[n]+scalar[1]*fields[n+1]
            zero(base*phases[n]+orbitT*Pi-source_A0.scalarmul(zf**n))
            zero(Pi-normal*phases[n]-expected_shift.scalarmul(zf**n))
        source_inverse = read_bound('source_active_retarded_inverse.json')
        inverse_row = next(row for row in source_inverse['source_fibres'] if any(s.sympify(v) != 0 for v in row['momentum']))
        beta_A = s.Integer(inverse_row['actual_consumer']['source_norm_bound']['integer_upper'])
        beta = beta_A+s.ceiling(abs(z))
        assert beta >= beta_A+abs(z) and s.re(z) == 0
        h = 1/(2*beta)
        partial_field, partial_phase = DM.zeros(j.shape, DOMAIN), DM.zeros((1214, 1), DOMAIN)
        for n in range(order+1):
            partial_field += fields[n].scalarmul(DOMAIN.convert(h**n/s.factorial(n)))
            partial_phase += phases[n].scalarmul(DOMAIN.convert(h**n/s.factorial(n)))
        bound = lambda matrix: sum(absolute_coefficient_bound(v) for v in matrix.to_Matrix())
        force_bound, affine_bound, phase_affine_bound = map(bound, (f, affine, affine_phase))
        denominator = s.Integer(2)**(order+1)*s.factorial(order+1)
        response_error = 2*force_bound/(beta*denominator)
        field_bound, phase_bound = norm_bound(B.to_Matrix()), norm_bound(X.to_Matrix())
        field_error = s.simplify(factor*(field_bound['integer']*response_error+2*affine_bound/denominator))
        phase_error = s.simplify(factor*(phase_bound['integer']*response_error+2*phase_affine_bound/denominator))
        return {'source_current': 'j(h)=exp(z*h) j0; no Heaviside cutoff, z is the actual on-shell energy transfer.',
            'actual_Cauchy_solution': 'w(0)=0; w(n+1)=A*w(n)+z^n*f for derivatives at0; dot(w)=A*w+exp(z*h)*f.',
            'all_order_full289_Euler_and_Gauss_operator_identities': True,
            'complete_vector_derivative_orders_checked': list(range(order+1)),
            'nonzero_total_initial_field': encode(affine.to_Matrix()),
            'nonzero_initial_field_rate': compact(fields[1]),
            'source_Gauss_amplitude12': encode(source_A0.to_Matrix()),
            'normal_scalar_momentum_amplitude70': encode(expected_shift.to_Matrix()),
            'elapsed_source_time': str(h), 'proper_clock': 'tau=N*t, original source N retained',
            'generator_norm_upper': str(beta_A), 'generator_plus_frequency_upper': str(beta),
            'Taylor_order': order, 'force_norm_upper': str(force_bound),
            'field_affine_norm_upper': str(affine_bound), 'phase_affine_norm_upper': str(phase_affine_bound),
            'field_embedding_norm_upper': field_bound['integer'], 'phase_embedding_norm_upper': phase_bound['integer'],
            'physical_field_remainder_upper': str(field_error), 'physical_phase_remainder_upper': str(phase_error),
            'factored_field_Taylor_readback': compact(partial_field), 'factored_phase_Taylor_readback': compact(partial_phase),
            'time_representation': 'Stationary representation of the same original source orbit; all source time derivatives are retained.'}


def main():
    started = time.monotonic()
    model = NonzeroFrequencyCommonResponse()
    legs, currents = model.source.sources()
    print('PASS original full252 energies, both Dirac shells and nonzero transfer with total two-body energy/momentum conserved', flush=True)
    references = [model.source.four_block_response(row) for row in currents]
    consumers, fields = [], []
    for sign, current, reference in zip((1, -1), currents, references):
        consumer, field = model.response(sign, current, reference)
        consumers.append(consumer); fields.append(field)
    contact = s.simplify((currents[1]['current289'].T*references[0]['local'])[0]*currents[0]['physical_current_factor'])
    dynamic = s.simplify((currents[1]['current289'].T*references[0]['propagated'])[0]*currents[0]['physical_current_factor'])
    direct = s.simplify(-(currents[1]['current289'].T*fields[0])[0])
    assert s.simplify(direct+contact+dynamic) == 0
    paths = [HERE/name for name in ('source_nonzero_frequency_onshell_response.py', 'source_onshell_phase_forcing.py',
        'source_onshell_cauchy_response.py', 'source_forced_hamiltonian_reduction.json',
        'independent_source_forced_hamiltonian_reduction.json', 'source_common_retarded_phase.py',
        'source_common_retarded_phase.json', 'independent_source_common_retarded_phase.json', 'source_active_retarded_inverse.json')]
    paths += [BASE/name for name in ('matter-vertices/receipt.json', 'matter-vertices/exchange.json',
        'matter-modes/source.json', 'full-phase/receipt.json', 'kinetic-residue/receipt.json')]
    serialize = lambda row: {key: encode(value) if isinstance(value, s.MatrixBase) else str(value) for key, value in row.items()}
    output = {'root': ROOT_ID, 'source_sha256': model.source.vertices['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'scope': 'SOURCE_ACTION_NORMALIZED_TRUE_NONZERO_ENERGY_TRANSFER_AND_COMMON_AFFINE_TIME_RESPONSE',
        'legs': list(map(serialize, legs)), 'currents': list(map(serialize, currents)), 'consumers': consumers,
        'total_two_body_energy_and_spatial_momentum_conserved': True,
        'process_interpretation': 'Elastic2-to-2 species-preserving exchange with nonzero individual energy transfer; no inelastic channel or decay is inferred.',
        'original_Ward9_scalar9_dual24_and_scalar70_checked': True,
        'dual24_and_peripheral_scalar61_sources_zero_from_actual_vertices': True,
        'action_leg_factor': str(model.source.action_factor), 'spinor_geometric_current_factor': '1/sqrt(10)',
        'canonical_dynamic_bilinear': str(dynamic), 'Contact_bilinear': str(contact), 'direct_tree_kernel': str(direct),
        'Contact_consumed_once': True,
        'frequency_evaluation': 'Meromorphic response at the actual imaginary frequency; not a claimed convergent boundary Laplace integral.',
        'interacting_quantum_spectrum_or_proton_lifetime_inferred': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_nonzero_frequency_onshell_response.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS nonzero-frequency source response', [str(row['transfer'][0]) for row in currents], 'energies', [str(row['energy']) for row in legs], flush=True)
    print('PASS nonzero-frequency source Cauchy consumer', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
