#!/usr/bin/env python3
"""Whole source physical time action and its original Cauchy phase.

All1208 source coordinates evolve by their actual coupled generator. The
entire series is controlled by its source coefficient norm; the recorded
Taylor value carries an explicit remainder and is not called an exact flow.
The independent dual is transported through -i chi E before canonical phase
rotation, retaining the source chi*dE contribution.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_common_retarded_phase import load_common_fiber, read_bound, dm, mul, field_element, DOMAIN
from source_gauge_legendre import realify
from source_lorentz_contact import GAMMA, PAIRS, clean, equal, encode
from source_stabilizer_phase_reduction import block_diagonal, canonical_J
from source_coframe_live_ordering import FREE


def zero(A):
    if isinstance(A, DM):
        assert A.is_zero_matrix
    else:
        equal(clean(A), s.zeros(*A.shape))


def conjugate(A):
    return dm(clean(A.to_Matrix().conjugate()))


@lru_cache(maxsize=None)
def absolute_coefficient_bound(value):
    return s.simplify(abs(s.re(value))+abs(s.im(value)))


def norm_bound(matrix):
    rows = [s.S.Zero]*matrix.rows; cols = [s.S.Zero]*matrix.cols
    for (i, j), value in matrix.todok().items():
        bound = absolute_coefficient_bound(value)
        rows[i] += bound; cols[j] += bound
    row, col = s.simplify(max(rows)), s.simplify(max(cols))
    integer = int(s.ceiling(max(row, col)))
    assert integer > 0 and integer >= row and integer >= col
    return {'row': row, 'column': col, 'operator2': s.sqrt(row*col), 'integer': integer}


def compact(vector, mandatory=()):
    boundaries = (0, 6, 67, 103, 355, 607, 613, 674, 710, 962, 1214)
    rows = {0, vector.shape[0]-1, *mandatory}
    for start, end in zip(boundaries, boundaries[1:]):
        if start < vector.shape[0]:
            rows.add(next((j for j in range(start, min(end, vector.shape[0]))
                           if vector.rep.get(j, {}).get(0, DOMAIN.zero) != DOMAIN.zero), start))
    rows = sorted(j for j in rows if j < vector.shape[0])
    return {'source_rows': rows, 'values': encode(vector.extract(rows, [0]).to_Matrix()),
            'complete_vector_dimension': vector.shape[0],
            'scope': 'Only serialization is sampled; every stated vector equation is checked in its complete dimension.'}


class OriginalCanonicalPhase:
    def __init__(self):
        self.record = read_bound('source_stationary_cauchy_orbit.json')
        read_bound('independent_source_stationary_cauchy_orbit.json')
        cauchy = read_bound('source_first_order_cauchy.json')
        source = cauchy['analytic_Cauchy_source_construction']['nonempty_source_witness']['literal_source_fields']
        self.e0, self.psi0, self.chi0 = (decode(source[k]) for k in ('e', 'psi', 'chi'))
        self.rates = list(map(s.Integer, self.record['primal_integer_rates']))
        self.dual_rates = list(map(s.Integer, self.record['independent_dual_integer_rates']))
        self.Rp, self.Rd = s.diag(*self.rates), s.diag(*self.dual_rates)
        self.omega = s.sympify(self.record['source_frequency'])
        self.N = self.e0[0, 0]
        assert s.simplify(self.N*self.N-s.Rational(54, 125)) == 0
        assert self.omega == 18*s.sqrt(15)/125
        self.gamma = [clean(s.kronecker_product(s.I*G, s.eye(63))) for G in GAMMA]
        for E in self.gamma:
            zero(self.Rd*E+E*self.Rp)
        assert self.Rd != -self.Rp
        self.spin = [clean(s.kronecker_product(GAMMA[a]*GAMMA[b]/2, s.eye(63))) for a, b in PAIRS]
        for E in self.gamma:
            for spin in self.spin:
                zero(self.Rd*E*spin+E*spin*self.Rp)
        for spin in self.spin:
            zero(self.Rp*spin-spin*self.Rp)

        variables = s.Matrix(4, 4, s.symbols('incoming_e0:16', real=True))
        adj = variables.adjugate()
        E4 = sum((adj[0, a]*s.I*GAMMA[a] for a in range(4)), s.zeros(4))
        at_source = dict(zip(variables, self.e0))
        self.E = clean(s.kronecker_product(E4.subs(at_source), s.eye(63)))
        self.dE = [clean(s.kronecker_product(E4.diff(x).subs(at_source), s.eye(63))) for x in variables]
        for variation in self.dE:
            zero(self.Rd*variation+variation*self.Rp)
        self.p0 = clean(-s.I*self.chi0*self.E)
        self.Kpsi = realify(s.I*self.omega*self.Rp)
        # This is the original real canonical momentum map, not a choice of
        # phase for the independent chi field or an adjoint identification.
        flip = s.zeros(252).row_join(-s.eye(252)).col_join((-s.eye(252)).row_join(s.zeros(252)))
        equal(flip*realify(-s.I*self.omega*self.Rp)*flip, self.Kpsi)
        self.K = block_diagonal(s.zeros(103), self.Kpsi, s.zeros(103), self.Kpsi)
        self.Omega = -canonical_J(607)
        zero(self.K.T+self.K)
        zero(self.K.T*self.Omega+self.Omega*self.K)
        self.counterexample_index = next(j for j in range(252) if self.dual_rates[j] != -self.rates[j])
        assert (self.Rp*self.E-self.E*self.Rp).todok()

    def phase_at_unit(self, unit):
        """Exact actual phase at t=arg(unit)/omega; unit is not a new clock."""
        assert s.simplify(s.conjugate(unit)*unit-1) == 0
        Up = s.diag(*[s.expand_complex(unit**r) for r in self.rates])
        Ud = s.diag(*[s.expand_complex(unit**r) for r in self.dual_rates])
        canonical = realify(Up)
        S = block_diagonal(s.eye(103), canonical, s.eye(103), canonical)
        zero(Ud*self.E*Up-self.E)
        for incoming in self.dE:
            zero(Ud*incoming*Up-incoming)
        return S, Up, Ud

    def actual_momentum_chain(self, tangent, unit, delta_e):
        S, Up, Ud = self.phase_at_unit(unit)
        vector = tangent.to_Matrix()
        for coordinate, index in enumerate(FREE):
            assert s.expand(delta_e[index]-vector[coordinate]) == 0
        assert delta_e[:, 0].todok()
        for index in (0, 4, 8, 12):
            zero(self.dE[index])
        dE = clean(sum((delta_e[j]*self.dE[j] for j in range(16)), s.zeros(252)))
        p = (-vector[607+355:1214, :]-s.I*vector[607+103:607+355, :]).T
        chi = clean((s.I*p-self.chi0*dE)*self.E.inv())
        original = clean(-s.I*chi*Ud*self.E-s.I*self.chi0*Ud*dE)
        expected = clean(p*Up.inv())
        zero(original-expected)
        changed = mul(S, vector)
        canonical = (-changed[607+355:1214, :]-s.I*changed[607+103:607+355, :]).T
        zero(canonical-expected)
        omission = clean(s.I*self.chi0*Ud*dE)
        assert dE.todok() and omission.todok()
        # The actual coframe-current variation includes its incoming deltaE
        # term; all three original terms are transported by the same phases.
        psi = vector[103:355, :]+s.I*vector[355:607, :]
        for spin in self.spin:
            source = chi*self.E*spin*self.psi0+self.chi0*self.E*spin*psi+self.chi0*dE*spin*self.psi0
            moved = chi*Ud*self.E*spin*Up*self.psi0+self.chi0*Ud*self.E*spin*Up*psi+self.chi0*Ud*dE*spin*Up*self.psi0
            zero(moved-source)
        return {'all16_incoming_principal_phase_identities_checked': True,
            'actual_full_original_coframe_variation': encode(delta_e),
            'actual_nonzero_temporal_coframe_column': encode(delta_e[:, 0]),
            'actual_coframe_source': 'original289_field_map * original quotient_section * the actual active126 datum; coframe rows are read from the original field manifest, including all four time-column components',
            'original_temporal_column_kinetic_variations_exact_zero': True,
            'all24_full_coframe_current_coefficient_identities_checked': True,
            'all6_actual_full_coframe_current_variations_invariant': True,
            'canonical_chain': 'delta p(t)=-i delta chi_stationary*Ud(t)*E0-i chi0*Ud(t)*delta E=delta p_stationary*Up(t)^-1',
            'independent_dual_is_not_same_index_negative_primal': {'index': self.counterexample_index,
                'primal_rate': int(self.rates[self.counterexample_index]), 'dual_rate': int(self.dual_rates[self.counterexample_index])},
            'actual_unit_phase': str(unit), 'actual_source_time': 'arg('+str(unit)+')/('+str(self.omega)+')',
            'omit_source_chi_deltaE_nonzero_defect': encode(omission),
            'canonical_real_momentum_phase_generated_from_original_chain': True}

    def endpoint_readout(self, vector, elapsed, rows):
        """Exact S(elapsed) applied to an algebraic source vector, recorded sparsely."""
        original = vector.to_Matrix(); values = []
        for row in rows:
            if 103 <= row < 607:
                base, local = 103, row-103
            elif 607+103 <= row < 1214:
                base, local = 607+103, row-(607+103)
            else:
                values.append(original[row]); continue
            j = local % 252
            c = s.cos(self.omega*self.rates[j]*elapsed)
            ss = s.sin(self.omega*self.rates[j]*elapsed)
            q, p = original[base+j], original[base+252+j]
            values.append(c*q-ss*p if local < 252 else ss*q+c*p)
        return {'source_rows': rows, 'values': encode(s.Matrix(values)),
                'phase_frequency': str(self.omega), 'elapsed_source_time': str(elapsed),
                'scope': 'Exact source sine/cosine endpoint rotation of the controlled stationary partial sum.'}


def generate_time_coefficients(data, initial, order):
    A, X, R = map(dm, (data['A_split'], data['X'], data['R']))
    coefficients = [initial]; physical = [X*initial]
    for j in range(order):
        next_coefficient = (A*coefficients[-1]).scalarmul(DOMAIN.convert(s.Rational(1, j+1)))
        zero(next_coefficient.scalarmul(DOMAIN.convert(j+1))-A*coefficients[-1])
        next_physical = X*next_coefficient
        zero(R*next_physical-next_coefficient)
        coefficients.append(next_coefficient); physical.append(next_physical)
    return coefficients, physical


def main():
    started = time.monotonic()
    loader = HERE/'source_common_retarded_phase.py'
    loader_hash = hashlib.sha256(loader.read_bytes()).hexdigest()
    plus, minus = load_common_fiber(1), load_common_fiber(-1)
    orbit = OriginalCanonicalPhase()
    for key in ('X', 'R', 'T', 'A_split', 'H_split', 'Omega_split'):
        zero(dm(minus[key])-conjugate(dm(plus[key])))
    Omega = dm(-plus['J'])
    X, R, opposite_R = map(dm, (plus['X'], plus['R'], minus['R']))
    split_Omega, split_H = map(dm, (plus['Omega_split'], plus['H_split']))
    zero(Omega*X-opposite_R.transpose()*split_Omega)
    source = read_bound('source_spatial_active_phase_splice.json')
    u0 = dm(decode(source['fibers'][0]['actual_phase_datum']))
    u0minus = dm(decode(source['fibers'][1]['actual_phase_datum']))
    zero(u0minus-conjugate(u0))
    w0 = R*u0; zero(X*w0-u0)
    coefficients, physical = generate_time_coefficients(plus, w0, 20)
    opposite_coefficients, opposite_physical = generate_time_coefficients(minus, dm(minus['R'])*u0minus, 20)
    for j in range(21):
        zero(opposite_coefficients[j]-conjugate(coefficients[j]))
        zero(opposite_physical[j]-conjugate(physical[j]))
        if j:
            zero((Omega*physical[j]).scalarmul(DOMAIN.convert(j))-opposite_R.transpose()*split_H*coefficients[j-1])
    zero(dm(plus['T'])*physical[-1]-physical[-1])
    print('PASS full1208 source time coefficients, all original1214 Hamiltonian recursions, physical constraints and opposite-momentum reality', flush=True)

    bound = norm_bound(plus['A_split']); embedding_bound = norm_bound(plus['X'])
    elapsed = s.Rational(1, 2*bound['integer'])
    partial = coefficients[0]
    for j in range(1, 21):
        partial += coefficients[j].scalarmul(DOMAIN.convert(elapsed**j))
    ambient_partial = X*partial
    force_bound = sum(absolute_coefficient_bound(v) for v in w0.to_Matrix())
    split_error = s.cancel(2*force_bound*s.Rational(1, 2)**21/s.factorial(21))
    physical_error = s.cancel(embedding_bound['integer']*split_error)
    assert split_error > 0 and physical_error > 0

    # The old two-hop witness is recomputed in the complete1208 generator,
    # with no restriction to its previously discovered small invariant block.
    tail = read_bound('source_full_linear_retarded.json')
    cascade_record = tail['actual_two_stage_time_consumer']
    dual = int(cascade_record['dual_initial_coordinate'])
    primal = int(cascade_record['primal_reader_coordinate'])
    impulse = dm(s.SparseMatrix(1208, 1, {(126+dual, 0): 1}))
    A = dm(plus['A_split'])
    cascades = [impulse]
    for _ in range(3):
        cascades.append(A*cascades[-1])
    zero(cascades[1].extract(range(728, 1208), [0]))
    zero(cascades[2].extract(range(728, 1208), [0]))
    third = DOMAIN.to_sympy(cascades[3].rep[728+primal][0])
    assert s.simplify(third-s.sympify(cascade_record['two_hop_third_time_derivative'])) == 0
    assert third != 0
    print('PASS source norm-controlled rational-time action and preserved nonzero dual/scalar/primal cascade in the whole carrier', flush=True)

    unit = s.Rational(12, 13)+s.I*s.Rational(5, 13)
    retained = read_bound('retained_hamiltonian_reduction.json')
    original_active = next(row for row in retained['source_momenta'] if tuple(map(s.sympify, row['momentum'])) == plus['k'])
    full_field = dm(decode(source['fibers'][0]['original289_field_map'])) * dm(decode(original_active['quotient_section'])) * w0.extract(range(126), [0])
    field_manifest_path = BASE/'active-gauge/receipt.json'
    manifest = json.loads(field_manifest_path.read_text())['fields']
    coframe_rows = [next(j for j, field in enumerate(manifest)
                        if field['group'] == 'coframe' and tuple(field['coordinate']) == (a, mu))
                    for a in range(4) for mu in range(4)]
    actual_coframe = full_field.extract(coframe_rows, [0]).to_Matrix().reshape(4, 4)
    phase_chain = orbit.actual_momentum_chain(u0, unit, actual_coframe)
    S, _, _ = orbit.phase_at_unit(unit)
    SD, KD = dm(S), dm(orbit.K)
    zero(SD.transpose()*SD-DM.eye((1214, 1214), DOMAIN))
    zero(SD.transpose()*Omega*SD-Omega)
    at_start = SD*u0
    phase_X, phase_R = SD*X, R*SD.transpose()
    zero(phase_R*at_start-w0)
    zero(phase_X*phase_R*at_start-at_start)
    # The two endpoints of the original phase are separate. At nonzero s,
    # the initial jump is T(s), and its ambient action differs from T(0).
    probe = dm(s.SparseMatrix(1214, 1, {(67, 0): 1}))
    moving_jump = phase_X*phase_R*probe
    fixed_jump = dm(plus['T'])*probe
    assert not (moving_jump-fixed_jump).is_zero_matrix
    def L(value):
        return phase_X*A*phase_R*value
    first_original = KD*at_start+SD*physical[1]
    zero(first_original-KD*at_start-L(at_start))
    second_original = KD*KD*at_start+SD*physical[2].scalarmul(DOMAIN.convert(2))+ (KD*SD*physical[1]).scalarmul(DOMAIN.convert(2))
    zero(second_original-KD*KD*at_start-(KD*L(at_start)).scalarmul(DOMAIN.convert(2))-L(L(at_start)))
    phase_partial = SD*ambient_partial
    sample = compact(phase_partial)
    endpoint = orbit.endpoint_readout(phase_partial, elapsed, sample['source_rows'])
    print('PASS original independent-dual/coframe momentum phase chain, two-endpoint T(s) jump and full original-phase time derivatives', flush=True)

    assert hashlib.sha256(loader.read_bytes()).hexdigest() == loader_hash, 'shared loader changed during this run; freeze it before binding this receipt'
    paths = list(plus['input_paths'])+[loader, HERE/'source_common_phase_time.py',
        HERE/'source_stationary_cauchy_orbit.json', HERE/'independent_source_stationary_cauchy_orbit.json',
        HERE/'source_first_order_cauchy.json', HERE/'source_full_linear_retarded.json',
        HERE/'independent_source_full_linear_retarded.json', HERE/'source_spatial_active_phase_splice.json',
        HERE/'independent_source_spatial_active_phase_splice.json', field_manifest_path]
    result = {'root': ROOT_ID, 'source_sha256': plus['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'WHOLE_SOURCE1208_PHYSICAL_TIME_ACTION_AND_ORIGINAL_LITERAL_CAUCHY_PHASE_ON_SIGNED_NONZERO_MOMENTA',
        'momenta': [list(map(str, plus['k'])), list(map(str, minus['k']))],
        'carrier': 'active126 plus dual480/scalar122/primal480, all embedded by the same frozen X into original1214 and read by its same R; no mode cutoff or new momentum grid.',
        'exact_time_action': 'u_stationary(t;s)=X sum_{j>=0} (t-s)^j A_split^j/j! R u_stationary(s), for T u(s)=u(s). The source norm bound proves convergence for every finite real elapsed time and uniqueness of the complete linear system.',
        'actual_full_time_recursions': {'dimension': 1208, 'original_ambient_dimension': 1214,
            'verified_orders': 20, 'all_original_Hamiltonian_vectors': 'j Omega1214 u_j=R(-k)^T H_split w_(j-1)',
            'all21_complete_opposite_momentum_coefficients_checked': True,
            'original_initial_datum': compact(u0), 'full_split_initial_datum': compact(w0)},
        'source_bounds': {'generator': {key: str(v) for key, v in bound.items()},
            'embedding': {key: str(v) for key, v in embedding_bound.items()},
            'norm': 'Euclidean coefficient norm used for controlled evaluation, not an added physical-state normalization.',
            'entire_series_bound': '||exp(t A_split)||2<=exp(beta*abs(t)), beta=sqrt(row_bound*column_bound).'},
        'actual_controlled_time_value': {'elapsed_time': str(elapsed), 'order': 20,
            'stationary_value': compact(ambient_partial),
            'split_remainder_upper_bound': str(split_error), 'original_phase_remainder_upper_bound': str(physical_error),
            'error_proof': 'beta*elapsed<=1/2, exp(1/2)<2, ||w0||2<=the actual component1 bound. The entire-series remainder is bounded by2*||w0||bound*(1/2)^21/21!; multiply by the displayed source X norm bound. Exact orthogonal phase rotations preserve this bound.',
            'finite_partial_sum_declared_exact_solution': False},
        'complete_tail_cascade': {'dual_initial_source_coordinate': dual, 'primal_reader_source_coordinate': primal,
            'whole1208_first_and_second_primal_derivatives_zero': True,
            'whole1208_third_primal_derivative': str(third),
            'tail_couplings_removed_or_replaced_by_uncoupled_evolution': False},
        'original_phase_chain': phase_chain,
        'canonical_phase': {'frequency': str(orbit.omega), 'primal_source_integer_rates': list(map(int, orbit.rates)),
            'generator': 'Kcan=diag(0_103,realify(i*omega*Rp),0_103,realify(i*omega*Rp)), derived after the full independent-dual kinetic chain.',
            'source_generator_real_skew_and_symplectic_checked': True,
            'proper_clock': 'tau=N*t, N='+str(orbit.N)},
        'two_endpoint_original_flow': 'G_original(t,s)=S(t) X Theta(t-s) exp((t-s)A_split) R S(s)^-1. The initial jump is T(s)=S(s)T S(s)^-1 and the original generator is Kcan+S(t)X A_split R S(t)^-1 on the transported source tangent.',
        'actual_nonzero_initial_phase': {'unit_phase': str(unit), 'source_time': 'arg('+str(unit)+')/('+str(orbit.omega)+')',
            'initial_state': compact(at_start), 'instantaneous_Ts_jump_on_state_checked': True,
            'moving_vs_frozen_jump_nonzero_control': compact(moving_jump-fixed_jump),
            'original_first_derivative': compact(first_original), 'original_second_derivative': compact(second_original),
            'future_value_with_exact_second_endpoint_rotation': endpoint},
        'original_density_and_source_orbit_consumer': 'The signed146 density/158 vertex identities and literal1500 Cauchy orbit supply the same original phase at both endpoints. All16 incoming deltaE coefficients and the complete coframe-current variations are additionally consumed here.',
        'nonlinear_or_interacting_quantum_spectral_measure_or_proton_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_common_phase_time.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS whole source physical phase time', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
