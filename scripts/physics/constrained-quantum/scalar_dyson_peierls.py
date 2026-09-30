#!/usr/bin/env python3
"""The original N2 CCR constant term and the source scalar retarded kernel.

The two-time field commutator comes from the same canonical phase used by
scalar_dyson_time.  The ordered product keeps its Weyl quadratic term; its
constant term is i/2 times the source Pauli--Jordan kernel.  No state, vacuum,
Hadamard function, or self-energy is introduced.  Nonzero momentum keeps the
whole (momentum, internal index) particle labels in the CAR coefficient.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from full_matter_ports import clean, equal, encode

KAPPA = s.symbols('kap1:4', real=True)
LAMBDA = s.Symbol('lambda')


def green_expression(value):
    # The original spectral parameter is named lambda, a Python keyword.
    return s.sympify(value.replace('lambda', 'laplace_z'), locals={'laplace_z': LAMBDA})


def green_matrix(record):
    return s.SparseMatrix(*record['shape'], {(int(i), int(j)): green_expression(value)
        for i, j, value in record['entries']})


def remap(matrix):
    return clean(matrix.subs({x: KAPPA[int(str(x)[1:])-1]
        for x in matrix.free_symbols if str(x) in ('k1', 'k2', 'k3')}))


def line_contract(kernel, first, second):
    """Ordered particle-line coefficients, with no internal-only Pauli deletion."""
    entries = defaultdict(lambda: s.Integer(0))
    for (a, b), coefficient in kernel.todok().items():
        for (i, j), left in first[a].todok().items():
            for (k, ell), right in second[b].todok().items():
                entries[(i, k, j, ell)] += coefficient * left * right
    return {indices: s.expand(value) for indices, value in entries.items() if s.expand(value) != 0}


def CAR_zero_mode_read(line_kernel):
    """Same-momentum test-space CAR readout for the actual real zero mode.

    Only this readout identifies labels using the internal mode alone.  The
    nonzero-transfer line kernel above retains equal internal indices on
    distinct physical momenta.
    """
    entries = defaultdict(lambda: s.Integer(0))
    for (i, k, j, ell), value in line_kernel.items():
        if i == k or j == ell:
            continue
        sign = (1 if i < k else -1) * (1 if j < ell else -1)
        output = tuple(sorted((i, k)))
        incoming = tuple(sorted((j, ell)))
        entries[(*output, *incoming)] += sign * value
    return {indices: s.expand(value) for indices, value in entries.items() if s.expand(value) != 0}


def encode_kernel(entries):
    return [[*map(int, indices), str(value)] for indices, value in sorted(entries.items())]


def annihilate_basis(mode, state):
    if mode not in state:
        return None, 0
    return tuple(i for i in state if i != mode), (-1) ** sum(i < mode for i in state)


def create_basis(mode, state):
    if mode in state:
        return None, 0
    return tuple(sorted((*state, mode))), (-1) ** sum(i < mode for i in state)


def word_read(i, k, ell, j, incoming, outgoing):
    value, state = 1, incoming
    for operation, mode in ((annihilate_basis, j), (annihilate_basis, ell),
                            (create_basis, k), (create_basis, i)):
        state, factor = operation(mode, state)
        value *= factor
        if value == 0:
            return 0
    return value if state == outgoing else 0


def main():
    started = time.monotonic()
    source = json.loads((HERE / 'scalar_canonical_phase.json').read_text())
    pair = json.loads((HERE / 'scalar_joint_hamiltonian.json').read_text())
    matter = json.loads((HERE / 'full-matter-ports.json').read_text())
    time_record = json.loads((HERE / 'scalar_dyson_time.json').read_text())
    time_audit = json.loads((HERE / 'independent_scalar_dyson_time.json').read_text())
    for record in (source, pair, matter, time_record, time_audit):
        assert record['root'] == ROOT_ID
        for key in ('source_sha256', 'input_sha256'):
            for name, digest in record.get(key, {}).items():
                assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
    assert source['source_sha256'] == pair['source_sha256'] == matter['source_sha256']
    N = s.sympify(source['source_lapse'])
    assert s.simplify(N * N - s.Rational(54, 125)) == 0
    A = remap(decode(pair['real_phase_generator']))
    J = decode(pair['canonical_J'])
    Ac = remap(decode(source['canonical_generator']))
    Jc = decode(source['canonical_Poisson_matrix'])
    Oc = decode(source['canonical_field_output'])
    P = decode(source['projector61'])
    R = decode(pair['scalar_R'])
    scalar_L = remap(decode(source['scalar_L']))
    zero_A = decode(pair['zero_mode']['generator'])
    zero_L = clean(scalar_L.subs(dict.fromkeys(KAPPA, 0)))
    minus = dict(zip(KAPPA, [-k for k in KAPPA]))
    Ac_minus = clean(Ac.subs(minus, simultaneous=True))
    q = s.sqrt(2) / 2
    plus = s.SparseMatrix.zeros(122, 244)
    for j in range(61):
        plus[j, j], plus[j, j + 61] = q, s.I * q
        plus[j + 61, j + 122], plus[j + 61, j + 183] = q, s.I * q
    negative = plus.conjugate()
    Fplus, Fminus = clean(Oc * plus), clean(Oc * negative)
    equal(plus * A, Ac * plus)
    equal(negative * A, Ac_minus * negative)
    equal(A * J + J * A.T, s.zeros(244))
    equal(zero_A * Jc + Jc * zero_A.T, s.zeros(122))
    equal(plus * J * negative.T, Jc)
    equal(negative * J * plus.T, Jc)
    equal(plus * J * plus.T, s.zeros(122))
    equal(negative * J * negative.T, s.zeros(122))
    equal(Fplus[:, :122], decode(pair['positive_transfer_field_frame']))
    equal(Fminus[:, :122], decode(pair['negative_transfer_field_frame']))
    equal(Fplus[:, 122:], s.zeros(70, 122))
    equal(Fminus[:, 122:], s.zeros(70, 122))

    # These intertwinings prove the entire two-time exponential identity, not
    # merely the following displayed initial jets:
    # F+ exp(t A) J F-^T = Oc exp(t Ac(k)) Jc Oc^T.
    equal(plus * J * Fminus.T, Jc * Oc.T)
    equal(negative * J * Fplus.T, Jc * Oc.T)
    jets, zero_jets = [], []
    for n in range(4):
        positive_jet = clean(Fplus * A**n * J * Fminus.T)
        negative_jet = clean(Fminus * A**n * J * Fplus.T)
        equal(positive_jet, Oc * Ac**n * Jc * Oc.T)
        equal(negative_jet, positive_jet.subs(minus, simultaneous=True))
        equal(Fplus * A**n * J * Fplus.T, s.zeros(70))
        equal(Fminus * A**n * J * Fminus.T, s.zeros(70))
        equal(negative_jet, (-1) ** (n + 1) * positive_jet.T)
        zero_jet = clean(Oc * zero_A**n * Jc * Oc.T)
        equal(zero_jet, positive_jet.subs(dict.fromkeys(KAPPA, 0)))
        jets.append(positive_jet)
        zero_jets.append(zero_jet)
    equal(jets[0], s.zeros(70))
    equal(jets[1], N * P)
    equal(jets[2], s.zeros(70))
    equal(jets[3], -N**3 * scalar_L * P)
    equal(Fplus * A**2, -N**2 * scalar_L * Fplus)
    equal(Oc * zero_A**2, -N**2 * zero_L * Oc)
    equal(jets[0] / N, s.zeros(70))
    equal(jets[1] / N, P)
    print('PASS whole70 two-time CCR readers, both physical Fourier orientations and original real zero mode', flush=True)

    # Clear the original source Green denominator.  The same Delta, with
    # Delta(0)=0 and Delta'(0)=N P61, generates exactly P61*delta(t).
    numerator = remap(green_matrix(source['original_Green_numerator']))
    raw_denominator = green_expression(source['original_Green_denominator'])
    denominator = s.expand(raw_denominator.subs({x: KAPPA[int(str(x)[1:])-1]
        for x in raw_denominator.free_symbols if str(x) in ('k1', 'k2', 'k3')}))
    operator = clean(LAMBDA**2 * s.eye(70) / N + N * scalar_L)
    equal(operator * numerator, denominator * P)
    equal(numerator * operator, denominator * P)
    equal(Oc * (Ac / N)**2, -scalar_L * Oc)
    equal(Oc * (Ac / N) * Jc * Oc.T, P)
    assert clean(jets[1] / (N * s.sqrt(2)) - P).todok()
    print('PASS exact original scalar Green and retarded delta source; proper clock tau=N*t gives slope P61', flush=True)

    # Actual CAR coefficients: all70 canonical source ports, followed by the
    # same source R that produced the full61 family in scalar_dyson_time.
    raw_ports = [row for row in matter['primitive_ports'] if row['group'] == 'scalar']
    assert len(raw_ports) == 70
    W70 = [decode(row['Hamiltonian_coefficients']['constant']) for row in raw_ports]
    W61 = [decode(row['canonical_matter_vertex']) for row in source['projected_CAR_couplings']]
    for a in range(61):
        equal(W61[a], sum((R[Aidx, a] * W70[Aidx] for Aidx in range(70)), s.zeros(252)))
    qread = s.SparseMatrix.hstack(s.eye(61), s.zeros(61))
    canonical_slope = clean(qread * Ac * Jc * qread.T)
    equal(R * canonical_slope * R.T, jets[1])
    raw_line = line_contract(jets[1], W70, W70)
    canonical_line = line_contract(canonical_slope, W61, W61)
    assert raw_line == canonical_line
    assert len(raw_line) == 576
    assert raw_line[(0, 0, 149, 149)] == 243 * s.sqrt(30) / 6250
    # This equal-internal-index entry survives with distinct momenta; dropping
    # it before antisymmetrizing the full (p,i) labels would be incorrect.
    line_witness = raw_line[(0, 1, 149, 150)]
    assert line_witness == 243 * s.sqrt(30) / 6250

    zero_CAR = CAR_zero_mode_read(raw_line)
    assert len(zero_CAR) == 244
    actual_input, actual_output = (149, 150), (0, 1)
    direct = s.Integer(0)
    for (a, b), coefficient in jets[1].todok().items():
        for (i, j), left in W70[a].todok().items():
            for (k, ell), right in W70[b].todok().items():
                direct += coefficient * left * right * word_read(
                    i, k, ell, j, actual_input, actual_output)
    direct = s.simplify(direct)
    assert direct == zero_CAR[(*actual_output, *actual_input)] == 243 * s.sqrt(30) / 3125
    assert zero_CAR.get((0, 1, 145, 152), 0) == 0
    # The complete projector sum cancels this old single-W0 witness; the full
    # source family above still has nonzero normal products.
    branches = {1: W70, -1: [clean(-W.conjugate()) for W in W70]}
    branch_kernels = []
    full_branch_line = {}
    for left_branch in (1, -1):
        for right_branch in (1, -1):
            kernel = line_contract(jets[1], branches[left_branch], branches[right_branch])
            left_offset, right_offset = (0 if left_branch == 1 else 252), (0 if right_branch == 1 else 252)
            for (i, k, j, ell), value in kernel.items():
                full_branch_line[(i + left_offset, k + right_offset,
                                  j + left_offset, ell + right_offset)] = value
            branch_kernels.append({'left_matter_branch': left_branch,
                'right_matter_branch': right_branch,
                'source_Peierls_slope_line_kernel': encode_kernel(kernel),
                'nonzero_line_entries': len(kernel),
                'Dyson_constant_factor': '-I/2',
                'internal_equal_labels_on_distinct_momenta_retained': True})
    full_zero_CAR = CAR_zero_mode_read(full_branch_line)
    assert full_zero_CAR[(*actual_output, *actual_input)] == direct
    assert all(any((i < 252) == (left_branch == 1) and (k < 252) == (right_branch == 1)
                   for i, k, _, _ in full_branch_line)
               for left_branch in (1, -1) for right_branch in (1, -1))
    print('PASS actual all70/all61 CAR contraction:576 line entries; real-zero CAR244 entries, direct matrix element', direct, flush=True)
    print('PASS complete real504 branch contraction', len(full_branch_line),
          'ordered line entries and', len(full_zero_CAR), 'zero-mode CAR entries', flush=True)

    files = [HERE / name for name in [
        'scalar_canonical_phase.json', 'scalar_joint_hamiltonian.json',
        'independent_scalar_canonical_phase.json', 'independent_scalar_joint_hamiltonian.json',
        'full-matter-ports.json', 'scalar_dyson_time.py', 'scalar_dyson_time.json',
        'independent_scalar_dyson_time.json', 'ScalarCCR.lean', 'RealScalarFock.lean',
        'scalar_dyson_fixed_N.json', 'scalar_dyson_peierls.py']]
    result = {'root': ROOT_ID, 'source_sha256': source['source_sha256'],
        'scope': 'ACTUAL_SCALAR_N2_CCR_CONSTANT_TERM_AND_ORIGINAL_P61_RETARDED_SOURCE',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in files},
        'scalar_pair_momentum': list(map(str, KAPPA)), 'source_lapse': str(N),
        'pair_field_reader_positive': encode(Fplus), 'pair_field_reader_negative': encode(Fminus),
        'zero_field_reader': encode(Oc), 'pair_phase_G': encode(A), 'pair_CCR_J': encode(J),
        'zero_phase_G': encode(zero_A), 'zero_CCR_J': encode(Jc),
        'all_time_commutator': '[phi_sigma,A(t2),phi_sigma_prime,B(t1)]=i*(F_sigma exp(Apair*t2) J exp(Apair^T*t1) F_sigma_prime^T)_AB',
        'relative_time_reduction': 'Apair*J+J*Apair^T=0 makes the displayed two-time matrix F_sigma exp(Apair*(t2-t1)) J F_sigma_prime^T',
        'opposite_transfer_kernel': 'Delta_plus_minus(t)=Oc exp(Ac(kappa)*t) Jc Oc^T; Delta_minus_plus(t)=Delta_plus_minus(t,-kappa)',
        'same_transfer_commutator': 'plus-plus=minus-minus=0 on one nonzero unordered Fourier pair',
        'two_time_reciprocity': 'Delta(kappa,t)=-transpose(Delta(-kappa,-t)); transpose, not an independent Hilbert-adjoint identification',
        'whole70_initial_jets': [encode(value) for value in jets],
        'real_zero_initial_jets': [encode(value) for value in zero_jets],
        'retarded_delta_equation': '(Dt^2/N+N*L(kappa)) [theta(t)*Delta(t,kappa)] = P61*delta(t), with no delta-prime because Delta(0)=0',
        'original_full70_Green_numerator': encode(numerator), 'original_Green_denominator': str(denominator),
        'proper_clock': 'tau=N*t; Delta_proper(tau)=Delta(tau/N); initial derivative is P61 and (Dtau^2+L)*theta(tau)Delta_proper=P61*delta(tau)',
        'Dyson_clock_conversion': 'all displayed Dyson coefficients use coordinate time t; under tau=N*t the generators are A/N and V_I/N and dt=dtau/N; no N*sqrt2 clock substitution or external normalization is used',
        'original_source_sign': 'rho_real=-j_action_real; phi=Gret*rho_real=-Gret*j_action_real, using the same P61 Green and canonical W as the original real action',
        'pair_and_zero_normalization': 'one nonzero pair uses1/sqrt2 positive/negative readers; original real zero mode uses Oc without duplication or1/sqrt2',
        'ordered_N2_product': 'phi_A(t2)phi_B(t1)=1/2{phi_A(t2),phi_B(t1)}+i/2 Delta_AB(t2-t1)',
        'Dyson_N2_constant': '(-i)^2 times the ordered product gives -i/2 Delta_AB times the original ordered CAR density word; the Weyl quadratic contribution remains -1/2 times the anticommutator',
        'Weyl_quadratic_term_retained': True,
        'vacuum_Hadamard_or_positive_state_selected': False,
        'retarded_order': 'for t2>t1 the same Delta equals Gret; no time-ordered vacuum propagator or stationary self-energy is inferred',
        'all70_to_all61_source_contraction': 'sum_AB Delta70_AB W70_A tensor W70_B = sum_ab Delta61_ab W61_a tensor W61_b by W61=R^T W70 and Delta70=R Delta61 R^T',
        'direct_source_line_kernel_initial_slope': encode_kernel(raw_line),
        'direct_line_nonzero_entries': len(raw_line), 'actual_real_matter_branch_kernels': branch_kernels,
        'continuous_two_particle_labels': 'each ordered line keeps (p,i); k_out1=k_in1+kappa, k_out2=k_in2-kappa, and reversed orientation; antisymmetrize full momentum-index labels, not internal indices alone',
        'line_witness': {'output_internal_indices': [0,1], 'input_internal_indices': [149,150],
            'coefficient_derivative_at_t2_t1_zero': str(line_witness),
            'Dyson_constant_derivative': str(s.simplify(-s.I*line_witness/2))},
        'same_internal_distinct_momentum_witness': {'output_internal_indices': [0,0],
            'input_internal_indices': [149,149], 'coefficient_derivative': str(raw_line[(0,0,149,149)]),
            'not_removed_for_distinct_physical_momenta': True},
        'real_zero_mode_plus_branch_CAR_consumer': {'nonzero_entries': len(zero_CAR),
            'matrix_elements': encode_kernel(zero_CAR), 'incoming_occupation': list(actual_input),
            'outgoing_occupation': list(actual_output), 'direct_original_CAR_word_derivative': str(direct),
            'Dyson_constant_derivative': str(s.simplify(-s.I*direct/2)),
            'old_single_W0_reader_full_projector_sum': '0'},
        'complete_real_zero_mode_two_branch_CAR': {
            'internal_branch_carrier_dimension': 504,
            'source_matrix': 'diag(W_A,-conjugate(W_A))',
            'ordered_branch_line_entries': len(full_branch_line),
            'CAR_normal_ordered_nonzero_entries': len(full_zero_CAR),
            'matrix_elements': encode_kernel(full_zero_CAR),
            'all_four_matter_branch_combinations_included': True,
            'plus_witness_matrix_element': str(direct),
            'continuous_momentum_carrier_replaced_by_finite_internal_Fock': False},
        'source_current_time_dependence': 'the full coefficient uses the original interaction-picture matrices exp(-Aout*t)W_A exp(Ain*t) from scalar_dyson_time; at coincident time the first Delta slope has no matter-drift correction because Delta(0)=0',
        'full_N2_continuous_evolution_assembled': False,
        'full_four_block_interacting_spectrum_or_decay_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started,3)}
    (HERE / 'scalar_dyson_peierls.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS actual N2 source CCR constant and P61 retarded coupling', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
