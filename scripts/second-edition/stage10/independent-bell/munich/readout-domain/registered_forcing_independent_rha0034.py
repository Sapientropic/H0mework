"""Independent raw-bath compilation of the complete first forcing program."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import fluorescence_channel as channel
import gaussian_atomic_pulse_source as gaussian
import bsm_retry_source as bsm
import retarded_receipt_activity_envelope as activity
import completed_retarded_inlet_rha0028 as paid


def require(value, reason):
    if not value: raise ValueError(reason)


def upper(value):
    value = Q(value); unit = 1 << 192
    whole, remainder = divmod(value.numerator*unit, value.denominator)
    return Q(whole+int(remainder != 0), unit)


def digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def raw_programs(raw):
    field = raw['complete_driven_field_source']
    transfer = [[channel._complex_record(v) for v in row]
        for row in field['working_common_optical_source']['generated_four_by_six_transfer']]
    groups = {}; operators = {}; programs = {'quiet': [], ('cross', 0, 1): [], ('cross', 1, 0): [], ('drive', 0): [], ('drive', 1): []}
    for side, leg in enumerate(field['physical_legs']):
        for jump in leg['original_physical_natural_jumps']:
            group = tuple(jump['group']); mu = 3*side+dipole.Q_COMPONENTS.index(jump['q']); rate = Q(jump['physical_amplitude_squared_per_second'])
            current = groups.setdefault(group, (rate, {})); require(current[0] == rate and mu not in current[1], 'raw resolved bath identity changed')
            current[1][mu] = side, gaussian._matrix(jump['normalized_natural_jump_operator'])
    def emit(component, port, coefficient, first=None, second=None):
        coefficient = dipole.complex_exact(coefficient)
        if not coefficient: return
        left, right = [None, None], [None, None]
        for target, item in ((left, first), (right, second)):
            if item is None: continue
            side, matrix = item; encoded = channel._input_record(matrix); identity = digest(encoded)
            operators[identity] = encoded; target[side] = identity
        for seen, scale in ((True, coefficient), (False, -coefficient)):
            counts = [int(seen and p == port) for p in range(4)]
            programs[component].append({'target': {'counts': counts, 'receipt': None},
                'coefficient': scale.serialize(), 'left_operators': left, 'right_operators': right})
    for port, rate in enumerate(raw['BG_source']['BG_rates_per_second']): emit('quiet', port, Q(rate))
    for group, (rate, modes) in groups.items():
        for mu, (side, first) in modes.items():
            for nu, (other, second) in modes.items():
                component = ('cross', side, other) if group[0] == 'D2' and side != other else 'quiet'
                for port in range(4):
                    emit(component, port, rate*transfer[port][mu]*transfer[port][nu].conjugate(),
                         (side, first), (other, dipole.matrix_adjoint(second)))
    return operators, programs


def check(report, law, bank):
    require(report['schema'] == 'stage10-source-complete-first-registered-forcing/rha0034', 'original complete forcing DAG required')
    raw = law.record(); field = raw['complete_driven_field_source']; operators, programs = raw_programs(raw)
    frozen = paid.paid.frozen(paid.HERE/'free-density-bank-first-rha0033.json')
    require(bank == json.loads(frozen) and report['paid_free_bank_sha256'] == hashlib.sha256(frozen).hexdigest() and
        bank['all_local_relative_accuracy_gates_passed'] is True and bank['new_uniform_tensor_error_below_old_input_error'] is True,
        'the independent program must consume the same frozen complete free bank')
    require([(n['side'], n['factor_index'], n['factor_id'], n['checked_curve']) for n in report['free_curve_nodes']] ==
        [(n['side'], n['factor_index'], n['factor_id'], n['checked_curve']) for n in bank['rows']], 'complete original factor incidence changed')
    for node in report['free_curve_nodes']:
        binding = node['checked_curve']; relative = Path(binding['path'])
        require(not relative.is_absolute() and '..' not in relative.parts, 'checked curve outside its workspace')
        path = paid.ROOT/relative
        require(path.stat().st_size == binding['bytes'] and hashlib.sha256(path.read_bytes()).hexdigest() == binding['sha256'], 'frozen local curve evidence changed')
        checked = json.loads(path.read_text()); side = node['side']; stream = node['Chebyshev_stream']; relative = Path(stream['path'])
        require(not relative.is_absolute() and '..' not in relative.parts, 'free stream outside its workspace')
        path = paid.ROOT/relative
        require(path.stat().st_size == stream['bytes'] == checked['untrusted_stream']['bytes'] and
            hashlib.sha256(path.read_bytes()).hexdigest() == stream['sha256'] == checked['untrusted_stream']['sha256'] and
            checked['original_density_source']['Gaussian_source'] == field['Gaussian_source_legs'][side] and
            checked['stream_header']['source_factor_id'] == node['factor_id'] and checked['registered_relative_accuracy_passed'] is True,
            'a full local source, factor or checked stream changed')
    require(report['operator_nodes'] == operators, 'independent raw local operator inventory differs')
    actual = {row['component'] if type(row['component']) is str else tuple(row['component']): row['rows']
              for row in report['original_registered_component_programs']}
    require(set(actual) == set(programs) and all(sorted(map(channel._canonical, actual[c])) ==
        sorted(map(channel._canonical, programs[c])) for c in programs), 'a source bath, Mark target, signed branch or component changed')
    require(all(len(pair) == 2 and pair[0] != pair[1] for _, pair in bsm.PATTERNS), 'the original first receipt requires two distinct ports')
    g0, g1 = map(Q, raw['gate_seconds']); require(report['source_detector_interval_seconds'] == [str(g0), str(g1)], 'same full detector interval required')
    starts = [g0-Q(x)-Q(y) for x, y in zip(field['flight_seconds'], field['emission_origins_seconds'])]
    require(min(starts) >= 0 and report['source_retarded_local_cuts_seconds'] == list(map(str, starts)), 'same source activation cuts required')
    omega = [Q(row['carrier_angular_frequency_per_second']) for row in field['Gaussian_source_legs']]
    phases = {tuple(row['component']): row for row in report['source_relative_phase_words']}
    require(set(phases) == {('cross', 0, 1), ('cross', 1, 0)}, 'both original interference words required')
    for component, row in phases.items():
        s, o = component[1:]
        require(Q(row['angle_at_detector_gate_start']) == omega[o]*starts[o]-omega[s]*starts[s] and
                Q(row['angular_frequency_per_second']) == omega[o]-omega[s], 'source relative phase or flight changed')
    norm = Q(0)
    for rows in programs.values():
        for row in rows:
            term = bsm._entry_norm({(0, 0): channel._complex_record(row['coefficient'])}, bits=192)
            for key in ('left_operators', 'right_operators'):
                for identity in row[key]:
                    if identity is not None: term *= bsm._entry_norm(gaussian._matrix(operators[identity]), bits=192)
            norm += term
    norm = upper(norm); clock = field['reference_clock']; centre = Q(clock['Gamma_numerical_centre'])
    lo, hi = map(Q, clock['angular_Gamma_enclosure_per_second']); delta = max(centre-lo, hi-centre)/centre
    require(0 < lo <= centre <= hi and Q(report['registered_component_sum_norm_per_second_upper']) == norm and
            Q(report['Gamma_relative_error_upper']) == delta and report['Gamma_registered_rate_scale_interval'] == [str(lo/centre), str(hi/centre)],
            'original Gamma family or complete row-norm bound changed')
    cap = activity.RetardedReceiptActivityEnvelope(law, bits=192).record()['source_activity']
    lam = Q(cap['registered_total_activity_upper_per_second']); require(Q(report['registered_total_activity_upper_per_second']) == lam, 'original activity bound changed')
    new = Q(bank['whole_new_uniform_free_tensor_error']); old = Q(bank['old_whole_input_error_once']); mass = Q(report['source_positive_mass_upper'])
    require(Q(report['new_uniform_free_tensor_error']) == new and Q(report['old_whole_input_error_once']) == old, 'source free bank or old price changed')
    p = report['forcing_prices']; free, gamma = 2*(g1-g0)*lam*new, (g1-g0)*delta*norm*(mass+old+new)
    require(Q(p['new_free_bank_forcing_integral_price']) == upper(free) and
        Q(p['registered_rate_Gamma_integral_price']) == upper(gamma) and Q(p['whole_new_forcing_integral_price']) == upper(free+gamma) and
        Q(p['central_initial_trace_norm_upper']) == mass+old and Q(p['signed_central_initial_tail_mass_upper']) == mass+old and
        p['old_input_error_included_in_free_bank_defect'] is False, 'independent full forcing price or one-time input payment differs')
    require(len(report['free_curve_nodes']) == bank['complete_local_residual_count'] == 10 and
        all(not report[key] for key in ('quantum_joint_matrix_expanded', 'source_phase_words_numerically_evaluated',
            'first_registered_time_integral_evaluated', 'source_Gaussian_field_cut_off', 'inverse_TP_flow_used',
            'source_marks_or_repeated_emissions_removed', 'full_control_clock_record_square_certified', 'full_gate_instrument_or_response_anchor_certified',
            'actual_hardware_uniquely_identified', 'controller_advance')), 'forcing representation promoted beyond its completed scope')
    return {'schema': 'stage10-independent-first-registered-forcing/rha0034',
        'raw_resolved_environment_groups': len(groups_from_raw(field)), 'complete_operator_nodes': len(operators),
        'complete_registered_rows': sum(map(len, programs.values())), 'all_signed_Mark_targets_checked': True,
        'both_relative_phase_words_checked': True, 'full_Gamma_and_forcing_prices_checked': True,
        'first_registered_time_integral_evaluated': False, 'actual_hardware_uniquely_identified': False}


def groups_from_raw(field):
    return {tuple(j['group']) for leg in field['physical_legs'] for j in leg['original_physical_natural_jumps']}
