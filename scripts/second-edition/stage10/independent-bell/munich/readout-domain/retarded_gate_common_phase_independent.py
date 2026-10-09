"""Entry-degree and explicit PC execution checks for the count coimage producer."""
from fractions import Fraction as Q
from math import factorial

import retarded_prepared_excitation_field_source as source


def require(value, reason):
    if not value:
        raise ValueError(reason)


def degree(matrix, weight):
    return all(not value or int(source.dipole.STATES[i].family == 'D2')-
               int(source.dipole.STATES[j].family == 'D2') == weight for (i, j), value in matrix.items())


def check_grading(pulses, optics, report):
    require(report.get('schema') == 'stage10-same-source-common-phase-retarded-count-coimage/v1/complete-source-generator-grading', 'grading schema')
    rows, groups = [], {}
    for side, pulse in enumerate(pulses):
        h, r, a = [source.gaussian._matrix(pulse[name]) for name in
            ('complete_static_H_per_second', 'complete_natural_R_per_second', 'source_raising_operator_per_second')]
        require(h == source.dipole.matrix_adjoint(h) and degree(h, 0) and degree(r, 0) and degree(a, 1), 'source matrix degree')
        recovered = {}
        for item in pulse['original_physical_natural_jumps']:
            label = tuple(item['group']); jump = source.gaussian._matrix(item['normalized_natural_jump_operator'])
            weight = -int(label[0] == 'D2'); rate = Q(item['physical_amplitude_squared_per_second'])
            require(degree(jump, weight) and rate >= 0, 'source jump degree')
            row = groups.setdefault(label, {'rate': rate, 'modes': 0})
            require(row['rate'] == rate, 'same resolved width on both arms')
            row['modes'] += 1
            source.field._add(recovered, source.dipole.matrix_product(source.dipole.matrix_adjoint(jump), jump), rate)
        require(recovered == r, 'complete original recycling must recover R')
        rows.append({'side': side, 'static_entries': len(h), 'loss_entries': len(r), 'raising_entries': len(a),
                     'natural_jumps': len(pulse['original_physical_natural_jumps'])})
    expected = [{'group': list(label), 'degree': -int(label[0] == 'D2'), 'mode_count': value['modes'], 'rate': str(value['rate'])}
                for label, value in sorted(groups.items())]
    transfer = tuple(tuple(source.channel._complex_record(v) for v in row) for row in optics['generated_four_by_six_transfer'])
    source.joint.passive_transfer(transfer)
    require(report['local_inventories'] == rows and report['resolved_port_loss_groups'] == expected, 'complete source grading inventory')
    require(report['raising_lowering_degrees'] == [1, -1] and report['quiet_natural_loss_port_and_background_degree'] == 0 and
        report['Mark_targets_change_line_degree'] is False and report['trace_on_projected_input_degree'] == 0 and
        report['relative_time_count_instrument_covariant'] is True and report['all_photon_numbers_and_original_Mark_words_covered'] is True,
        'generator-to-word covariance scope')
    return True


def clock_check(raw, report):
    parent = raw['preparation_source']; policy = raw['fixed_pump_clock_member']['restart_policy']
    require(policy in ('continuous', 'restart_on_preparation', 'restart_on_pump', 'source_PC_policy'), 'clock policy')
    support = parent['source_expiry_free_preparation_support']
    prefix = sum(map(Q, support['physical_pump_durations_seconds']), Q(0))
    gate = list(map(Q, raw['source_gate_offsets_from_pump_end_seconds']))
    flights = list(map(Q, raw['flight_seconds'])); horizon = gate[1]-min(flights)
    origins = list(map(Q, raw['original_prior_driven_field_source']['emission_origins_seconds']))
    old_prefix = [sum((Q(p['raw_controls']['duration_seconds']) for p in side[:2]), Q(0)) for side in parent['original_source_local_plans']]
    same_age = origins[0] == origins[1] and old_prefix[0] == old_prefix[1]
    equal = Q(raw['source_generated_zero_line_chart_pulses'][0]['carrier_angular_frequency_per_second']) == Q(
        raw['source_generated_zero_line_chart_pulses'][1]['carrier_angular_frequency_per_second'])
    before = max(map(Q, raw['pump_end_time_family_seconds']))+horizon < Q(support['earliest_possible_recent_expiry_seconds'])
    cuts = []
    period = Q(parent['source_poll_period_seconds']); rules = {r['name']: r for r in parent['raw_PC_rules']}
    require(period > 0 and gate[0] >= max(flights) and horizon > 0, 'source causal clocks')
    for face in support['source_all_Ready_face_PC_updates']:
        row = [Q(0)]
        if policy == 'source_PC_policy' and parent['original_PC_phase_policy'] == 'restart_on_stage_change':
            state = face['original_high_poll_PC_state']['stage']
            for index in range(1, int((prefix+horizon)//period)+1):
                following = rules[state]['high_next']
                time = index*period-prefix
                if state != following and Q(0) < time < horizon:
                    row.append(time)
                state = following
        row.append(horizon); cuts.append(row)
    constant = all(len(row) == 2 for row in cuts)
    require(report['same_two_leg_phase_age'] is same_age and report['same_raw_carrier'] is equal and
        report['restart_policy'] == policy and report['expiry_free_whole_gate_support'] is before and
        report['all_Ready_face_phase_cuts_seconds'] == [list(map(str, row)) for row in cuts] and
        report['common_phase_constant_on_each_whole_gate_fibre'] is constant and
        report['relative_count_readout_factors_through_quantum_coimage'] is (same_age and equal and before and constant) and
        report['absolute_timestamp_or_joint_queue_readout_factored'] is False, 'independent complete clock qualification')
    return True


def check_future_tail(raw, report, bits=192):
    earliest = min(map(Q, raw['pump_end_time_family_seconds'])); old = raw['original_prior_driven_field_source']
    clock = raw['reference_clock']; centre = Q(clock['Gamma_numerical_centre'])
    ratio = max(Q(clock['angular_Gamma_enclosure_per_second'][1]), centre)/centre
    require(len(report['sides']) == 2, 'complete future tail inventory')
    total = Q(0)
    for side, (pulse, row) in enumerate(zip(old['Gaussian_source_legs'], report['sides'])):
        cut = earliest-Q(old['emission_origins_seconds'][side]); x = cut-Q(pulse['centre_seconds']); variance = Q(pulse['sigma_squared_seconds'])
        if x > 0:
            radius = x*x/(4*variance); envelope = min(Q(factorial(n))/radius**n for n in range(17))
            integral = 2*variance*envelope/x
        else:
            integral = Q(row['original_field_tail_integral_upper_seconds'])
            require(integral >= 0 and integral*integral >= 36*variance, 'future full Gaussian integral upper')
        norm = source.gaussian._norm(source.gaussian._matrix(pulse['source_raising_operator_per_second']), bits)
        expected = 4*ratio*norm*integral
        require(row['side'] == side and Q(row['source_earliest_old_local_cut_seconds']) == cut and
            Q(row['original_field_tail_integral_upper_seconds']) == integral and Q(row['source_raising_norm_upper_per_second']) == norm and
            Q(row['new_future_operator_difference_upper']) == expected, 'independent future source price')
        total += expected
    require(Q(report['future_time_retaining_instrument_difference_per_input_norm']) == total and
        Q(report['future_instrument_difference_upper']) == total*Q(raw['same_positive_CEM_mother_mass_upper']) and
        report['past_quantum_coimage_error_reused_as_fine_TV'] is False, 'future operator price scope')
    return True


def check_count_gate(report, optics):
    from common_optical_readout import CommonOpticalReadout
    original, proof = CommonOpticalReadout.from_record(optics).bsm_gate(compilation_bits=160)
    require(report['raw_bsm_gate'] == original.record() and report['same_optical_gate_certificate'] == proof and
            report['raw_bsm_source_used_for_count_targets_only'] is True and
            report['physical_gate_clock_owner'] == 'source_clock_qualification.complete_relative_gate_seconds', 'same source gate/clock ownership')
    gate = source.retarded.bsm.BSMSource.from_record(report['raw_bsm_gate'])
    observed = {source.retarded.bsm.INITIAL}; previous = set()
    while previous != observed:
        previous = set(observed)
        observed |= {gate.target(mark, port) for mark in previous if mark.receipt is None for port in range(4)}
    marks = sorted(observed, key=lambda m:(m.counts,-1 if m.receipt is None else m.receipt))
    encode = lambda m:{'counts':list(m.counts),'receipt':m.receipt}
    require(len(marks) == 45 and report['complete_Mark_inventory'] == list(map(encode,marks)) and
            report['four_port_targets'] == [{'source':encode(m),'targets':[] if m.receipt is not None else
                [encode(gate.target(m,p)) for p in range(4)]} for m in marks] and report['receipt_coimage_stops_at_first_receipt'] is True,
            'complete same-source Mark word selector')
    return True
