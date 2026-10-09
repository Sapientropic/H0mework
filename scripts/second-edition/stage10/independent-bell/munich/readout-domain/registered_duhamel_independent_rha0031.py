"""Independent scalar recurrence and source transfer-complement checks."""
from fractions import Fraction as Q

import atomic_dipole as dipole
import fluorescence_channel as channel


def require(value, reason):
    if not value: raise ValueError(reason)


def tail(variation, order):
    require(Q(variation) >= 0, 'negative source variation is not a price')
    a = upper(variation); require(a >= 0 and type(order) is int and 0 <= order <= 128 and a < order+2,
                            'valid interaction suffix ratio required')
    first = Q(1)
    for j in range(1, order+2): first = first*a/j
    return upper(first*Q(order+2)/(Q(order+2)-a))


def upper(value):
    value = Q(value); quantum = 1 << 192
    quotient, remainder = divmod(value.numerator*quantum, value.denominator)
    return Q(quotient+int(remainder != 0), quantum)


def check(report, raw_source, paid_activity):
    require(report['schema'] == 'stage10-registered-Duhamel-full-gate-budget-first/rha0031' and
        report['source_identity'] == {'source': 'positiveSmoothUnifiedSource', 'root_visit': 10, 'current_tick': 16, 'next_tick': 17},
        'same source occurrence required')
    require(report['free_flow_is_complete_local_TP'] is True and report['physical_receipt_coimage_stays_frozen'] is True and
        report['inverse_TP_flow_used'] is False and report['large_atomic_H_norm_enters_interaction_tail'] is False,
        'stopped source decomposition changed')
    facts = paid_activity['source_activity']
    rates = list(map(Q, facts['complete_Gamma_family_natural_loss_operator_norms_per_second']))
    background = sum(map(Q, facts['four_source_BG_rate_upper_per_second']), Q(0))
    source = raw_source['complete_driven_field_source']
    transfer = tuple(tuple(channel._complex_record(v) for v in row)
                     for row in source['working_common_optical_source']['generated_four_by_six_transfer'])
    gram = [[sum((transfer[p][j].conjugate()*transfer[p][k] for p in range(4)), dipole.ComplexRadical())
             for k in range(6)] for j in range(6)]
    require(facts['full_detected_transfer_gram'] == [[v.serialize() for v in row] for row in gram],
            'independent full optical Gram differs from the paid source')
    for j in range(6):
        for k in range(6):
            lost = dipole.ComplexRadical(int(j == k))-gram[j][k]
            require(lost+sum((transfer[p][k]*transfer[p][j].conjugate() for p in range(4)),
                            dipole.ComplexRadical()) == dipole.ComplexRadical(int(j == k)),
                    'unobserved and registered source environments do not sum to the original bath')
    duration = Q(report['detector_interval_seconds'][1])-Q(report['detector_interval_seconds'][0])
    mass = Q(report['source_positive_mass_upper']); old = Q(report['old_input_trace_norm_error_once'])
    require(duration >= 0 and mass >= 0 and old >= 0, 'source mass and exact original interval required')
    checked = []
    for label, kappa in (('current_optical_member', Q(facts['registered_optical_operator_norm_square_upper'])),
                         ('whole_objective_transfer_domain', Q(facts['source_objective_operator_norm_square_upper']))):
        activity = kappa*sum(rates, Q(0))+background; variation = 2*duration*activity
        branch = report['variation_domains'][label]
        require(Q(branch['registered_activity_upper_per_second']) == activity and
            Q(branch['interaction_variation_upper']) == variation, 'source activity/Gamma/optical binding changed')
        require([b['retained_order'] for b in branch['tail_budgets']] == [0, 2, 4, 6, 8, 10, 12, 16],
                'complete fixed order inventory required')
        for item in branch['tail_budgets']:
            if upper(variation) >= item['retained_order']+2:
                require(item == {'retained_order': item['retained_order'], 'geometric_ratio_valid': False},
                        'invalid geometric denominator must remain unpriced')
                continue
            value = tail(variation, item['retained_order'])
            require(Q(item['whole_instrument_operator_tail_upper']) == value and
                Q(item['interaction_variation_upper']) == upper(variation) and
                Q(item['source_mass_times_tail_upper']) == upper(mass*value) and
                item['tail_below_old_input_error'] is (upper(mass*value) < old), 'independent factorial/geometric tail differs')
        checked.append({'domain': label, 'interaction_variation_upper': str(variation),
            'first_registered_order_below_old_input_error': next((r['retained_order'] for r in branch['tail_budgets']
                                                               if r.get('tail_below_old_input_error')), None)})
    require(all(report[name] is False for name in ('free_flow_and_quadrature_residuals_already_paid',
        'full_gate_trajectory_generated', 'actual_hardware_member_asserted', 'actual_hardware_uniquely_identified', 'controller_advance')),
        'source representation was promoted to an uncomputed actual trajectory')
    return {'schema': 'stage10-independent-registered-Duhamel-budget/rha0031',
        'all_36_transfer_complement_coordinates_checked': True, 'factorial_recurrence_tail_checked': True,
        'whole_Gamma_family_and_objective_transfer_domain_checked': True, 'domains': checked,
        'full_gate_trajectory_generated': False, 'actual_hardware_uniquely_identified': False}
