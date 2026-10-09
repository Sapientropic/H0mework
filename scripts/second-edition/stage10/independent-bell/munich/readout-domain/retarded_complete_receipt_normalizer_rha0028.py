"""Whole-gate mass bounds from the invariant empty face and source activity."""
from fractions import Fraction as Q

import retarded_empty_receipt_time_measure as empty
import retarded_receipt_activity_envelope as activity


def bounds(source, *, interval=None, bits=192):
    empty._CHECK(); activity._CHECK()
    empty._require(type(source) is empty.prepared.PreparedRetardedGaussianInlet,
                   'closed current source-issued retarded inlet required')
    raw = source.record(); law = source._law
    lower, upper = map(Q, raw['retarded_detector_law']['gate_seconds'] if interval is None else interval)
    # H, drive and every jump preserve ionic occupation; the scalar receipt
    # effect is block diagonal.  Its other positive blocks cannot cancel II.
    projected = empty.RetardedEmptyReceiptTimeMeasure(law).apply_inlet(source, lower, upper, bits=bits)
    envelope = activity.RetardedReceiptActivityEnvelope(law, bits=bits)
    cap = envelope.first_receipt_cap(interval=(lower, upper))
    mass_upper = Q(raw['source_positive_mass_upper'])
    union_upper = mass_upper*Q(cap['whole_first_receipt_input_contraction_upper'])
    rows = [{'pattern': item['pattern'], 'whole_instrument_mass_lower': item['projected_receipt_mass_lower'],
             'whole_instrument_mass_upper': str(union_upper)} for item in projected['four_pattern_poststates']]
    union_lower = sum((Q(item['whole_instrument_mass_lower']) for item in rows), Q(0))
    empty._require(0 <= union_lower <= union_upper, 'whole receipt mass bounds are inconsistent')
    return {'schema': 'stage10-complete-retarded-receipt-normalizer/rha0028',
        'source_record': raw, 'receipt_interval_seconds': list(map(str, (lower, upper))),
        'invariant_empty_face': projected, 'complete_source_activity_cap': cap,
        'whole_first_receipt_mass_interval': list(map(str, (union_lower, union_upper))),
        'four_pattern_mass_bounds': rows, 'whole_first_receipt_strictly_positive': union_lower > 0,
        'four_pattern_masses_strictly_positive': all(Q(item['whole_instrument_mass_lower']) > 0 for item in rows),
        'source_positive_mass_upper': str(mass_upper),
        'source_law': 'receipt effect = direct sum of positive occupation blocks; E_II=p_BG P_II; E>=E_II',
        'other_occupation_blocks_replaced_by_empty_face': False,
        'complete_gate_state_or_response_difference_computed': False,
        'generation1_asserted': False, 'actual_hardware_member_asserted': False,
        'actual_hardware_uniquely_identified': False, 'controller_advance': False}
