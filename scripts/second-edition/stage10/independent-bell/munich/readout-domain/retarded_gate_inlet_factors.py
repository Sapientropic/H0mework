"""Read the checked retarded-cut factors, preserving their source identities.

This readout does not certify JSON provenance or issue a new inlet.  Its
callers authenticate the frozen source payload before using its matrices.
"""
from fractions import Fraction as Q

import prepared_retarded_gaussian_inlet as inlet


def require(value, reason):
    if not value:
        raise ValueError(reason)


def factor_terms(source_record, *, expected_local_cuts=None):
    require(type(source_record) is dict and source_record.get('schema') == inlet.SCHEMA,
            'the complete checked retarded inlet is required; a pump-end record is not a gate inlet')
    cuts = tuple(map(Q, source_record['actual_retarded_local_cuts_seconds']))
    require(len(cuts) == 2 and min(cuts) >= 0, 'both nonnegative checked retarded cuts are required')
    law = source_record['retarded_detector_law']; field = law['complete_driven_field_source']
    start = Q(law['gate_seconds'][0])
    actual = tuple(start-Q(origin)-Q(flight) for origin, flight in
                   zip(field['emission_origins_seconds'], field['flight_seconds']))
    require(len(actual) == 2 and cuts == actual and Q(source_record['fixed_detector_gate_start_seconds']) == start,
            'the saved factor cuts must equal the original gate minus source origin and flight')
    if expected_local_cuts is not None:
        require(tuple(map(Q, expected_local_cuts)) == cuts, 'explicit expected retarded cuts do not match this inlet')
    parent = source_record['source_issued_two_pump_source']
    require(source_record['source_factor_ids'] == parent['source_tensor_factor_ids'], 'the original tensor factor identities changed')
    banks = source_record['checked_local_density_inventories']
    require(len(banks) == 2 and len(parent['source_issued_two_pump_factor_inlets']) == 2, 'both checked factor banks are required')
    endpoints = []
    for side, rows in enumerate(banks):
        ids = [item['factor_id'] for item in rows]
        expected = [item['factor_id'] for item in parent['source_issued_two_pump_factor_inlets'][side]]
        require(ids == expected and len(ids) == len(set(ids)), 'every source factor must reach its own checked retarded cut')
        bank = {}
        for item in rows:
            require(Q(item['new_local_trace_norm_error']) >= 0, 'the checked local price must be nonnegative')
            matrix = inlet.channel._read_input(item['complete_retarded_local_endpoint'], inlet.full.DIMENSION)
            require(matrix == inlet.dipole.matrix_adjoint(matrix), 'a complete Hermitian source factor is required')
            bank[item['factor_id']] = matrix
        endpoints.append(bank)
    terms = []
    for left, right in source_record['source_factor_ids']:
        require(left in endpoints[0] and right in endpoints[1], 'a retarded tensor factor is missing')
        terms.append((endpoints[0][left], endpoints[1][right]))
    return tuple(terms)
