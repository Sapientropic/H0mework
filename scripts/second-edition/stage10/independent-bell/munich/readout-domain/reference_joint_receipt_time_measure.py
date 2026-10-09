"""One reference Gamma family pays the complete two-signal receipt CP.

The literal chronological Bose integral remains owned by its original source.
The parameter payment compares its two true contraction families, so centre
rounding is paid separately and the four-background family is preserved.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import b_field_photon_source as photons
import b_field_receipt_time_measure as joint_time
import reference_photon_time_measure as reference


SCHEMA = 'stage10-reference-clock-joint-receipt-time-source/v1'
_ISSUED = set()


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _bindings():
    paths = (Path(__file__), Path(photons.__file__), Path(joint_time.__file__), Path(reference.__file__))
    return {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def _parameter_payment(raw, report, bits):
    source = raw['reference_centre_field_source']
    left, right = map(Q, report['first_receipt_restriction_seconds'])
    g0, g1 = map(Q, source['gate_seconds'])
    clock = raw['reference_clock']
    gamma = Q(clock['Gamma_numerical_centre'])
    hi = max(gamma, Q(clock['angular_Gamma_enclosure_per_second'][1]))
    _, root_hi = reference._sqrt_bounds(hi, bits)
    _, root_c = reference._sqrt_bounds(gamma, bits)
    groups = sorted({tuple(item['group']) for item in source['physical_legs'][0]['original_physical_natural_jumps']})
    area = ((right-g0)**2-(left-g0)**2)/2
    cache = {}
    def leg(side, group, port):
        key = side, group, port
        if key not in cache:
            price = reference._clock_payment(raw, source, side, group, port, left, right, right, bits)
            norm = Q(price['normalized_jump_operator_norm_upper'])
            cache[key] = (root_hi*norm, root_c*norm, Q(price['uniform_reference_amplitude_payment']))
        return cache[key]
    total, records = Q(0), []
    zero = report['source_generated_exact_zero_two_signal_column']
    if not zero:
        for pattern in report['patterns']:
            ports = photons.bsm.PATTERNS[pattern][1]
            for p, q in (ports, ports[::-1]):
                for early in groups:
                    for late in groups:
                        a, ac, ea = leg(0, early, p)
                        b, bc, eb = leg(1, late, q)
                        c, cc, ec = leg(0, late, q)
                        d, dc, ed = leg(1, early, p)
                        amplitude_error = ea*b+ac*eb+ec*d+cc*ed
                        true_norm, centre_norm = a*b+c*d, ac*bc+cc*dc
                        density_error = amplitude_error*(true_norm+centre_norm)
                        price = area*density_error
                        total += price
                        if price:
                            records.append({'pattern': pattern, 'ordered_ports': [p, q],
                                'early_group': list(early), 'late_group': list(late),
                                'reference_amplitude_error_upper': str(amplitude_error),
                                'true_Gamma_and_centre_amplitude_norm_upper': [str(true_norm), str(centre_norm)],
                                'integrated_reference_density_payment': str(price)})
    beta = sum(map(Q, source['common_optical_source']['background_rates']), Q(0))
    delta = Q(clock['Gamma_numerical_error'])
    background_payment = Q(0) if zero else delta*(g1-g0)*beta
    return {'reference_clock': clock, 'complete_group_and_Bose_parameter_prices': records,
        'original_chronological_triangle_area_upper': str(area),
        'whole_signal_reference_payment': str(total),
        'whole_no_BG_reference_payment': str(background_payment),
        'whole_reference_clock_payment': str(total+background_payment),
        'no_BG_bound': 'deltaGamma*whole_gate_width*sum(original_normalized_BG); whole CP trace contraction',
        'two_Bose_assignments_consumed': True, 'centre_curve_error_repeated': False,
        'BG_parameter_payment_per_source_instrument_once': True}


class ReferenceJointReceiptTimeMeasure:
    def __init__(self, parent, certificates):
        _check()
        _require(type(parent) is reference.ReferencePhotonTimeSource,
                 'closed reference physical field source required; a density or marginal law is not input')
        raw = reference.ReferencePhotonTimeSource.record(parent)
        measure = joint_time.BFieldReceiptTimeMeasure(parent._centre, certificates)
        record = joint_time.BFieldReceiptTimeMeasure.record(measure)
        _require(record['complete_two_arm_field_mother'] == raw['reference_centre_field_source'],
                 'joint receipt must retain the same two reference physical arms')
        self._parent, self._measure = parent, measure
        self._value = {'schema': SCHEMA, 'reference_field_source': raw,
            'centre_joint_source': record, 'source_bindings': _bindings(), 'controller_advance': False}
        self._seal = photons._digest(self._value)
        _ISSUED.add(self._seal)

    def record(self):
        _check()
        _require(type(self) is ReferenceJointReceiptTimeMeasure and
                 set(vars(self)) == {'_parent', '_measure', '_value', '_seal'} and
                 self._seal in _ISSUED and self._seal == photons._digest(self._value) and
                 self._value['source_bindings'] == _bindings() and
                 reference.ReferencePhotonTimeSource.record(self._parent) == self._value['reference_field_source'] and
                 joint_time.BFieldReceiptTimeMeasure.record(self._measure) == self._value['centre_joint_source'],
                 'reference joint source, Gamma, chronological curve or complete field mother changed')
        return photons._copy(self._value)

    def interval_column(self, row, column, start, stop, *, patterns=None, bits=192):
        raw = ReferenceJointReceiptTimeMeasure.record(self)
        centre = joint_time.BFieldReceiptTimeMeasure.interval_column(self._measure, row, column, start, stop,
                                                                   patterns=patterns, bits=bits)
        payment = _parameter_payment(raw['reference_field_source'], centre, bits)
        price = Q(payment['whole_reference_clock_payment'])
        return {'schema': SCHEMA+'/joint-CP-column', 'source_record': raw,
            'reference_centre_CP_certificate': centre, 'reference_clock_price': payment,
            'four_pattern_poststates': centre['four_pattern_poststates'],
            'source_matrix_unit': [row, column], 'first_receipt_restriction_seconds': list(map(str, (start, stop))),
            'centre_curve_and_scalar_error': centre['whole_trace_norm_error_upper'],
            'whole_reference_clock_payment': str(price),
            'whole_trace_norm_error_upper': str(Q(centre['whole_trace_norm_error_upper'])+price),
            'complete_reference_family_and_BG_mother': raw['reference_field_source'],
            'probability_scope': centre['probability_scope'],
            'full_record_or_actual_hardware_identity_asserted': False,
            'centre_complete_quantum_poststate_changed': False}


def _fingerprint(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _execution():
    functions = (_require, _bindings, _parameter_payment, _fingerprint, _execution, _check,
                 reference.ReferencePhotonTimeSource.record, reference._clock_payment, reference._sqrt_bounds,
                 joint_time.BFieldReceiptTimeMeasure.__init__, joint_time.BFieldReceiptTimeMeasure.record,
                 joint_time.BFieldReceiptTimeMeasure.interval_column)
    methods = tuple(_fingerprint(member) for member in vars(ReferenceJointReceiptTimeMeasure).values() if callable(member))
    return tuple(map(_fingerprint, functions)), methods, SCHEMA


def _check():
    if _check is not _CHECK or _check.__code__ is not _CHECK_CODE or \
       _execution is not _EXECUTION or _execution.__code__ is not _EXECUTION_CODE or _execution() != _EXPECTED:
        raise ValueError('reference joint photon source execution changed')


_CHECK, _CHECK_CODE = _check, _check.__code__
_EXECUTION, _EXECUTION_CODE = _execution, _execution.__code__
_EXPECTED = _execution()
