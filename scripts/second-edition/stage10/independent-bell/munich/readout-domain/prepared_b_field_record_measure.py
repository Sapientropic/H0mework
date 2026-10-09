"""The source-time B-field receipt measure enters the original record cells.

The fixed receipt-relative CEM map acts on each complete measure mu(B).
The native source epoch is already included in its physical gate; UID and
Unix inverse cells therefore use t/unit, without adding the Ready time.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import prepared_b_field_receipt as prepared
import prepared_record_measure as records
import reference_response_window_source as response
import full_zeeman_cem_source as cem


SCHEMA = 'stage10-prepared-B-field-original-record-measure/v1'
_RESPONSE_CHECK = response._CHECK
_CEM_CHECK = cem._CHECK


def _require(value, message):
    if not value:
        raise ValueError(message)


def _response_module():
    return response


def _bindings():
    modules = (prepared, records, _response_module(), cem)
    paths = (Path(__file__), *(Path(module.__file__) for module in modules))
    return {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def _restriction(rows, raw_writer, timing, modes, gate_seconds):
    cell, faces, reasons = records._record_cell(rows, raw_writer.encoders, raw_writer,
                                              timing.events(), modes)
    unit = timing.seconds_per_unit
    gate = records.clock.Interval(*(Q(t)/unit for t in gate_seconds), False, True)
    selected = None if cell is None else records.clock.intersect((cell, gate))
    start = Q(gate_seconds[0])
    bounds = (start, start) if selected is None else (selected.lower*unit, selected.upper*unit)
    return selected, cell, faces, reasons, bounds


def _background_upper(source_record, empty):
    if empty:
        return Q(0)
    physical = source_record['reference_joint_instrument']['reference_field_source']
    raw = physical['reference_centre_field_source']
    start, stop = map(Q, raw['gate_seconds'])
    gamma = Q(physical['reference_clock']['angular_Gamma_enclosure_per_second'][1])
    rate = gamma*sum(map(Q, raw['common_optical_source']['background_rates']), Q(0))
    mass = Q(source_record['source_input_positive_mass_upper'])
    return mass*min(Q(1), rate*(stop-start))


class PreparedBFieldRecordMeasure:
    def __init__(self, source, response_source, raw_writer, *, modes=('valid', 'valid'),
                 herald_labels=('Psi+', 'Psi-')):
        _execution()
        _require(type(source) is prepared.PreparedBFieldReceipt and
                 type(raw_writer) is records.writer.RecordWriterSource,
                 'closed prepared B-field mother, reference response and original encoder required')
        response = _response_module()
        _RESPONSE_CHECK()
        _CEM_CHECK()
        _require(type(response_source) is response.ReferenceResponseWindowSource,
                 'closed prepared B-field mother, reference response and original encoder required')
        for value in (source, response_source, raw_writer):
            records._closed(value)
        raw = prepared.PreparedBFieldReceipt.record(source)
        local = raw['reference_local_parent']
        control = response.ReferenceResponseWindowSource.record(response_source)
        _require(control['reference_local_parent'] == local and
                 control['working_atomic_owner'] == local['working_atomic_owner'] and
                 control['reference_clock'] == local['reference_clock'],
                 'receipt and CEM must consume the same original atomic and clock source')
        timing = records.response.PublicResponseTiming.from_record(control['raw_receipt_timing'])
        full_cem = cem.FullZeemanCEMSource(response_source)
        cem_record = cem.FullZeemanCEMSource.record(full_cem)
        raw_window = cem.FullZeemanCEMSource.geometry_source(full_cem)
        _require(raw_window.record() == control['raw_window_source'],
                 'CEM waveform must be the checked reference response source')
        unit = Q(local['working_atomic_owner']['atomic_base']['seconds_per_unit'])
        _require(raw_writer.seconds_per_unit == timing.seconds_per_unit == raw_window.seconds_per_unit == unit,
                 'same source time unit is required for the field, CEM and original encoder')
        records._response_support(raw_window, timing)
        _require(type(modes) is tuple and len(modes) == 2 and all(mode in records.writer.MODES for mode in modes),
                 'two original registered record modes required')
        self._source, self._response, self._writer = source, response_source, raw_writer
        self._cem = full_cem
        self._window, self._timing, self._unit = raw_window, timing, unit
        self._encoding = records.observed.Encoding(tuple(item.click_token for item in raw_writer.encoders),
            tuple(item.setting_zero_token for item in raw_writer.encoders), herald_labels)
        self._model = records.full.nonnegative(cem_record['source_model_trace_norm_error'])
        field = raw['reference_joint_instrument']['reference_field_source']['reference_centre_field_source']
        self._value = {'schema': SCHEMA, 'prepared_mother': raw,
            'reference_response_source': control, 'raw_window_source': raw_window.record(),
            'complete_Zeeman_CEM_source': cem_record,
            'raw_receipt_timing': timing.record(), 'raw_encoder_source': raw_writer.record(),
            'settings': control['settings'], 'modes': list(modes), 'encoding': self._encoding.record(),
            'raw_gate_seconds': field['gate_seconds'],
            'physical_clock_chart': 'native source start; record coordinate = physical seconds / source unit',
            'Ready_epoch_added_to_gate': False, 'response_depends_on_absolute_receipt_time': False,
            'time_restriction_law': 'Phi_window(mu(B)); no ground-state stationarity premise',
            'SI_source_model_trace_norm_error': str(self._model),
            'record_cell_rule': 'one UID ceil, RN age and Unix floor cell for all CEM outcomes',
            'source_scope': 'the original first-gate two-signal subinstrument and its retained complementary mother',
            'source_bindings': _bindings(), 'controller_advance': False}
        self._seal = records.channel._canonical(self._value)

    def record(self):
        _execution()
        records._closed(self)
        response = _response_module()
        _RESPONSE_CHECK()
        _CEM_CHECK()
        _require(type(self) is PreparedBFieldRecordMeasure and set(vars(self)) == {
            '_source', '_response', '_writer', '_window', '_timing', '_unit', '_encoding', '_model', '_cem', '_value', '_seal'} and
            records.channel._canonical(self._value) == self._seal and
            self._value['source_bindings'] == _bindings() and
            prepared.PreparedBFieldReceipt.record(self._source) == self._value['prepared_mother'] and
            response.ReferenceResponseWindowSource.record(self._response) == self._value['reference_response_source'] and
            cem.FullZeemanCEMSource.record(self._cem) == self._value['complete_Zeeman_CEM_source'] and
            self._writer.record() == self._value['raw_encoder_source'] and
            self._window.record() == self._value['raw_window_source'] and
            self._timing.record() == self._value['raw_receipt_timing'] and
            self._encoding.record() == self._value['encoding'] and
            self._unit == self._writer.seconds_per_unit and
            str(self._model) == self._value['SI_source_model_trace_norm_error'],
            'prepared B-field state, raw CEM control, clock or encoder changed')
        return records._copy(self._value)

    def _event(self, first, second, admitted, pair_row, bits, receipt_report=None):
        raw = self.record()
        decoded = records.observed.decode_observation(first, second, admitted, pair_row, self._encoding)
        rows, origin, settings, herald, clicks = decoded
        _require(settings == tuple(raw['settings']), 'observed settings differ from the applied original control')
        restriction = _restriction(rows, self._writer, self._timing, tuple(raw['modes']), raw['raw_gate_seconds'])
        if receipt_report is None:
            signal = prepared.PreparedBFieldReceipt.interval(self._source, *restriction[-1], bits=bits)
        else:
            prepared.PreparedBFieldReceipt.verify(self._source, receipt_report)
            _require(tuple(map(Q, receipt_report['first_receipt_restriction_seconds'])) == restriction[-1] and
                     receipt_report['scalar_bits'] == bits,
                     'checked receipt restriction and precision must equal the original record cell')
            signal = receipt_report
        _require(signal['patterns'] == list(range(4)), 'the original record requires all four source patterns')
        return raw, decoded, restriction, signal

    def generate_trials(self, first, second, admitted, pair_row, *, order=8, mode_bits=60,
                        coefficient_bits=160, exponential_bits=160, receipt_report=None):
        _, _, _, signal = self._event(first, second, admitted, pair_row, coefficient_bits, receipt_report)
        return [cem.FullZeemanCEMSource.generate_trials(self._cem,
                    records.channel._read_input(state, records.joint.DIMENSION), order=order, mode_bits=mode_bits,
                    coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
                for state in signal['four_pattern_poststates']]

    def generate(self, first, second, admitted, pair_row, trial_families, *, mode_bits=60,
                 coefficient_bits=160, exponential_bits=160, receipt_report=None):
        raw, decoded, restriction, signal = self._event(first, second, admitted, pair_row, coefficient_bits, receipt_report)
        rows, origin, settings, herald, clicks = decoded
        selected, cell, faces, reasons, bounds = restriction
        _require(type(trial_families) is list and len(trial_families) == 4,
                 'all four physical patterns require their complete CEM witnesses')
        states = tuple(records.channel._read_input(state, records.joint.DIMENSION)
                       for state in signal['four_pattern_poststates'])
        precision = dict(mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        packets, certificates, local_error = [], [], Q(0)
        for pattern, (matrix, families) in enumerate(zip(states, trial_families)):
            outcomes, error, reports = cem.FullZeemanCEMSource.image(self._cem, matrix, families, precision)
            local_error += error
            certificates.append(reports)
            for outcome, poststate in zip(records.window.REGISTRATION_ORDER, outcomes):
                packets.append({'pattern': pattern, 'herald': records.bsm.PATTERNS[pattern][0],
                    'clicks': list(outcome), 'complete_matrix': records.channel._input_record(poststate)})
        denominator = records._sum(records.channel._read_input(packet['complete_matrix'], records.joint.DIMENSION)
            for packet in packets if packet['herald'] == herald)
        numerator = records._sum(records.channel._read_input(packet['complete_matrix'], records.joint.DIMENSION)
            for packet in packets if packet['herald'] == herald and tuple(packet['clicks']) == clicks)
        empty = selected is None or selected.lower == selected.upper
        background = _background_upper(raw['prepared_mother'], empty)
        model_price = self._model*sum((records.bsm._entry_norm(matrix, bits=coefficient_bits)
                                      for matrix in states), Q(0))
        state_error = Q(signal['whole_trace_norm_error_upper'])+local_error+model_price
        n, nlo, nhi = records._trace_bounds(numerator, state_error, coefficient_bits)
        d, dlo, dhi = records._trace_bounds(denominator, state_error, coefficient_bits)
        nhi += background
        dhi += background
        probability = [str(nlo/dhi if dhi else Q(0)), str(min(Q(1), nhi/dlo) if dlo else Q(1))]
        return {'schema': SCHEMA+'/event', 'source_record': raw, 'original_pair': list(origin),
            'original_rows': [list(row) for row in rows], 'settings': list(settings), 'herald': herald, 'clicks': list(clicks),
            'original_record_cell': records._cell_record(cell), 'selected_first_gate_cell': records._cell_record(selected),
            'encoder_inverse_faces': faces, 'empty_or_unadmitted_reasons': reasons,
            'receipt_restriction_seconds': list(map(str, bounds)), 'empty_restriction_is_zero_instrument': empty,
            'whole_receipt_report': signal, 'sixteen_CEM_packets': packets, 'CEM_step_certificates': certificates,
            'trial_families': records._copy(trial_families), 'precision': precision,
            'CEM_local_error': str(local_error), 'SI_source_model_payment': str(model_price),
            'positive_BG_complement_upper': str(background), 'complete_event_trace_norm_error': str(state_error+background),
            'selected_complete_matrix': records.channel._input_record(numerator),
            'admission_complete_matrix': records.channel._input_record(denominator),
            'selected_mass_centre': str(n), 'admission_mass_centre': str(d),
            'selected_mass_bounds': list(map(str, (nlo, nhi))), 'admission_mass_bounds': list(map(str, (dlo, dhi))),
            'conditional_first_gate_probability_bounds': probability,
            'admission_does_not_read_CEM_outcome': True, 'whole_upstream_error_carried_once': True,
            'complete_native_time_mother': raw['prepared_mother']['whole_reference_native_time_and_PC_mother'],
            'complete_remaining_field_time_mother': signal['complete_reference_field_BG_positive_complement_mother'],
            'source_positive_Ready_normalized': False, 'ground_state_stationarity_assumed': False,
            'full_nextRaw_history_scored': False, 'actual_original_run_admission_certified': False,
            'actual_hardware_uniquely_identified': False, 'new_confidence_budget_spent': False, 'controller_advance': False}

    def verify(self, report, first, second, admitted):
        _require(type(report) is dict and report.get('schema') == SCHEMA+'/event' and
                 report.get('source_record') == self.record(), 'same closed B-field original record source required')
        expected = PreparedBFieldRecordMeasure.generate(self, first, second, admitted, report['original_pair'][1],
            report['trial_families'], receipt_report=report['whole_receipt_report'], **report['precision'])
        _require(expected == report, 'original time cell, CEM matrix, admission or source price changed')
        return True


def _signature():
    functions = (_require, _response_module, _bindings, _restriction, _background_upper,
        _signature, _guard, _execution, prepared.PreparedBFieldReceipt.record, prepared.PreparedBFieldReceipt.interval,
        prepared.PreparedBFieldReceipt.verify,
        _RESPONSE_CHECK, response.ReferenceResponseWindowSource.record,
        response.ReferenceResponseWindowSource.window_source,
        _CEM_CHECK, cem.FullZeemanCEMSource.record, cem.FullZeemanCEMSource.geometry_source,
        cem.FullZeemanCEMSource.generate_trials, cem.FullZeemanCEMSource.image,
        records._guard,
        records._record_cell, records._window_image, records._window_trials, records._trace_bounds,
        records._response_support, records._sum, records.observed.decode_observation,
        records.clock.uid_interval, records.clock.unix_interval, records.clock.intersect)
    functions += tuple(member for member in vars(PreparedBFieldRecordMeasure).values() if callable(member))
    return tuple((id(function), id(function.__code__)) for function in functions)


def _guard():
    if _signature is not _SIGNATURE or _signature.__code__ is not _SIGNATURE_CODE or _signature() != _EXPECTED:
        raise ValueError('prepared B-field record source execution changed')
    records._guard()


def _execution():
    if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
        raise ValueError('prepared B-field record source execution changed')
    _GUARD()


_SIGNATURE = _signature
_SIGNATURE_CODE = _signature.__code__
_GUARD = _guard
_GUARD_CODE = _guard.__code__
_EXPECTED = _signature()
