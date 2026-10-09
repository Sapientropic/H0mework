"""Prepared photon time measure -> the original local record event.

The zero-background signal instrument is stationary in the common ground
frame.  Its complete matrix can therefore enter the receipt-relative raw
CEM waveform.  The positive background field packet and the original
native/field time mothers stay in the source; they are not replaced by a
gate-end atomic snapshot or a caller-supplied probability table.
"""
from fractions import Fraction as Q
from dataclasses import replace
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import aperture_collection_domain as aperture
import bsm_retry_source as bsm
import conditioned_window_history as observed
import fluorescence_channel as channel
import history_feed as history
import joint_fluorescence_presence as joint
import munich_atomic_programme as atomic
import prepared_retarded_source as prepared
import receipt_triggered_programme as response
import record_programme_source as writer
import retarded_receipt_source as receipt
import window_cem_source as window
import writer_domain as clock


SCHEMA = 'stage10-prepared-first-gate-original-record-measure/v1'
ZERO = dipole.ComplexRadical()


def _require(value, message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _bindings(*, objective=False):
    modules = (dipole, full, bsm, observed, channel, history, joint, atomic,
               prepared, response, writer, receipt, window, clock)
    if objective:
        modules += (aperture,)
    paths = (Path(__file__), *(Path(module.__file__) for module in modules))
    return {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def _closed(value):
    for cls in type(value).__mro__:
        for name, method in vars(cls).items():
            if callable(method) or isinstance(method, (classmethod, staticmethod, property)):
                _require(name not in vars(value), 'source operations cannot be instance callbacks')


def _sum(matrices):
    result = {}
    for matrix in matrices:
        for key, value in matrix.items():
            window.local._add(result, key, value)
    return result


def _trace_bounds(matrix, error, bits):
    trace = joint._trace(matrix)
    _require(not trace.imag, 'complete Hermitian event trace required')
    centre, rounding = full.radical_midpoint(trace.real, bits)
    radius = full.nonnegative(error) + rounding
    return centre, max(Q(0), centre-radius), max(Q(0), centre+radius)


def _cell_record(cell):
    return clock._interval_record(cell)


def _shift(cell, delta):
    return None if cell is None else clock.Interval(cell.lower+delta, cell.upper+delta,
                                                   cell.lower_closed, cell.upper_closed)


def _record_cell(rows, encoders, raw_writer, events, modes):
    cells, reasons, faces = [], [], []
    for side, (row, encoder, event, mode) in enumerate(zip(rows, encoders, events, modes)):
        uid = history.schema.integer(row[4], 'local_timestamp')
        unix = history.schema.timestamp(row[1], 'Unix-time')
        sample = clock.uid_interval(encoder, uid)
        strobe = None if sample is None else sample.upper+encoder.request_latency
        age = None if strobe is None else clock.Interval(
            strobe-event['RN_output'], strobe-event['earliest_RN_correlation'], True, True)
        inverse = (_shift(sample, -event['RN_request']), age,
                   clock.unix_interval(raw_writer, side, unix, event['CEM_logic_deadline']))
        faces.append({'side': side, 'UID_ceil_inverse': _cell_record(inverse[0]),
                      'RN_age_inverse': _cell_record(age), 'Unix_floor_inverse': _cell_record(inverse[2])})
        if mode != 'valid' or tuple(row[6:8]) != writer.MODES[mode]:
            reasons.append('source mode or original flag/comment is outside admission')
        if any(cell is None for cell in inverse):
            reasons.append('original time token has no inverse in this encoder')
        cells.extend(inverse)
    if abs(history.schema.timestamp(rows[0][1], 'Unix-time')-
           history.schema.timestamp(rows[1][1], 'Unix-time')) > 100:
        reasons.append('original two-side Unix cell exceeds 100ms pairing')
    return (None if reasons else clock.intersect(tuple(cells))), faces, reasons


def _fresh_signal_state(matrix):
    _require(all(all(dipole.STATES[index].family == 'ground' for index in divmod(address, 33))
                 for key in matrix for address in key),
             'two source signal photons must generate complete neutral ground output')
    return {(window.INITIAL, i, j): value for (i, j), value in matrix.items()}


def _window_trials(source, initial, order, mode_bits, coefficient_bits, exponential_bits):
    """Untrusted producer; every returned curve is checked by the caller."""
    _require(type(order) is int and 0 <= order <= 64, 'finite raw CEM source jet order required')
    matrix = _fresh_signal_state(initial)
    quantum, families = 1 << mode_bits, []
    for phase in source.phases():
        kernel = window.SourceKernel(phase, coefficient_bits)
        coefficients = {(window.mark_index(mark), i, j): tuple(full.radical_midpoint(part, coefficient_bits)[0]
                        for part in (value.real, value.imag)) for (mark, i, j), value in matrix.items()}
        polynomial = []
        for degree in range(order+1):
            encoded = [[c, i, j, round(a*quantum), round(b*quantum)]
                       for (c, i, j), (a, b) in sorted(coefficients.items())
                       if round(a*quantum) or round(b*quantum)]
            polynomial.append(encoded)
            quantized = {(c, i, j): (Q(a, quantum), Q(b, quantum)) for c, i, j, a, b in encoded}
            coefficients = {key: (a*phase.duration/(degree+1), b*phase.duration/(degree+1))
                            for key, (a, b) in kernel.action(quantized).items()}
        pieces = [{'duration': str(phase.duration),
                   'modes': [{'lambda': [0, 0], 'coefficients': polynomial}]}]
        report = window.certify_step(phase, matrix, pieces, mode_bits=mode_bits,
                                    coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        matrix, _ = window.marked_poststate(report)
        families.append(pieces)
    return families


def _window_image(source, initial, families, precision):
    _require(type(families) is list and len(families) == len(source.partition),
             'every raw waveform and fragment-window phase needs its complete witness')
    matrix = _fresh_signal_state(initial)
    price, reports = Q(0), []
    for phase, pieces in zip(source.phases(), families):
        report = window.certify_step(phase, matrix, pieces, upstream_error=price, **precision)
        matrix, price = window.marked_poststate(report)
        reports.append(report)
    final = source.background_action(matrix)
    blocks = window._blocks(final)
    return tuple(blocks.get(window.Mark(clicks), {}) for clicks in window.REGISTRATION_ORDER), price, reports


def _response_support(source, timing):
    events, unit = timing.events(), timing.seconds_per_unit
    _require(source.duration == max(event['CEM_logic_deadline'] for event in events),
             'full raw waveform must end at the common original CEM cutoff')
    for side, (waveform, registration, event) in enumerate(zip(source.waveforms, source.registrations, events)):
        elapsed = Q(0)
        for segment in waveform:
            end = elapsed+segment.duration
            light = (any(segment.r*value for value in segment.fields_r.values()) or
                     any(segment.c*value for value in segment.fields_c.values()))
            birth = any(segment.ion_rates.values())
            _require(not (light or birth) or elapsed >= event['readout_reaches_atom'],
                     'setting-dependent field or ion birth precedes the original AOM onset')
            _require(not birth or end <= event['ion_acceptance_window_closes'],
                     'ion birth extends beyond the original acceptance cutoff')
            _require(not light or end <= event['CEM_logic_deadline'],
                     'raw readout field extends beyond its original CEM cutoff')
            elapsed = end
        _require(registration.electron_window[1]-registration.electron_window[0] ==
                    (240 if side == 0 else 160)*response.NS/unit and
                 registration.ion_window[1]-registration.ion_window[0] ==
                    (240 if side == 0 else 220)*response.NS/unit and
                 registration.ion_window[1] == event['ion_acceptance_window_closes'],
                 'raw fragment windows differ from the published side lengths or ion cutoff')


def _paid_window_at_receipt(owner, timing, settings):
    old, model = owner.si_window_source(settings)
    events, base = timing.events(), owner.atomic_base()
    _require(old.seconds_per_unit == timing.seconds_per_unit,
             'paid SI and public response must use the same source time unit')
    terminal = max(event['CEM_logic_deadline'] for event in events)
    waveforms, registrations = [], []
    for side, (waveform, registration, event) in enumerate(zip(old.waveforms, old.registrations, events)):
        onset = event['readout_reaches_atom']
        _require(event['CEM_logic_deadline']-onset == old.logic_deadlines[side] and
                 event['ion_acceptance_window_closes']-onset == registration.ion_window[1],
                 'paid fragment cutoff differs from the receipt-relative public timing point')
        rows = [base.segment(side, onset)]
        remaining = old.logic_deadlines[side]
        for segment in waveform:
            if remaining <= 0:
                break
            width = min(remaining, segment.duration)
            rows.append(replace(segment, duration=width))
            remaining -= width
        _require(remaining == 0, 'original paid waveform does not cover its local CEM cutoff')
        if event['CEM_logic_deadline'] < terminal:
            rows.append(base.segment(side, terminal-event['CEM_logic_deadline']))
        waveforms.append(tuple(rows))
        registrations.append(replace(registration,
            electron_window=tuple(onset+t for t in registration.electron_window),
            ion_window=tuple(onset+t for t in registration.ion_window)))
    shifted = window.WindowCEMSource(*waveforms, registrations=tuple(registrations),
        backgrounds=old.backgrounds, logic_deadlines=tuple(event['CEM_logic_deadline'] for event in events),
        seconds_per_unit=old.seconds_per_unit)
    extra_zeeman = 2*max(Q(0), shifted.duration-old.duration)*sum(
        (atomic._operator_upper(base.off_diagonal_zeeman(side), 160) for side in (0, 1)), Q(0))
    return shifted, {**model,
        'source_model_trace_norm_error': str(Q(model['source_model_trace_norm_error'])+extra_zeeman),
        'receipt_relative_extra_Zeeman_price': str(extra_zeeman),
        'original_ionization_relative_window': old.record(),
        'receipt_relative_window': shifted.record(),
        'time_transport': 'same local pulse and cutoff shifted by its raw AOM onset; full bath before and after',
        'fragment_flight_not_shifted': True}


class PreparedRecordMeasure:
    def __init__(self, source, raw_window, timing, raw_writer, *, settings, modes=('valid', 'valid'),
                 herald_labels=('Psi+', 'Psi-'), objective_domain=None):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('prepared record source execution changed')
        _guard()
        _require(type(source) is prepared.PreparedRetardedSource and type(raw_window) is window.WindowCEMSource and
                 type(timing) is response.PublicResponseTiming and type(raw_writer) is writer.RecordWriterSource,
                 'closed prepared photon mother, raw CEM waveform, timing and encoder required')
        for value in (source, raw_window, timing, raw_writer):
            _closed(value)
        raw = source.record()
        recipe = raw['native_ready_relative_time_recipe']
        _require(raw['native_inlet_kind'] in ('first PC-ready at the original first poll',
                 'exact native-frame Ready at the original first poll'),
                 'this record source consumes the original finite first-poll Ready event')
        owner = atomic.MunichAtomicProgramme.from_record(raw['common_atomic_programme'])
        base = atomic.MunichAtomicProgramme.atomic_base(owner)
        unit = Q(base.record()['seconds_per_unit'])
        _require(raw_window.seconds_per_unit == timing.seconds_per_unit == raw_writer.seconds_per_unit == unit and
                 raw_window.interval_start == 0 and
                 raw_window.logic_deadlines == tuple(event['CEM_logic_deadline'] for event in timing.events()),
                 'same physical source unit and receipt-relative CEM deadlines required')
        _response_support(raw_window, timing)
        _require(type(settings) is tuple and len(settings) == 2 and all(type(v) is int and v in (0, 1) for v in settings),
                 'two original applied setting addresses required')
        _require(type(modes) is tuple and len(modes) == 2 and all(mode in writer.MODES for mode in modes),
                 'two registered PC record modes required')
        for side, waveform in enumerate(raw_window.waveforms):
            for segment in waveform:
                quiet = base.segment(side, segment.duration)
                _require(segment.gammas == quiet.gammas and segment.detunings == quiet.detunings and
                         segment.radiation_regime == quiet.radiation_regime and
                         segment.field_convention == quiet.field_convention,
                         'receipt and CEM must have one complete natural bath and hyperfine source')
        model = None
        if owner.record()['paid_si_leaf'] is not None:
            expected, model = _paid_window_at_receipt(owner, timing, settings)
            _require(expected.record() == raw_window.record(), 'original shared paid SI command source required')
        common = receipt.RetardedReceiptSource.from_record(raw['full_retarded_receipt_time_mother'])
        reference = common.signal_reference_law()
        _require(reference['signal_poststate_commutes_with_common_ground_Hamiltonian'],
                 'receipt-relative signal state needs its source ground-frame identity')
        admission = None
        if objective_domain is not None:
            _require(type(objective_domain) is aperture.ApertureCollectionDomain,
                     'closed objective domain required; an optical budget is not a caller scalar')
            _closed(objective_domain)
            admission = aperture.ApertureCollectionDomain.admit_prepared(objective_domain, source)
        self._objective = objective_domain
        self._source, self._window, self._timing, self._writer = source, raw_window, timing, raw_writer
        self._encoding = observed.Encoding(tuple(item.click_token for item in raw_writer.encoders),
            tuple(item.setting_zero_token for item in raw_writer.encoders), herald_labels)
        self._unit = unit
        self._epoch = Q(recipe['first_poll_geometry']['poll'])
        self._model = Q(0) if model is None else Q(model['source_model_trace_norm_error'])
        self._record = {'schema': SCHEMA, 'prepared_mother': raw, 'raw_window_source': raw_window.record(),
            'raw_receipt_timing': timing.record(), 'raw_encoder_source': raw_writer.record(),
            'settings': list(settings), 'modes': list(modes), 'encoding': self._encoding.record(),
            'native_confirmation_source_clock': str(self._epoch), 'signal_reference_law': reference,
            'SI_source_model_price': str(self._model), 'SI_source_model_certificate': model,
            'record_cell_rule': 'same UID ceil, RN age and Unix floor cell for every CEM outcome',
            'source_scope': 'finite first-poll, first-gate event with the complete positive continuation retained',
            'native_time_mother': raw['native_time_state_mother'],
            'complete_field_time_mother': raw['full_retarded_receipt_time_mother'],
            'objective_collection_admission': admission,
            'parameter_domain': raw['parameter_domain'] if admission is None else admission['parameter_domain'],
            'source_bindings': _bindings(objective=objective_domain is not None), 'controller_advance': False}
        self._seal = channel._canonical(self._record)

    @classmethod
    def from_paid_si(cls, source, timing, raw_writer, *, settings, modes=('valid', 'valid'),
                     herald_labels=('Psi+', 'Psi-'), objective_domain=None):
        _require(type(source) is prepared.PreparedRetardedSource, 'closed prepared source required')
        owner = atomic.MunichAtomicProgramme.from_record(source.record()['common_atomic_programme'])
        raw_window, _ = _paid_window_at_receipt(owner, timing, settings)
        return cls(source, raw_window, timing, raw_writer, settings=settings, modes=modes,
                   herald_labels=herald_labels, objective_domain=objective_domain)

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('prepared record source execution changed')
        _guard()
        _closed(self)
        _require(type(self) is PreparedRecordMeasure and
                 set(vars(self)) == {'_source', '_window', '_timing', '_writer', '_encoding', '_unit',
                                    '_epoch', '_model', '_objective', '_record', '_seal'} and
                 self._seal == channel._canonical(self._record) and
                 self._record['source_bindings'] == _bindings(objective=self._objective is not None) and
                 self._encoding.record() == self._record['encoding'] and
                 self._unit == self._writer.seconds_per_unit and
                 str(self._epoch) == self._record['native_confirmation_source_clock'] and
                 str(self._model) == self._record['SI_source_model_price'] and
                 self._source.record() == self._record['prepared_mother'] and
                 self._window.record() == self._record['raw_window_source'] and
                 self._timing.record() == self._record['raw_receipt_timing'] and
                 self._writer.record() == self._record['raw_encoder_source'],
                 'prepared field, waveform, original encoder or source snapshot changed')
        admission = self._record['objective_collection_admission']
        if self._objective is None:
            _require(admission is None and self._record['parameter_domain'] == self._source.record()['parameter_domain'],
                     'original prepared parameter domain changed')
        else:
            _require(type(self._objective) is aperture.ApertureCollectionDomain and
                     aperture.ApertureCollectionDomain.record(self._objective) == admission['objective_collection_domain'] and
                     self._record['parameter_domain'] == admission['parameter_domain'],
                     'same objective source domain must persist through the original record event')
        return _copy(self._record)

    def _interval(self, bounds, bits):
        if self._objective is None:
            return prepared.PreparedRetardedSource.interval(self._source, *bounds, bits=bits)
        return aperture.ApertureCollectionDomain.prepared_interval(self._objective, self._source, *bounds, bits=bits)

    def _restriction(self, rows):
        cell, faces, reasons = _record_cell(rows, self._writer.encoders, self._writer,
            self._timing.events(), tuple(self._record['modes']))
        raw = self._record['prepared_mother']['field_kernel']
        gate = clock.Interval(*(self._epoch+Q(t)/self._unit for t in raw['raw_gate_seconds']), False, True)
        selected = None if cell is None else clock.intersect((cell, gate))
        return selected, cell, faces, reasons

    def generate_trials(self, first, second, admitted, pair_row, *, order=8, mode_bits=60,
                        coefficient_bits=160, exponential_bits=160):
        self.record()
        rows, _, settings, _, _ = observed.decode_observation(first, second, admitted, pair_row, self._encoding)
        _require(settings == tuple(self._record['settings']), 'observed settings differ from the applied source')
        selected, _, _, _ = self._restriction(rows)
        gate = tuple(map(Q, self._record['prepared_mother']['field_kernel']['raw_gate_seconds']))
        bounds = (gate[0], gate[0]) if selected is None else tuple((t-self._epoch)*self._unit for t in (selected.lower, selected.upper))
        signal = PreparedRecordMeasure._interval(self, bounds, coefficient_bits)
        return [_window_trials(self._window, channel._read_input(state, joint.DIMENSION), order,
                    mode_bits, coefficient_bits, exponential_bits) for state in signal['four_pattern_poststates']]

    def generate(self, first, second, admitted, pair_row, trial_families, *, mode_bits=60,
                 coefficient_bits=160, exponential_bits=160):
        source_record = self.record()
        rows, origin, settings, herald, clicks = observed.decode_observation(
            first, second, admitted, pair_row, self._encoding)
        _require(settings == tuple(source_record['settings']), 'observed settings differ from the applied source')
        selected, whole_cell, faces, reasons = self._restriction(rows)
        gate = tuple(map(Q, source_record['prepared_mother']['field_kernel']['raw_gate_seconds']))
        bounds = (gate[0], gate[0]) if selected is None else tuple((t-self._epoch)*self._unit for t in (selected.lower, selected.upper))
        signal = PreparedRecordMeasure._interval(self, bounds, coefficient_bits)
        _require(type(trial_families) is list and len(trial_families) == 4,
                 'all four original signal patterns need their complete CEM witness')
        states = tuple(channel._read_input(state, joint.DIMENSION) for state in signal['four_pattern_poststates'])
        precision = dict(mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        packets, certificates, local_error = [], [], Q(0)
        for pattern, (matrix, families) in enumerate(zip(states, trial_families)):
            outcomes, price, reports = _window_image(self._window, matrix, families, precision)
            local_error += price
            certificates.append(reports)
            for outcome, state in zip(window.REGISTRATION_ORDER, outcomes):
                packets.append({'pattern': pattern, 'herald': bsm.PATTERNS[pattern][0], 'clicks': list(outcome),
                                'complete_matrix': channel._input_record(state)})
        denominator = _sum(channel._read_input(packet['complete_matrix'], joint.DIMENSION) for packet in packets
                           if packet['herald'] == herald)
        numerator = _sum(channel._read_input(packet['complete_matrix'], joint.DIMENSION) for packet in packets
                         if packet['herald'] == herald and tuple(packet['clicks']) == clicks)
        empty = selected is None or selected.lower == selected.upper
        background = Q(0) if empty else Q(signal['source_positive_BG_receipt_remainder_mass_upper'])
        finite_price = Q(0) if empty else Q(signal['global_trace_norm_error'])-background
        model_price = self._model*sum((bsm._entry_norm(matrix, bits=coefficient_bits) for matrix in states), Q(0))
        state_price = finite_price+local_error+model_price
        n, nlo, nhi = _trace_bounds(numerator, state_price, coefficient_bits)
        d, dlo, dhi = _trace_bounds(denominator, state_price, coefficient_bits)
        # The source's BG packet is positive, so it affects the upper mass
        # and the posterior radius, but never subtracts from a mass lower.
        nhi += background
        dhi += background
        probability = [str(nlo/dhi if dhi > 0 else Q(0)), str(min(Q(1), nhi/dlo) if dlo > 0 else Q(1))]
        return {'schema': SCHEMA+'/event', 'source_record': source_record, 'original_pair': list(origin),
            'original_rows': [list(row) for row in rows], 'settings': list(settings),
            'herald': herald, 'clicks': list(clicks), 'original_record_cell': _cell_record(whole_cell),
            'selected_first_gate_cell': _cell_record(selected), 'encoder_inverse_faces': faces,
            'empty_or_unadmitted_reasons': reasons, 'receipt_restriction_seconds': list(map(str, bounds)),
            'empty_restriction_is_zero_instrument': empty,
            'whole_receipt_report': signal, 'sixteen_CEM_packets': packets, 'CEM_step_certificates': certificates,
            'parameter_domain': _copy(signal['parameter_domain']),
            'trial_families': _copy(trial_families), 'precision': precision,
            'CEM_local_error': str(local_error), 'SI_source_model_payment': str(model_price),
            'complete_event_trace_norm_error': str(state_price+background),
            'positive_BG_packet_upper': str(background), 'selected_complete_matrix': channel._input_record(numerator),
            'admission_complete_matrix': channel._input_record(denominator),
            'selected_mass_centre': str(n), 'admission_mass_centre': str(d),
            'selected_mass_bounds': list(map(str, (nlo, nhi))), 'admission_mass_bounds': list(map(str, (dlo, dhi))),
            'conditional_first_gate_probability_bounds': probability,
            'admission_does_not_read_CEM_outcome': True, 'source_error_carried_once': True,
            'complete_native_time_mother': source_record['native_time_mother'],
            'complete_remaining_field_time_mother': source_record['complete_field_time_mother'],
            'continuation_is_not_replaced_by_normalized_first_gate_atom_state': True,
            'full_nextRaw_history_scored': False, 'new_confidence_budget_spent': False,
            'actual_original_run_admission_certified': False, 'actual_hardware_uniquely_identified': False,
            'controller_advance': False}

    def verify(self, report, first, second, admitted):
        _require(type(report) is dict and report.get('schema') == SCHEMA+'/event' and
                 report.get('source_record') == self.record(), 'same prepared physical record event required')
        expected = self.generate(first, second, admitted, report['original_pair'][1],
                                report['trial_families'], **report['precision'])
        _require(expected == report, 'original rows, physical time cell, complete CEM state or source price changed')
        return True


def _signature():
    functions = (_require, _copy, _bindings, _closed, _sum, _trace_bounds, _cell_record, _shift,
        _record_cell, _fresh_signal_state, _window_trials, _window_image, _signature, _guard,
        _paid_window_at_receipt, _response_support,
        PreparedRecordMeasure.__init__, PreparedRecordMeasure.from_paid_si.__func__,
        PreparedRecordMeasure.record, PreparedRecordMeasure._restriction, PreparedRecordMeasure.generate_trials,
        PreparedRecordMeasure._interval,
        PreparedRecordMeasure.generate, PreparedRecordMeasure.verify,
        window.certify_step, window._checked_step, window.marked_poststate, window._blocks,
        window.WindowCEMSource.background_action, window.WindowCEMPhase.action, channel._piece,
        observed.decode_observation, clock.uid_interval, clock.unix_interval, clock.intersect,
        aperture.ApertureCollectionDomain.record, aperture.ApertureCollectionDomain.admit_prepared,
        aperture.ApertureCollectionDomain.prepared_interval)
    return tuple((id(f), id(f.__code__)) for f in functions)


def _guard():
    if _signature is not _SIGNATURE or _signature.__code__ is not _SIGNATURE_CODE or _signature() != _EXPECTED:
        raise ValueError('prepared record source execution changed')


_SIGNATURE = _signature
_SIGNATURE_CODE = _signature.__code__
_GUARD = _guard
_GUARD_CODE = _guard.__code__
_EXPECTED = _signature()
