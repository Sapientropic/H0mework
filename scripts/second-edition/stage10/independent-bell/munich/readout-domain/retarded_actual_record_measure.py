"""Actual-time joint receipt matrices enter the original sixteen CEM packets.

Receipt-relative full-Z CEM is the same channel for every time in the
original UID/RN/Unix cell.  The complete time-measure error is transported
once; local CEM certificates and source model differences are paid on the
four-pattern direct sum before either admission or outcome is selected.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import retarded_actual_time_measure as actual
import prepared_b_field_record_measure as original
import aperture_collection_domain as positive
import full_zeeman_cem_local_flow as local_cem

records, response, cem = original.records, original.response, original.cem
field, full, channel, joint, bsm = actual.field, actual.full, actual.channel, actual.joint, actual.bsm
gaussian = actual.continuous.gaussian
SCHEMA = 'stage10-source-retarded-actual-time-original-record-measure/v1'
_ACTUAL_CHECK, _RESPONSE_CHECK, _CEM_CHECK = actual._CHECK, response._CHECK, cem._CHECK
_LOCAL_CEM_CHECK = local_cem._CHECK
_ORIGINAL_EXECUTION = original._execution
_ISSUED = {}


def _require(value, message):
    if not value:
        raise ValueError(message)


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), *(Path(m.__file__) for m in
            (actual, original, records, response, cem, positive, local_cem, local_cem.reduction)))}


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _cem_backend(value):
    _require(type(value) is str and value in ('marked', 'local_terminal'),
             'named original full-Z CEM calculation backend required')
    return value


def _cem_columns(backend, value):
    _require(type(value) is str and value in ('rational', 'integer') and
             (backend == 'local_terminal' or value == 'rational'),
             'named local CEM columns require the original local-terminal backend')
    return value


def _field_record(source):
    return source._measure._certificate._source._value['retarded_source']['complete_driven_field_source']


def _positive_input(source):
    curve = source._measure._report
    if curve['source_issued_input_used']:
        return {'certified': True, 'scope': 'source-issued positive complete inlet',
                'numerical_endpoint_PSD_assumed': False}
    parent = source._measure._certificate._source
    initial = actual.continuous._read_state(curve['untrusted_trial']['complete_initial_marked_state'], parent)
    blocks = actual.continuous.trajectory.RetardedGaussianTrajectorySource._blocks(parent, initial)
    proofs = []
    for mark, matrix in blocks.items():
        axes = sorted({i for key in matrix for i in key})
        try:
            if all(i == j for i, j in matrix):
                for value in matrix.values():
                    _require(not value.imag and positive.photons.radical_sign(value.real) >= 0,
                             'signed numerical source input')
                pivots = [matrix.get((i, i), actual.timed.dipole.ComplexRadical()).serialize() for i in axes]
            elif len(axes) <= 64:
                pivots = positive._psd([[matrix.get((i, j), actual.timed.dipole.ComplexRadical())
                                        for j in axes] for i in axes])
            else:
                return {'certified': False, 'scope': 'generic signed Hermitian linear input',
                        'positive_source_input_required_for_probability': True}
        except ValueError:
            return {'certified': False, 'scope': 'generic signed Hermitian linear input',
                    'positive_source_input_required_for_probability': True}
        proofs.append({'source_Mark_counts': list(mark.counts), 'source_Mark_receipt': mark.receipt,
                       'complete_nonzero_quantum_axes': axes, 'exact_PSD_pivots': pivots})
    return {'certified': True, 'scope': 'exact positive numerical-control input',
            'original_complete_input_PSD_proof': proofs, 'unknown_error_ball_assumed_positive': False,
            'actual_hardware_membership_inferred': False}


def _continuing_tail(source, lower, bits):
    raw = _field_record(source); clock = raw['reference_clock']
    gamma = Q(clock['Gamma_numerical_centre'])
    high = Q(clock['angular_Gamma_enclosure_per_second'][1])
    multiplier = max(gamma, high) / gamma
    rows = []; price = Q(0)
    for side, (pulse, origin) in enumerate(zip(source._measure._certificate._source._law._field._pulses,
                                               map(Q, raw['emission_origins_seconds']))):
        after = max(Q(0), lower - origin)
        paid = gaussian.GaussianAtomicPulseSource.field_off_tail_price(pulse, after, bits=bits)
        value = multiplier * Q(paid['density_CP_Duhamel_price_per_input_norm_upper'])
        price += value
        rows.append({'side': side, 'actual_clock_after_emission_origin_seconds': str(after),
            'original_source_tail_price': paid, 'reference_Gamma_hi_over_centre': str(multiplier),
            'density_difference_upper': str(field._price_upper(value, bits))})
    return min(Q(2), price), rows


class RetardedActualRecordMeasure:
    def __init__(self, source, control, raw_writer, *, modes=('valid', 'valid'),
                 herald_labels=('Psi+', 'Psi-')):
        _CHECK()
        _require(type(source) is actual.RetardedActualTimeMeasure and
            type(control) is response.ReferenceResponseWindowSource and
            type(raw_writer) is records.writer.RecordWriterSource,
            'closed actual-time measure, same source CEM control and original writer required')
        for item in (source, control, raw_writer):
            records._closed(item)
        raw = actual.RetardedActualTimeMeasure.record(source)
        photon = _field_record(source)
        local = photon['Gaussian_source_legs'][0]['reference_local_parent']
        _require(all(leg['reference_local_parent'] == local for leg in photon['Gaussian_source_legs']),
                 'both photon legs consume the same original reference parent')
        window = response.ReferenceResponseWindowSource.record(control)
        _require(window['reference_local_parent'] == local and
            window['working_atomic_owner'] == local['working_atomic_owner'] and
            window['reference_clock'] == local['reference_clock'],
            'receipt, delayed atoms, CEM and physical clock must have the same source parent')
        timing = records.response.PublicResponseTiming.from_record(window['raw_receipt_timing'])
        full_cem = cem.FullZeemanCEMSource(control)
        cem_raw = cem.FullZeemanCEMSource.record(full_cem)
        geometry = cem.FullZeemanCEMSource.geometry_source(full_cem)
        unit = Q(local['working_atomic_owner']['atomic_base']['seconds_per_unit'])
        _require(raw_writer.seconds_per_unit == timing.seconds_per_unit == geometry.seconds_per_unit == unit,
                 'source actual-time atoms and original encoder use the same physical unit')
        _require(geometry.record() == window['raw_window_source'], 'the CEM geometry is the original checked waveform')
        records._response_support(geometry, timing)
        _require(type(modes) is tuple and len(modes) == 2 and all(value in records.writer.MODES for value in modes),
                 'two original registered record modes required')
        self._source, self._control, self._writer = source, control, raw_writer
        self._cem, self._geometry, self._timing, self._unit = full_cem, geometry, timing, unit
        self._encoding = records.observed.Encoding(tuple(v.click_token for v in raw_writer.encoders),
            tuple(v.setting_zero_token for v in raw_writer.encoders), herald_labels)
        self._model = Q(cem_raw['source_model_trace_norm_error'])
        self._positive = _positive_input(source)
        self._value = {'schema': SCHEMA, 'complete_actual_time_measure': raw,
            'reference_response_source': window, 'complete_Zeeman_CEM_source': cem_raw,
            'raw_window_source': geometry.record(), 'raw_receipt_timing': timing.record(),
            'raw_encoder_source': raw_writer.record(), 'modes': list(modes), 'settings': window['settings'],
            'encoding': self._encoding.record(), 'raw_gate_seconds': photon['gate_seconds'],
            'certified_source_interval_seconds': source._measure._report['source_detector_interval_seconds'],
            'source_receipt_CEM_model_price_per_input_norm': str(self._model),
            'positive_source_input': self._positive,
            'physical_record_coordinate': 'detector seconds/source unit; Ready epoch is already included',
            'Ready_epoch_added_twice': False, 'reference_CEM_channel_depends_on_absolute_receipt_time': False,
            'continuing_Gaussian_tau_dependence_priced': True,
            'CEM_rule': 'full-Z SI channel with the same ongoing Gaussian source enclosed by its source tail',
            'Gaussian_duration_used_as_physical_turnoff': False,
            'CEM_BG_applied_once': True, 'uncomputed_source_time_face_used_as_normalizer': False,
            'all_other_field_and_queue_mother_retained': True,
            'source_bindings': _bindings(), 'controller_advance': False}
        self._seal = _digest(self._value)
        _ISSUED[id(self)] = self._seal, source, control, raw_writer

    def record(self):
        _CHECK(); records._closed(self)
        _require(type(self) is RetardedActualRecordMeasure and set(vars(self)) ==
            {'_source', '_control', '_writer', '_cem', '_geometry', '_timing', '_unit', '_encoding', '_model', '_positive', '_value', '_seal'} and
            _ISSUED.get(id(self)) == (self._seal, self._source, self._control, self._writer) and
            _digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
            actual.RetardedActualTimeMeasure.record(self._source) == self._value['complete_actual_time_measure'] and
            response.ReferenceResponseWindowSource.record(self._control) == self._value['reference_response_source'] and
            cem.FullZeemanCEMSource.record(self._cem) == self._value['complete_Zeeman_CEM_source'] and
            self._geometry.record() == self._value['raw_window_source'] and
            self._timing.record() == self._value['raw_receipt_timing'] and
            self._writer.record() == self._value['raw_encoder_source'] and
            self._encoding.record() == self._value['encoding'] and
            self._unit == self._writer.seconds_per_unit and str(self._model) == self._value['source_receipt_CEM_model_price_per_input_norm'] and
            self._positive == self._value['positive_source_input'],
            'actual source time measure, complete CEM, clock or original encoder changed')
        return records._copy(self._value)

    def _coordinates(self, first, second, admitted, pair_row):
        raw = RetardedActualRecordMeasure.record(self)
        decoded = records.observed.decode_observation(first, second, admitted, pair_row, self._encoding)
        rows, _, settings, _, _ = decoded
        _require(settings == tuple(raw['settings']), 'observed settings differ from applied source CEM controls')
        selected, cell, faces, reasons, bounds = original._restriction(
            rows, self._writer, self._timing, tuple(raw['modes']), raw['raw_gate_seconds'])
        if selected is not None:
            a, b = map(Q, raw['certified_source_interval_seconds'])
            _require(a <= bounds[0] <= bounds[1] <= b,
                     'the complete original record cell needs a source curve covering all of its times')
        return raw, decoded, (selected, cell, faces, reasons, bounds)

    def _receipt(self, bounds, selected, report):
        _require(report is not None, 'a checked same-cell actual-time image is required')
        verified = actual.RetardedActualTimeMeasure.verify(self._source, report)
        trial = verified['untrusted_trial']
        _require(tuple(map(Q, trial['physical_receipt_interval_seconds'])) == bounds and
            trial['Stieltjes_left_closed'] is selected.lower_closed and
            trial['Stieltjes_right_closed'] is selected.upper_closed,
            'actual-time measure must consume the literal original UID/RN/Unix cell')
        return verified

    def generate_trials(self, first, second, admitted, pair_row, *, actual_report=None,
                        reference=None, delay_slices=16, delay_order=8, delay_mode_bits=128,
                        order=8, mode_bits=96, coefficient_bits=192, exponential_bits=192, envelope_order=10,
                        delay_representation='polynomial',delay_krylov_dimension=48,
                        cem_backend='marked', cem_krylov_dimension=1089, cem_column_backend='rational'):
        backend = _cem_backend(cem_backend)
        columns = _cem_columns(backend, cem_column_backend)
        raw, decoded, restriction = RetardedActualRecordMeasure._coordinates(self, first, second, admitted, pair_row)
        selected, _, _, _, bounds = restriction
        if selected is None or bounds[0] == bounds[1]:
            return {'actual_time_report': None, 'CEM_trial_families': [],
                    'CEM_calculation_backend': backend, 'CEM_column_backend': columns, 'empty_admission': True}
        if actual_report is None:
            reference = sum(bounds) / 2 if reference is None else full.nonnegative(reference)
            trial = actual.RetardedActualTimeMeasure.generate_trial(self._source, *bounds, reference,
                left_closed=selected.lower_closed, right_closed=selected.upper_closed,
                slices=delay_slices, order=delay_order, mode_bits=delay_mode_bits,
                coefficient_bits=coefficient_bits, envelope_order=envelope_order,
                delay_representation=delay_representation,delay_krylov_dimension=delay_krylov_dimension)
            actual_report = actual.RetardedActualTimeMeasure.certify(self._source, trial,
                coefficient_bits=coefficient_bits, envelope_order=envelope_order)
        else:
            actual_report = RetardedActualRecordMeasure._receipt(self, bounds, selected, actual_report)
        states = [channel._read_input(row['complete_actual_time_poststate'], joint.DIMENSION)
                  for row in actual_report['four_pattern_actual_time_poststates']]
        if backend == 'local_terminal':
            families = [local_cem.generate_trials(self._cem, matrix, mode_bits=mode_bits,
                coefficient_bits=coefficient_bits, krylov_dimension=cem_krylov_dimension) for matrix in states]
        else:
            families = [cem.FullZeemanCEMSource.generate_trials(self._cem, matrix, order=order,
                mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
                for matrix in states]
        return {'actual_time_report': actual_report, 'CEM_trial_families': families,
            'CEM_calculation_backend': backend, 'CEM_column_backend': columns, 'empty_admission': False,
            'same_original_pair': list(decoded[1]), 'source_record': raw}

    def generate(self, first, second, admitted, pair_row, trial_families, *, actual_report=None,
                 mode_bits=96, coefficient_bits=192, exponential_bits=192, cem_backend='marked',
                 cem_column_backend='rational'):
        backend = _cem_backend(cem_backend)
        columns = _cem_columns(backend, cem_column_backend)
        raw, decoded, restriction = RetardedActualRecordMeasure._coordinates(self, first, second, admitted, pair_row)
        rows, origin, settings, herald, clicks = decoded
        selected, cell, faces, reasons, bounds = restriction
        empty = selected is None or bounds[0] == bounds[1]
        precision = dict(mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        packets, certificates = [], []
        old = local = model = input_norm = tail = Q(0); tail_components = []
        if not empty:
            actual_report = RetardedActualRecordMeasure._receipt(self, bounds, selected, actual_report)
            _require(type(trial_families) is list and len(trial_families) == 4,
                     'all four actual joint pattern poststates require their complete CEM witnesses')
            states = [channel._read_input(row['complete_actual_time_poststate'], joint.DIMENSION)
                      for row in actual_report['four_pattern_actual_time_poststates']]
            old = Q(actual_report['whole_four_pattern_trace_norm_error'])
            input_norm = sum((records.bsm._entry_norm(matrix, bits=coefficient_bits) for matrix in states), Q(0))
            tail, tail_components = _continuing_tail(self._source, bounds[0], coefficient_bits)
            model = (self._model + tail) * (input_norm + old)
            for h, (matrix, families) in enumerate(zip(states, trial_families)):
                if backend == 'local_terminal':
                    reports = local_cem.image(self._cem, matrix, families, input_error=0,
                        column_backend=columns, **precision)
                    outcomes = [channel._read_input(row, joint.DIMENSION) for row in reports['complete_four_outcomes']]
                    error = Q(reports['whole_four_output_trace_norm_error'])
                else:
                    outcomes, error, reports = cem.FullZeemanCEMSource.image(self._cem, matrix, families, precision)
                local += error; certificates.append(reports)
                for outcome, state in zip(records.window.REGISTRATION_ORDER, outcomes):
                    packets.append({'pattern': h, 'herald': bsm.PATTERNS[h][0], 'clicks': list(outcome),
                                    'complete_matrix': channel._input_record(state)})
        else:
            _require(actual_report is None and trial_families == [], 'empty record admission uses the exact zero instrument')
            for h in range(4):
                for outcome in records.window.REGISTRATION_ORDER:
                    packets.append({'pattern': h, 'herald': bsm.PATTERNS[h][0], 'clicks': list(outcome), 'complete_matrix': []})
        error = old + local + model
        denominator = records._sum(channel._read_input(p['complete_matrix'], joint.DIMENSION)
            for p in packets if p['herald'] == herald)
        numerator = records._sum(channel._read_input(p['complete_matrix'], joint.DIMENSION)
            for p in packets if p['herald'] == herald and tuple(p['clicks']) == clicks)
        n, nlo, nhi = records._trace_bounds(numerator, error, coefficient_bits)
        d, dlo, dhi = records._trace_bounds(denominator, error, coefficient_bits)
        positive_input = self._positive['certified']
        if positive_input:
            probability = [str(nlo / dhi if dhi else 0), str(min(Q(1), nhi / dlo) if dlo else 1)]
        else:
            probability = None
            n, rounding_n = full.radical_midpoint(joint._trace(numerator).real, coefficient_bits)
            d, rounding_d = full.radical_midpoint(joint._trace(denominator).real, coefficient_bits)
            nlo, nhi = n - error - rounding_n, n + error + rounding_n
            dlo, dhi = d - error - rounding_d, d + error + rounding_d
        return {'schema': SCHEMA + '/original-event', 'source_record': raw, 'original_pair': list(origin),
            'original_rows': [list(row) for row in rows], 'settings': list(settings), 'herald': herald, 'clicks': list(clicks),
            'original_record_cell': records._cell_record(cell), 'selected_first_gate_cell': records._cell_record(selected),
            'encoder_inverse_faces': faces, 'empty_or_unadmitted_reasons': reasons,
            'source_receipt_restriction_seconds': list(map(str, bounds)), 'whole_actual_time_report': actual_report,
            'sixteen_CEM_packets': packets, 'complete_CEM_step_certificates': certificates,
            'trial_families': records._copy(trial_families), 'precision': precision,
            'CEM_calculation_backend': backend,
            'CEM_column_backend': columns,
            'source_actual_time_error_transported_once': str(old), 'CEM_new_local_error_direct_sum': str(field._price_upper(local, coefficient_bits)),
            'CEM_input_centre_trace_norm_upper': str(field._price_upper(input_norm, coefficient_bits)),
            'CEM_source_model_true_input_payment': str(field._price_upper(model, coefficient_bits)),
            'continuing_Gaussian_density_difference_per_input_norm': str(field._price_upper(tail, coefficient_bits)),
            'continuing_Gaussian_source_tail_components': tail_components,
            'CEM_old_model_difference_per_input_norm': str(self._model),
            'CEM_model_includes_input_error_cross_term': True,
            'complete_event_trace_norm_error': str(field._price_upper(error, coefficient_bits)),
            'selected_complete_matrix': channel._input_record(numerator), 'admission_complete_matrix': channel._input_record(denominator),
            'selected_mass_centre': str(n), 'admission_mass_centre': str(d),
            'selected_mass_bounds': list(map(str, (nlo, nhi))), 'admission_mass_bounds': list(map(str, (dlo, dhi))),
            'conditional_first_gate_probability_bounds': probability,
            'probability_interpretation_source': self._positive,
            'conditional_on_positive_source_input': not positive_input,
            'strict_normalizer_source_generated': positive_input and dlo > 0, 'same_cell_for_numerator_and_admission': True,
            'admission_does_not_read_CEM_outcome': True, 'empty_admission_is_zero_instrument': empty,
            'complete_time_field_and_queue_mother': raw['complete_actual_time_measure'],
            'actual_hardware_uniquely_identified': False, 'full_nextRaw_history_scored': False,
            'new_confidence_budget_spent': False, 'controller_advance': False}

    def verify(self, report, first, second, admitted):
        _require(type(report) is dict and report.get('schema') == SCHEMA + '/original-event', 'complete original record source event required')
        expected = RetardedActualRecordMeasure.generate(self, first, second, admitted, report['original_pair'][1],
            report['trial_families'], actual_report=report['whole_actual_time_report'],
            cem_backend=report['CEM_calculation_backend'], cem_column_backend=report['CEM_column_backend'],
            **report['precision'])
        _require(expected == report, 'original inverse cell, complete CEM, source error or admission changed')
        return True


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None)), repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None))


def _signature():
    helpers = (_require, _bindings, _digest, _cem_backend, _cem_columns, _field_record, _positive_input, _continuing_tail, _function, _signature, _check,
        actual.RetardedActualTimeMeasure.record, actual.RetardedActualTimeMeasure.generate_trial,
        actual.RetardedActualTimeMeasure.certify, actual.RetardedActualTimeMeasure.verify,
        response.ReferenceResponseWindowSource.record, cem.FullZeemanCEMSource.record,
        local_cem.generate_trials, local_cem.image,
        cem.FullZeemanCEMSource.generate_trials, cem.FullZeemanCEMSource.image, cem.FullZeemanCEMSource.geometry_source,
        original._restriction, _ORIGINAL_EXECUTION, records.observed.decode_observation,
        records._response_support, records._record_cell, records._sum, records._trace_bounds,
        gaussian.GaussianAtomicPulseSource.field_off_tail_price, positive._psd,
        positive.photons.radical_sign, positive.photons.radical_inverse,
        field._price_upper, channel._read_input, channel._input_record)
    methods = tuple(_function(v) for v in vars(RetardedActualRecordMeasure).values() if callable(v))
    return tuple(map(_function, helpers)), methods, SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
        actual._CHECK is _ACTUAL_CHECK and response._CHECK is _RESPONSE_CHECK and cem._CHECK is _CEM_CHECK and
        local_cem._CHECK is _LOCAL_CEM_CHECK and
        original._execution is _ORIGINAL_EXECUTION, 'actual-time original record source execution changed')
    _ACTUAL_CHECK(); _RESPONSE_CHECK(); _CEM_CHECK(); _LOCAL_CEM_CHECK(); _ORIGINAL_EXECUTION()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
