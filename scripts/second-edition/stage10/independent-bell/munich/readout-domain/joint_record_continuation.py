"""A checked joint record posterior enters its original reload and BSM source.

The integrated quantum coimage is sufficient for the time-homogeneous raw
actions.  Its conditional time/state mother remains in the source recipe;
neither the response-end offset nor an occupation witness is an actual clock.
"""
from fractions import Fraction as Q
import hashlib
import inspect
from pathlib import Path

import atomic_full_forward as full
import bsm_background_tail as background
import bsm_resolvent as bsm_future
import bsm_retry_source as bsm
import bsm_channel as marked
import fluorescence_channel as channel
import history_feed as history
import joint_reload_resolvent as native
import joint_reload_source as reload
import projected_window_cem as projected
import receipt_record_measure as record_measure
import stopped_history_law as stopped_history


SOURCE_SCHEMA = 'stage10-joint-record-native-continuation-source/v1'
SCHEMA = 'stage10-joint-record-whole-native-BSM-continuation/v1'


def _copy(value):
    return projected._copy(value)


def _observers(record):
    channel._require(type(record) is dict and set(record) == {'histories', 'admitted'} and
                     type(record['histories']) is list and len(record['histories']) == 2,
                     'both complete original local observers and admitted run required')
    histories = tuple(history.RecordHistory(item['run'], item['role'],
                      tuple(tuple(row) for row in item['observations']), frozenset(item['paired_rows']))
                      for item in record['histories'])
    raw = record['admitted']
    admitted = history.schema.AdmittedRun(raw['run'],
               tuple(history.schema.Trial(row[0], Q(row[1]), *row[2:]) for row in raw['trials']),
               _copy(raw['token_dictionaries']), _copy(raw['audit']))
    channel._require(record_measure._observer_record(*histories, admitted) == record,
                     'complete observer identity or original trial word changed')
    return *histories, admitted


def _bindings():
    modules = (record_measure, native, bsm_future, background, bsm, marked, reload,
               projected, full, channel, history, stopped_history)
    paths = {Path(__file__).resolve(), *(Path(module.__file__).resolve() for module in modules)}
    return [{'path': str(path.relative_to(full.ROOT)),
             'sha256': hashlib.sha256(path.read_bytes()).hexdigest()} for path in sorted(paths)]


def _signature(function):
    value = getattr(function, '__func__', function)
    return (id(value), id(getattr(value, '__code__', None)),
            repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None)))


def _ray_scale(matrix, original):
    channel._require(bool(original) and set(matrix) == set(original),
                     'the complete source matrices must occupy the same nonzero ray')
    trace, radius = projected._trace(original)
    next_trace, next_radius = projected._trace(matrix)
    channel._require(radius == next_radius == 0 and trace > 0 and next_trace > 0,
                     'an exact positive source ray mass is required for linear transport')
    factor = next_trace/trace
    channel._require(all(matrix[key] == value*factor for key, value in original.items()),
                     'the complete source matrices differ beyond their common ray mass')
    return factor


def _scaled_trials(pieces, factor, old_bits, new_bits=None):
    """Scale amplitudes and re-encode precision; the source frequencies stay fixed."""
    new_bits = old_bits if new_bits is None else new_bits
    precision = Q(2)**(new_bits-old_bits)
    result = _copy(pieces)
    def rounded(value):
        value = Q(value)
        return full._round_nearest(value.numerator, value.denominator)
    for piece in result:
        for mode in piece['modes']:
            mode['lambda'] = [rounded(value*precision) for value in mode['lambda']]
            for matrix in mode['coefficients']:
                for row in matrix:
                    row[-2:] = [rounded(value*factor*precision) for value in row[-2:]]
    return result


def _scaled_matrix(record, factor):
    matrix = channel._read_input(record, reload.DIMENSION)
    return channel._input_record({key: value*factor for key, value in matrix.items()})


def _reprice_bsm_curves(raw, witness, factor):
    """Recheck the original forty-cycle curves at their transported inputs."""
    if factor == 1:
        return _copy(witness)
    channel._require(type(witness) is dict and set(witness) == {
        'schema', 'occupation_matrix', 'phase_certificates', 'gate_certificates', 'multitone_bits'} and
        witness['schema'] == bsm_future.WITNESS_SCHEMA and len(witness['gate_certificates']) == bsm.BURST_CYCLES,
        'the complete original forty-cycle occupation curves are required')
    original_phases = iter(witness['phase_certificates'])
    phases, gates = [], []
    occupation = _scaled_matrix(witness['occupation_matrix'], factor)
    state = channel._read_input(occupation, reload.DIMENSION)
    def evolve(values, matrix):
        price = Q(0)
        for phase in values:
            if not phase.duration:
                continue
            template = next(original_phases, None)
            channel._require(template is not None, 'every original atomic phase curve must remain')
            source = bsm.joint.JointCounterGenerator(phase.first, phase.second, threshold=1,
                        background_rate=0, collection=((0, 0, 0, 0, 0, 0),))
            channel._require(template['raw_source'] == source.record() and template['initial_counter'] == 0,
                             'transport must retain the original raw atomic phase and counter')
            payment = phase.model_error*(bsm._entry_norm(matrix)+price)
            certificate = channel.certify(source, matrix,
                _scaled_trials(template['trial_pieces'], factor, template['mode_bits']),
                upstream_error=price+payment, mode_bits=template['mode_bits'],
                coefficient_bits=template['coefficient_bits'], exponential_bits=template['exponential_bits'])
            phases.append(certificate)
            matrix, price = channel.poststate(certificate)
        return matrix
    for cycle, template in enumerate(witness['gate_certificates'], 1):
        state = evolve(raw.preparation+raw.excitation+raw.arrival_delay, state)
        channel._require(template['raw_source'] == raw.gate.record(),
                         'transport must retain the original complete BSM gate')
        certificate = marked.certify(raw.gate, state,
            _scaled_trials(template['trial_pieces'], factor, template['mode_bits']),
            upstream_error=0, mode_bits=template['mode_bits'], coefficient_bits=template['coefficient_bits'],
            exponential_bits=template['exponential_bits'])
        gates.append(certificate)
        for pattern in certificate['patterns']:
            endpoint = {(i, j): bsm.dipole.ComplexRadical(Q(a), Q(b))
                        for i, j, a, b in pattern['poststate_center']}
            evolve(raw.return_phases, endpoint)
        state, _ = marked.poststate(certificate, 'failure')
        state = evolve(raw.return_phases+(raw.recooling if cycle == bsm.BURST_CYCLES else ()), state)
    channel._require(next(original_phases, None) is None, 'no unrelated phase curve may be added')
    return {'schema': bsm_future.WITNESS_SCHEMA, 'occupation_matrix': occupation,
            'phase_certificates': phases, 'gate_certificates': gates, 'multitone_bits': witness['multitone_bits']}


class JointRecordContinuation:
    def __init__(self, source, joint_report, first, second, admitted):
        channel._require(type(self) is JointRecordContinuation and type(source) is record_measure.ReceiptRecordMeasure,
                         'closed ReceiptRecordMeasure required; a posterior matrix is not a source')
        record_measure._closed(source)
        source_record = record_measure.ReceiptRecordMeasure.record(source)
        channel._require(type(joint_report) is dict and joint_report.get('schema') == record_measure.JOINT_SCHEMA and
                         joint_report.get('source_record') == source_record,
                         'same complete original joint record posterior required')
        channel._require(type(first) is history.RecordHistory and type(second) is history.RecordHistory and
                         type(admitted) is history.schema.AdmittedRun,
                         'original closed complete record observers required')
        observer = _copy(record_measure._observer_record(first, second, admitted))
        channel._require(joint_report['complete_original_observer'] == observer,
                         'joint posterior must consume the same complete original observers')
        report = _copy(joint_report)
        self.source = source
        self._source_record, self._joint_report, self._observer_record = source_record, report, observer
        self._first, self._second, self._admitted = _observers(observer)
        self._reload = reload.JointReloadSource.from_record(report['raw_reload_source'])
        # This is the sole state-producing entrance.  The original owner
        # verifies the joint CP families and emits stage0/counter0 itself.
        inlet = record_measure.ReceiptRecordMeasure.joint_reload_input(source, report, self._reload,
                                      self._first, self._second, self._admitted)
        self._inlet = self._inlet_record(inlet)
        self._burst = background._from_record('programme', self._inlet['raw_BSM_source'])
        channel._require(self._burst.gate.seconds_per_unit == Q(self._inlet['seconds_per_source_unit']),
                         'joint posterior and original BSM must share the source time unit')
        self._hardware = _copy(type(source._mother).hardware_record(source._mother))
        self._value = {'schema': SOURCE_SCHEMA, 'receipt_record_source': source_record,
            'original_joint_posterior': report, 'complete_original_observer': observer,
            'source_inlet': self._inlet, 'original_shared_hardware': self._hardware,
            'raw_encoding': source_record['raw_encoding'], 'window_geometry': report['window_geometry'],
            'source_bindings': _bindings(), 'inlet_state_owner': 'ReceiptRecordMeasure.joint_reload_input',
            'source_control': {'stage': 0, 'shared_counter': 0},
            'input_matrix_or_target_receipt_allowed': False, 'hardware_prior_used': False,
            'conditional_time_state_mother_retained': True, 'actual_scalar_clock_created': False,
            'literal_cohort_reconstructed': False, 'actual_original_run_admission_certified': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False}
        self._seal = channel._canonical(self._value)
        self._execution = self._execution_signature()
        self._verified_result_snapshot = None

    def _inlet_record(self, inlet):
        channel._require(type(inlet) is dict and inlet['source_posterior_record'] == self._joint_report and
                         inlet['raw_reload_source'] == self._joint_report['raw_reload_source'] and
                         inlet['raw_BSM_source'] == self._joint_report['raw_BSM_source'],
                         'the original joint owner must generate the complete native inlet')
        self._reload._projected_blocks(inlet['state'])
        channel._require(all(key[:2] == (0, 0) for key in inlet['state']),
                         'the post-CEM diagnostic starts at original stage0 and counter0')
        matrix = {(i, j): value for (_, _, i, j), value in inlet['state'].items()}
        matrix = channel._initial(matrix, reload.DIMENSION)
        box, mother = self._joint_report['normalized_state_box'], self._joint_report['time_state_mother_record']
        domain = {'encoder': self._joint_report['encoder_domains'], 'detector': self._joint_report['detector_domain']}
        error = full.nonnegative(inlet['upstream_trace_norm_error'])
        unit, start = map(full.exact, (inlet['seconds_per_source_unit'], inlet['source_relative_start']))
        channel._require(channel._input_record(matrix) == box['normalized_complete_state_centre'] and
                         error == Q(box['uniform_posterior_trace_norm_error']) and
                         inlet['parameter_domain'] == domain and inlet['time_state_mother_record'] == mother and
                         inlet['source_support_word'] == self._joint_report['source_support_word'] and
                         unit == Q(self._joint_report['window_geometry']['seconds_per_unit']) and unit > 0 and
                         start == Q(mother['common_response_end_shift']) and start >= 0,
                         'native inlet must retain the sealed uniform state, error, parameter support and time mother')
        return _copy({'complete_matrix': channel._input_record(matrix), 'upstream_trace_norm_error': str(error),
            'parameter_domain': domain, 'source_support_word': inlet['source_support_word'],
            'time_state_mother_record': mother, 'raw_reload_source': inlet['raw_reload_source'],
            'raw_BSM_source': inlet['raw_BSM_source'], 'source_relative_start': str(start),
            'seconds_per_source_unit': str(unit), 'stage': 0, 'shared_counter': 0,
            'source_relative_start_is_actual_clock': False, 'literal_cohort_reconstructed': False})

    def _execution_signature(self):
        methods = tuple(_signature(inspect.getattr_static(type(self), name)) for name in
                        ('__init__', '_inlet_record', '_execution_signature', 'record', 'from_record',
                         'hardware_record', '_assemble_result', 'certify', 'certify_rebased', 'verify', 'receipt_measure'))
        helpers = tuple(_signature(value) for value in
                        (_copy, _observers, _bindings, _signature, _ray_scale, _scaled_trials,
                         _scaled_matrix, _reprice_bsm_curves, record_measure._observer_record,
                         native.certify, native._source, native._blocks, native.certify_contraction,
                         native.verify_certificate, reload.certify_window, reload.JointReloadSource.projected_window_end,
                         bsm_future.certify, bsm_future._source, bsm_future.contraction,
                         bsm_future._joint_price, background._from_record,
                         channel.certify, channel.poststate, marked.certify, marked.poststate))
        return methods, helpers, stopped_history._verification_code(self.source._mother)

    def record(self):
        channel._require(type(self) is JointRecordContinuation and type(self.source) is record_measure.ReceiptRecordMeasure and
                         type(self._reload) is reload.JointReloadSource and
                         type(self._burst) is bsm_future.stopped.StoppedBSMProgramme,
                         'closed original joint, reload and BSM sources required')
        record_measure._closed(self)
        record_measure._closed(self.source)
        channel._require(self._execution == self._execution_signature() and
                         self._value['source_bindings'] == _bindings() and
                         channel._canonical(self._value) == self._seal,
                         'joint continuation source or executed checker changed')
        channel._require(record_measure.ReceiptRecordMeasure.record(self.source) == self._source_record and
                         self._source_record == self._value['receipt_record_source'] and
                         self._joint_report == self._value['original_joint_posterior'] and
                         self._observer_record == self._value['complete_original_observer'] and
                         record_measure._observer_record(self._first, self._second, self._admitted) == self._observer_record and
                         self._inlet == self._value['source_inlet'] and
                         reload.JointReloadSource.record(self._reload) == self._inlet['raw_reload_source'] and
                         type(self._burst).record(self._burst) == self._inlet['raw_BSM_source'] and
                         self._hardware == self._value['original_shared_hardware'] and
                         type(self.source._mother).hardware_record(self.source._mother) == self._hardware,
                         'original joint posterior, raw hardware, observer, price or time spectrum changed')
        for value in (self._reload, self._burst):
            record_measure._closed(value)
        return _copy(self._value)

    @classmethod
    def from_record(cls, record):
        channel._require(type(record) is dict and record.get('schema') == SOURCE_SCHEMA,
                         'closed same-joint continuation source record required')
        source = record_measure.ReceiptRecordMeasure.from_record(record['receipt_record_source'])
        first, second, admitted = _observers(record['complete_original_observer'])
        result = cls(source, record['original_joint_posterior'], first, second, admitted)
        channel._require(result.record() == record,
                         'joint source, original observer, parameter support or native inlet changed')
        return result

    def hardware_record(self):
        self.record()
        return _copy(self._hardware)

    def certify(self, witnesses):
        source_record = self.record()
        channel._require(type(witnesses) is dict and set(witnesses) == {'reload', 'BSM'},
                         'only native reload and whole BSM occupation witnesses are accepted')
        proposals = _copy(witnesses)
        matrix = channel._read_input(self._inlet['complete_matrix'], reload.DIMENSION)
        pending = {stage: matrix if stage == 0 else {} for stage in range(reload.READY)}
        inherited = Q(self._inlet['upstream_trace_norm_error'])
        ready = native.certify(self._reload, pending, proposals['reload'],
                              seconds_per_unit=self._inlet['seconds_per_source_unit'], upstream_error=inherited)
        state = channel._read_input(ready['generated_ready_JX'], reload.DIMENSION)
        receipt = bsm_future.certify(self._burst, state, proposals['BSM'],
                                   upstream_error=ready['ready_trace_norm_error'])
        return self._assemble_result(source_record, ready, receipt, proposals)

    def _assemble_result(self, source_record, ready, receipt, proposals, transport=None):
        inherited = Q(self._inlet['upstream_trace_norm_error'])
        channel._require(Q(ready['upstream_trace_norm_error']) == inherited and
                         Q(receipt['upstream_trace_norm_error']) == Q(ready['ready_trace_norm_error']),
                         'the uniform whole source error must travel once through both native actions')
        whole_error = Q(receipt['whole_receipt_trace_norm_error'])
        result = _copy({'schema': SCHEMA, 'source_record': source_record,
            'native_reload_resolvent': ready, 'BSM_resolvent': receipt,
            'complete_future_ready_matrix': ready['generated_ready_JX'],
            'whole_receipt_measure': {'poststates': receipt['generated_receipt_JX'],
                'global_trace_norm_error': str(whole_error),
                'pattern_inventory': [{'pattern_index': index, 'physical_herald': herald, 'ports': list(ports)}
                                      for index, (herald, ports) in enumerate(bsm.PATTERNS)],
                'receipt_matrices_are_time_integrated': True, 'individual_inherited_errors_summed': False},
            'parameter_domain': self._inlet['parameter_domain'], 'source_support_word': self._inlet['source_support_word'],
            'original_shared_hardware': self._hardware, 'raw_encoding': source_record['raw_encoding'],
            'window_geometry': source_record['window_geometry'],
            'time_state_mother_record': self._inlet['time_state_mother_record'],
            'complete_relative_time_measure_recipe': {
                'conditional_original_time_state_mother': self._inlet['time_state_mother_record'],
                'receipt_relative_response_end_shift': self._inlet['source_relative_start'],
                'raw_native_source': ready['raw_source'],
                'native_time_edges': ready['source_relative_time_recurrence'],
                'native_measure': 'J_native(z)*(I-K_native(z))^-1 on every original conditional time restriction',
                'BSM_first_receipt_measure': receipt['full_relative_time_measure_recipe'],
                'composition': 'retain the original conditional mother; shift each native edge and every BSM first-receipt branch before composing',
                'aggregate_quantum_coimage_scope': 'time-homogeneous raw actions; absolute time/state correlation remains in the mother recipe'},
            'old_whole_error_paid_once': str(inherited), 'new_native_ready_error': ready['new_resolvent_ready_error'],
            'new_whole_BSM_receipt_error': receipt['new_whole_receipt_error'], 'global_trace_norm_error': str(whole_error),
            'whole_source_error_paid_once': True, 'all_four_original_BSM_patterns_retained': True,
            'native_and_BSM_pending_absorbed_by_original_source_contractions': True,
            'time_resolved_numerical_measure_certified': False, 'actual_scalar_clock_created': False,
            'literal_cohort_reconstructed': False, 'actual_original_run_admission_certified': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False})
        if transport is not None:
            result['source_witness_transport'] = _copy(transport)
        self._verified_result_snapshot = (self._execution_signature(), channel._canonical(proposals),
                                          channel._canonical(result))
        return result

    def certify_rebased(self, original_native, original_bsm):
        """Prepend the mother's paid stage0 and transport the original suffix."""
        source_record = self.record()
        native_template, bsm_template = _copy(original_native), _copy(original_bsm)
        channel._require(type(native_template) is dict and native_template.get('schema') == native.SCHEMA and
                         native_template.get('raw_source') == self._inlet['raw_reload_source'] and
                         Q(native_template['seconds_per_source_unit']) == Q(self._inlet['seconds_per_source_unit']) and
                         type(bsm_template) is dict and bsm_template.get('schema') == bsm_future.SCHEMA and
                         bsm_template.get('raw_source') == self._inlet['raw_BSM_source'],
                         'both original resolvents must use the same complete raw native and BSM source')
        parent = self._source_record['whole_source']['complete_native_parent']
        channel._require(parent['source_record']['raw_source'] == self._inlet['raw_reload_source'] and
                         Q(parent['source_record']['seconds_per_source_unit']) == Q(self._inlet['seconds_per_source_unit']) and
                         parent['steps'] and len(parent['steps'][0]) == 1,
                         'the same mother must own a unique initial diagnostic step')
        prefix = parent['steps'][0][0]
        certificate = prefix['certificate']
        channel._require(prefix['depth'] == prefix['stage'] == certificate['stage'] == 0 and
                         Q(prefix['start_time']) == Q(parent['start_time']) and
                         Q(prefix['end_time'])-Q(prefix['start_time']) == self._reload._window(0).duration and
                         certificate['raw_source']['source_programme'] == self._inlet['raw_reload_source'] and
                         certificate['initial_counter'] == 0,
                         'prepend the original stage0 at its source clock; an arbitrary curve is not a prefix')
        matrix = channel._read_input(self._inlet['complete_matrix'], reload.DIMENSION)
        original = channel._read_input(certificate['initial_state'], reload.DIMENSION)
        factor = _ray_scale(matrix, original)
        endpoint = {(0, c, i, j): bsm.dipole.ComplexRadical(Q(a), Q(b))
                    for c, i, j, a, b in certificate['counter_poststate_center']}
        suffix, finite_ready = {stage: {} for stage in range(reload.READY)}, {}
        for branch in self._reload.projected_window_end(endpoint).values():
            for (stage, counter, i, j), value in branch.items():
                native._add(finite_ready if stage == reload.READY else suffix[stage], {(i, j): value})
        channel._require(native._block_record(suffix) == native_template['initial_pending'],
                         'every original suffix stage matrix must equal the source-generated prefix boundary')
        native.verify_certificate(native_template, self._reload, suffix)
        witness = _copy(native_template['untrusted_occupation_witness'])
        bits = witness['precision'][0]
        channel._require(not witness['occupation'][0]['complete_matrix'],
                         'the suffix occupation cannot already contain an initial diagnostic')
        for item in witness['occupation']:
            item['complete_matrix'] = _scaled_matrix(item['complete_matrix'], factor)
            item['trial_pieces'] = _scaled_trials(item['trial_pieces'], factor, bits)
        witness['occupation'][0] = {'stage': 0, 'complete_matrix': channel._input_record(matrix),
            'trial_pieces': _scaled_trials(certificate['trial_pieces'], factor, certificate['mode_bits'], bits)}
        pending = {stage: matrix if stage == 0 else {} for stage in range(reload.READY)}
        ready = native.certify(self._reload, pending, witness,
                    seconds_per_unit=self._inlet['seconds_per_source_unit'],
                    upstream_error=self._inlet['upstream_trace_norm_error'])
        original_ready = dict(finite_ready)
        native._add(original_ready, channel._read_input(native_template['generated_ready_JX'], reload.DIMENSION))
        old_bsm_input = channel._read_input(bsm_template['initial_matrix'], reload.DIMENSION)
        channel._require(original_ready == old_bsm_input,
                         'the original BSM input must be the full source-generated prefix plus suffix Ready matrix')
        state = channel._read_input(ready['generated_ready_JX'], reload.DIMENSION)
        bsm_factor = _ray_scale(state, old_bsm_input)
        bsm_witness = _reprice_bsm_curves(self._burst, bsm_template['untrusted_occupation_witness'], bsm_factor)
        receipt = bsm_future.certify(self._burst, state, bsm_witness, upstream_error=ready['ready_trace_norm_error'])
        proposals = {'reload': witness, 'BSM': bsm_witness}
        transport = {'schema': SOURCE_SCHEMA+'/witness-rebasing',
            'original_native_resolvent': native_template, 'original_BSM_resolvent': bsm_template,
            'source_owned_prefix': prefix, 'prefix_initial_complete_matrix': certificate['initial_state'],
            'prefix_generated_pending': native._block_record(suffix),
            'prefix_generated_ready': channel._input_record(finite_ready),
            'new_inlet_to_original_prefix_scale': str(factor),
            'new_ready_to_original_BSM_inlet_scale': str(bsm_factor),
            'native_rule': 'one source-owned stage0 occupation plus the original complete suffix occupation',
            'BSM_rule': 'scale the complete original occupation and every phase/gate coefficient; recheck input and local prices',
            'relative_clock_rule': 'transport the same time-homogeneous stage action; the conditional mother supplies its time origin',
            'source_frequencies_and_window_durations_changed': False,
            'target_ready_or_receipt_used': False, 'solver_executed': False}
        return self._assemble_result(source_record, ready, receipt, proposals, transport)

    def verify(self, report, first=None, second=None, admitted=None):
        source_record = self.record()
        channel._require(type(report) is dict and report.get('schema') == SCHEMA and
                         report.get('source_record') == source_record,
                         'same closed joint continuation result required')
        channel._require(all(value is None for value in (first, second, admitted)) or
                         all(value is not None for value in (first, second, admitted)),
                         'both full observers and admitted run must be supplied together')
        if first is not None:
            channel._require(record_measure._observer_record(first, second, admitted) == self._observer_record,
                             'complete original observer or unpaired record identity changed')
        channel._require(type(report.get('native_reload_resolvent')) is dict and
                         type(report.get('BSM_resolvent')) is dict,
                         'both complete original source resolvent certificates required')
        witnesses = {'reload': report['native_reload_resolvent']['untrusted_occupation_witness'],
                     'BSM': report['BSM_resolvent']['untrusted_occupation_witness']}
        signature = (self._execution_signature(), channel._canonical(witnesses), channel._canonical(report))
        if self._verified_result_snapshot is not None and self._verified_result_snapshot[:2] == signature[:2]:
            channel._require(self._verified_result_snapshot == signature,
                             'same checked curves must retain their complete source receipt and metadata')
            return True
        if 'source_witness_transport' in report:
            transport = report['source_witness_transport']
            channel._require(type(transport) is dict and transport.get('schema') == SOURCE_SCHEMA+'/witness-rebasing',
                             'closed source-generated witness transport required')
            expected = self.certify_rebased(transport['original_native_resolvent'], transport['original_BSM_resolvent'])
        else:
            expected = self.certify(witnesses)
        channel._require(expected == report,
                         'native source, full receipt, uniform error, parameter domain or time mother changed')
        self._verified_result_snapshot = signature
        return True

    def receipt_measure(self, report):
        self.verify(report)
        value = report['whole_receipt_measure']
        return {'poststates': tuple(channel._read_input(matrix, reload.DIMENSION) for matrix in value['poststates']),
                'global_trace_norm_error': Q(value['global_trace_norm_error']),
                'pattern_inventory': _copy(value['pattern_inventory']),
                'parameter_domain': _copy(report['parameter_domain']),
                'source_support_word': _copy(report['source_support_word']),
                'time_state_mother_record': _copy(report['time_state_mother_record']),
                'complete_relative_time_measure_recipe': _copy(report['complete_relative_time_measure_recipe']),
                'receipt_matrices_are_time_integrated': True, 'time_resolved_numerical_measure_certified': False,
                'actual_scalar_clock_created': False}
