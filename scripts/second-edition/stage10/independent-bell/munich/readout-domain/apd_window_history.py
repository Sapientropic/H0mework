"""Shared APD arrival rates and the exact finite-memory sliding-window readout.

The arrival queue labels a quantum jump history; it is not an observed photon
archive.  For thresholds <= N, retaining the last N arrival times gives the
same present and future rolling counts as retaining every arrival.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import atomic_full_forward as full
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint


SCHEMA = 'stage10-shared-APD-sliding-window-source/v1'
BASE = Path(__file__).resolve().parent


def _copy(value):
    return json.loads(channel._canonical(value))


def _public_window():
    raw = (BASE/'programme-sources-hp0001.json').read_bytes()
    source = json.loads(raw)
    return Q(source['PRL_SI']['presence_integration_ms'], 1000), hashlib.sha256(raw).hexdigest()


def _bindings():
    return {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in
            (Path(__file__), Path(joint.__file__), Path(local.__file__), Path(full.__file__), Path(channel.__file__),
             BASE/'munich_atomic_programme.py')}


def _compiled_state(source):
    return repr((vars(source), tuple(vars(atom) for atom in source.sources)))


def _execution_signature():
    functions = (_copy, _public_window, _bindings, _compiled_state, _memory, _closed, _execution_signature,
                 joint._matrix, joint._operator_left, joint._operator_right, local._add, local._sum,
                 local.CounterGenerator.atomic_action, local.CounterGenerator._drift,
                 joint.JointCounterGenerator.from_record.__func__, joint.JointCounterGenerator.record,
                 joint.JointCounterGenerator.detected_action, joint.JointCounterGenerator.unobserved_action,
                 joint.JointCounterGenerator.independent_atomic_action, full.nonnegative, full.exact,
                 APDWindowHistorySource.record, APDWindowHistorySource.memory, APDWindowHistorySource._check_memory,
                 APDWindowHistorySource.elapse, APDWindowHistorySource.append_arrival,
                 APDWindowHistorySource.observe, APDWindowHistorySource.jump_rate,
                 APDWindowHistorySource.no_arrival_action, APDWindowHistorySource.forget_arrival_action,
                 APDWindowHistorySource.first_arrival_source, APDWindowHistorySource.retain_on_phase_change,
                 APDWindowHistorySource.from_atomic_cell.__func__,
                 APDWindowHistorySource.certify_no_arrival, APDWindowHistorySource.verify_no_arrival,
                 APDWindowHistorySource.first_arrival_measure, APDWindowHistorySource.verify_first_arrival_measure,
                 APDWindowHistorySource.stopped_arrival_instrument, APDWindowHistorySource.arrival_memory_at,
                 channel.certify, channel.verify_certificate, channel.poststate,
                 channel.SourceKernel.column, channel.SourceKernel.action, channel._piece,
                 channel._hermitian, channel._coefficient, channel._input_record, channel._read_input)
    return tuple((id(function), id(function.__code__)) for function in functions)


def _closed(source):
    if type(source) is not APDWindowHistorySource or set(vars(source)) != {
            '_raw','seconds_per_unit','maximum_threshold','window','_record','_seal','_compiled'}:
        raise ValueError('closed shared APD instance required')
    if _execution_signature() != _EXPECTED_EXECUTION:
        raise ValueError('shared APD source execution changed')


@dataclass(frozen=True)
class ArrivalMemory:
    clock: Q
    recent: tuple
    maximum_threshold: int
    seconds_per_source_unit: Q

    def record(self):
        return {'source_relative_clock': str(self.clock), 'recent_arrival_times': list(map(str, self.recent)),
                'maximum_threshold': self.maximum_threshold,
                'seconds_per_source_unit': str(self.seconds_per_source_unit),
                'arrival_times_are_latent_source_coordinates': True,
                'which_atom_labels_supplied': False, 'actual_arrival_archive_reconstructed': False}


def _memory(clock, arrivals, maximum_threshold, unit, window):
    clock = full.nonnegative(clock)
    channel._require(type(arrivals) in (tuple, list), 'ordered source arrival word required')
    arrivals = tuple(full.nonnegative(value) for value in arrivals)
    channel._require(all(a <= b for a, b in zip(arrivals, arrivals[1:])) and
                     all(value <= clock for value in arrivals), 'arrival word must be causal and ordered')
    # All omitted arrivals are older than every retained one.  When a retained
    # arrival expires, every omitted arrival has already expired too.
    recent = tuple(value for value in arrivals if clock-window < value <= clock)[-maximum_threshold:]
    return ArrivalMemory(clock, recent, maximum_threshold, unit)


class APDWindowHistorySource:
    def __init__(self, source, *, seconds_per_unit, maximum_threshold=None):
        if _execution_signature() != _EXPECTED_EXECUTION:
            raise ValueError('shared APD source execution changed')
        channel._require(type(self) is APDWindowHistorySource and type(source) is joint.JointCounterGenerator,
                         'original shared APD source required; independent side counters are not input')
        raw = joint.JointCounterGenerator.from_record(source.record())
        unit = full.exact(seconds_per_unit)
        maximum_threshold = raw.threshold if maximum_threshold is None else maximum_threshold
        channel._require(unit > 0 and type(maximum_threshold) is int and maximum_threshold >= raw.threshold,
                         'positive common unit and a threshold cover of the original source required')
        physical_window, binding = _public_window()
        channel._require(physical_window > 0, 'positive public presence integration window required')
        self._raw = raw
        self.seconds_per_unit, self.maximum_threshold = unit, maximum_threshold
        self.window = physical_window/unit
        self._record = {'schema': SCHEMA, 'original_shared_source': raw.record(),
            'seconds_per_source_unit': str(unit), 'public_integration_seconds': str(physical_window),
            'source_window_duration': str(self.window), 'public_programme_binding': binding,
            'maximum_threshold': maximum_threshold, 'arrival_jump': 'D_shared + background * identity',
            'no_arrival_generator': 'L_A + L_B - D_shared - background * identity',
            'observer': 'min(N, number of shared APD arrivals in (t-W,t])',
            'retained_memory': 'last maximum_threshold arrival times, without emitter attribution',
            'owned_atomic_cell': None, 'source_model_delta': '0',
            'cross_measurement_counter_reset_assumed': False, 'actual_controller_policy_identified': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False, 'source_bindings': _bindings()}
        self._seal = channel._canonical(self._record)
        self._compiled = _compiled_state(raw)

    def record(self):
        _closed(self)
        channel._require(type(self) is APDWindowHistorySource and
                         channel._canonical(self._record) == self._seal and
                         self._compiled == _compiled_state(self._raw) and
                         self._raw.record() == self._record['original_shared_source'] and
                         self.seconds_per_unit == Q(self._record['seconds_per_source_unit']) and
                         self.maximum_threshold == self._record['maximum_threshold'] and
                         self.window == Q(self._record['source_window_duration']) and
                         self._record['source_bindings'] == _bindings() and
                         _public_window() == (Q(self._record['public_integration_seconds']),
                                               self._record['public_programme_binding']),
                         'shared source, unit or rolling observer changed')
        return _copy(self._record)

    @classmethod
    def from_record(cls, record):
        channel._require(type(record) is dict and record.get('schema') == SCHEMA, 'shared arrival source record required')
        result = cls(joint.JointCounterGenerator.from_record(record['original_shared_source']),
                     seconds_per_unit=record['seconds_per_source_unit'], maximum_threshold=record['maximum_threshold'])
        if record['owned_atomic_cell'] is not None:
            import munich_atomic_programme as atomic
            owned = record['owned_atomic_cell']
            owner = atomic.MunichAtomicProgramme.from_record(owned['common_programme'])
            atomic.MunichAtomicProgramme.verify_native_cell(owner,owned)
            channel._require(owned['raw_counter_source'] == result._raw.record() and
                             Q(owned['common_programme']['atomic_base']['seconds_per_unit']) == result.seconds_per_unit,
                             'owned atomic model belongs to a different APD source or unit')
            result._record['owned_atomic_cell'] = _copy(owned)
            result._record['source_model_delta'] = owned['per_unit_model_delta']['total']
            result._seal = channel._canonical(result._record)
        channel._require(result.record() == record, 'shared arrival source or claim scope differs')
        return result

    @classmethod
    def from_atomic_cell(cls, owner, first, second, cuts, cell_index, *, threshold, background_rate,
                         collection, maximum_threshold=None, compilation_bits=160):
        import munich_atomic_programme as atomic
        channel._require(cls is APDWindowHistorySource and type(owner) is atomic.MunichAtomicProgramme,
                         'closed common atomic owner required; a model price is not input')
        raw,model = atomic.MunichAtomicProgramme.native_cell(owner,first,second,cuts,cell_index,
            threshold=threshold,background_rate=background_rate,collection=collection,bits=compilation_bits)
        atomic.MunichAtomicProgramme.verify_native_cell(owner,model)
        result = cls(raw,seconds_per_unit=Q(model['common_programme']['atomic_base']['seconds_per_unit']),
                     maximum_threshold=maximum_threshold)
        result._record['owned_atomic_cell'] = _copy(model)
        result._record['source_model_delta'] = model['per_unit_model_delta']['total']
        result._seal = channel._canonical(result._record)
        return result

    def memory(self, clock, ordered_arrivals=()):
        _closed(self)
        self.record()
        return _memory(clock, ordered_arrivals, self.maximum_threshold, self.seconds_per_unit, self.window)

    def _check_memory(self, memory):
        channel._require(type(memory) is ArrivalMemory and memory.maximum_threshold == self.maximum_threshold and
                         memory.seconds_per_source_unit == self.seconds_per_unit and
                         _memory(memory.clock, memory.recent, self.maximum_threshold, self.seconds_per_unit, self.window) == memory,
                         'same causal source arrival-memory coimage required')

    def elapse(self, memory, duration):
        _closed(self)
        self.record()
        self._check_memory(memory)
        duration = full.nonnegative(duration)
        return self.memory(memory.clock+duration, memory.recent)

    def append_arrival(self, memory):
        _closed(self)
        self.record()
        self._check_memory(memory)
        return self.memory(memory.clock, (*memory.recent, memory.clock))

    def observe(self, memory, *, threshold=None):
        _closed(self)
        self.record()
        self._check_memory(memory)
        threshold = self._raw.threshold if threshold is None else threshold
        channel._require(type(threshold) is int and 1 <= threshold <= self.maximum_threshold,
                         'observation threshold outside the retained source cover')
        return {'threshold': threshold, 'capped_count': min(threshold, len(memory.recent)),
                'at_least_threshold': len(memory.recent) >= threshold,
                'memory': memory.record(), 'public_observation': 'one shared APD count',
                'emitter_identity_observed': False}

    def jump_rate(self, matrix):
        _closed(self)
        self.record()
        matrix = joint._matrix(matrix)
        result = self._raw.detected_action(matrix)
        for key, value in matrix.items():
            local._add(result, key, self._raw.background_rate*value)
        return result

    def no_arrival_action(self, matrix):
        _closed(self)
        self.record()
        matrix = joint._matrix(matrix)
        result = self._raw.unobserved_action(matrix)
        for key, value in matrix.items():
            local._add(result, key, -self._raw.background_rate*value)
        return result

    def forget_arrival_action(self, matrix):
        _closed(self)
        return local._sum(self.no_arrival_action(matrix), self.jump_rate(matrix))

    def first_arrival_source(self):
        """The original threshold-one CP source, including both complete blocks."""
        _closed(self)
        record = self.record()['original_shared_source']
        record['threshold'], record['counter_levels'] = 1, 2
        return joint.JointCounterGenerator.from_record(record)

    def certify_no_arrival(self, memory, initial, pieces, *, upstream_error=0,
                           mode_bits=60, coefficient_bits=160, exponential_bits=160):
        """Original CP residual step and its retained rolling-memory branch."""
        _closed(self)
        self.record()
        self._check_memory(memory)
        raw = self.first_arrival_source()
        old = full.nonnegative(upstream_error)
        centre_norm = Q(0)
        for value in channel._initial(initial,joint.DIMENSION).values():
            for part in (value.real,value.imag):
                centre,error = full.radical_midpoint(part,coefficient_bits)
                centre_norm += abs(centre)+error
        model_delta = Q(self.record()['source_model_delta'])
        model_price = model_delta*centre_norm
        certificate = channel.certify(raw, initial, pieces, upstream_error=old+model_price,
                    mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        state, error = channel.poststate(certificate, 'below_N')
        following = self.elapse(memory, raw.duration)
        return {'schema': SCHEMA+'/no-arrival-step', 'source_record': self.record(),
            'incoming_memory': memory.record(), 'original_threshold_one_certificate': certificate,
            'no_arrival_complete_poststate': channel._input_record(state),
            'no_arrival_trace_norm_error': str(error), 'no_arrival_memory': following.record(),
            'upstream_error_before_source_model':str(old),'source_model_per_unit_delta':str(model_delta),
            'complete_centre_trace_norm_upper':str(centre_norm),'source_model_payment':str(model_price),
            'source_model_error_added_to_original_checker_once':True,
            'other_arrival_histories': {'at_least_one_complete_poststate': certificate['at_least_N'],
                'first_arrival_density': '(D_shared+b Id) exp((L_A+L_B-D_shared-b Id)*s) rho',
                'source_relative_interval': [str(memory.clock),str(following.clock)],
                'arrival_memory_remains_a_time_dependent_source_fibre': True,
                'integrated_arrival_mass_replaced_by_end_time': False},
            'subnormalized_CP_branches': True, 'same_source_error_charged_once': True,
            'numerical_clock_is_actual_scalar': False, 'actual_controller_policy_identified': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False}

    def verify_no_arrival(self, report):
        _closed(self)
        channel._require(type(report) is dict and report.get('schema') == SCHEMA+'/no-arrival-step' and
                         report.get('source_record') == self.record(), 'same source no-arrival step required')
        record = report['incoming_memory']
        memory = self.memory(record['source_relative_clock'],record['recent_arrival_times'])
        channel._require(memory.record() == record, 'same complete incoming arrival-memory coimage required')
        certificate = report['original_threshold_one_certificate']
        initial = channel._read_input(certificate['initial_state'], joint.DIMENSION)
        channel.verify_certificate(certificate,self.first_arrival_source(),initial,
                                   upstream_error=certificate['upstream_trace_norm_error'])
        expected = self.certify_no_arrival(memory,initial,certificate['trial_pieces'],
            upstream_error=report['upstream_error_before_source_model'],mode_bits=certificate['mode_bits'],
            coefficient_bits=certificate['coefficient_bits'],exponential_bits=certificate['exponential_bits'])
        channel._require(expected == report,'no-arrival branch, memory, source curve or shared price changed')
        return True

    def first_arrival_measure(self, step, cells=None):
        """First APD jump CP measure from the same complete polynomial curve."""
        _closed(self)
        self.verify_no_arrival(step)
        certificate = step['original_threshold_one_certificate']
        raw = self.first_arrival_source()
        start = Q(step['incoming_memory']['source_relative_clock'])
        stop = start+raw.duration
        cells = ((start,stop),) if cells is None else cells
        channel._require(type(cells) in (tuple,list), 'ordered disjoint source-time cells required')
        cells = tuple(tuple(map(full.exact,cell)) for cell in cells)
        channel._require(all(len(cell) == 2 and start <= cell[0] <= cell[1] <= stop for cell in cells) and
                         all(a[1] <= b[0] for a,b in zip(cells,cells[1:])),
                         'first-arrival cells must be disjoint and inside the original source interval')
        kernel = channel.SourceKernel(raw,certificate['coefficient_bits'])
        bound = sum(max(atom.outgoing) for atom in raw.sources)+raw.background_rate
        price = Q(certificate['initial_radical_error'])
        result, elapsed, local_error = {}, Q(0), Q(0)
        quantum = 1 << certificate['mode_bits']
        nonempty = any(left < right for left,right in cells)
        for piece,paid in zip(certificate['trial_pieces'],certificate['piece_error_records']):
            width = Q(piece['duration'])
            price += sum(Q(paid[key]) for key in ('initial_join_error','source_residual_error',
                                                'radical_coefficient_error','scalar_exponential_error'))
            for left,right in cells:
                a,z = max(Q(0),left-start-elapsed), min(width,right-start-elapsed)
                if a >= z:
                    continue
                local_error += bound*(z-a)*price
                for mode in piece['modes']:
                    channel._require(mode['lambda'] == [0,0],
                                     'first-arrival measure consumes original polynomial residual curves')
                    for degree,encoded in enumerate(mode['coefficients']):
                        coefficient = channel._hermitian(channel._coefficient(encoded,quantum,kernel))
                        state = {(i,j):local.dipole.ComplexRadical(real,imag)
                                 for (count,i,j),(real,imag) in coefficient.items() if count == 0}
                        weight = width*((z/width)**(degree+1)-(a/width)**(degree+1))/(degree+1)
                        for key,value in self.jump_rate(state).items():
                            local._add(result,key,weight*value)
            elapsed += width
        # The stopped first-jump instrument contracts the input error once,
        # across the entire union, independently of the number of cells.
        inherited = Q(certificate['upstream_trace_norm_error']) if nonempty else Q(0)
        return {'schema':SCHEMA+'/first-arrival-measure','source_record':self.record(),
            'original_no_arrival_step':step,'source_time_cells':[[str(a),str(b)] for a,b in cells],
            'complete_poststate_center':channel._input_record(result),
            'global_trace_norm_error':str(inherited+local_error), 'local_curve_error':str(local_error),
            'input_error_paid_once_for_whole_time_instrument':str(inherited),
            'common_APD_jump_norm_upper':str(bound),'same_curve_first_APD_jump_rate_integrated':True,
            'source_arrival_time_mother_retained':True,'zero_width_cells_have_zero_instrument':True,
            'end_time_replaces_arrival_history':False,'actual_controller_policy_identified':False,
            'actual_hardware_uniquely_identified':False,'controller_advance':False}

    def verify_first_arrival_measure(self, report):
        _closed(self)
        channel._require(type(report) is dict and report.get('schema') == SCHEMA+'/first-arrival-measure' and
                         report.get('source_record') == self.record(),'same source first-arrival measure required')
        expected = self.first_arrival_measure(report['original_no_arrival_step'],report['source_time_cells'])
        channel._require(expected == report,'source arrival measure, whole error or time fibre changed')
        return True

    def stopped_arrival_instrument(self, step, cells=None):
        measure = self.first_arrival_measure(step,cells)
        certificate = step['original_threshold_one_certificate']
        old = Q(certificate['upstream_trace_norm_error'])
        endpoint_local = Q(certificate['trace_norm_error_bound'])-old
        rate_local = Q(measure['local_curve_error'])
        return {'schema':SCHEMA+'/stopped-arrival-instrument','source_record':self.record(),
            'no_arrival_terminal':{'complete_poststate_center':step['no_arrival_complete_poststate'],
                                   'memory':step['no_arrival_memory']},
            'first_arrival_time_measure':measure,
            'arrival_memory_recipe':'at each source arrival coordinate t, elapse the same incoming queue to t and append t once',
            'global_trace_norm_error':str(old+endpoint_local+rate_local),
            'whole_input_error_paid_once':str(old),'endpoint_local_error':str(endpoint_local),
            'integrated_first_arrival_local_error':str(rate_local),
            'first_arrival_state_is_at_arrival_not_at_interval_end':True,
            'multiple_arrival_terminal_branch_not_used_as_first_arrival_state':True,
            'actual_hardware_uniquely_identified':False,'controller_advance':False}

    def arrival_memory_at(self, measure, time):
        """Evaluate the memory fibre at a latent coordinate; do not choose it."""
        _closed(self)
        self.verify_first_arrival_measure(measure)
        time = full.exact(time)
        channel._require(any(Q(a) <= time <= Q(b) and Q(a) < Q(b)
                             for a,b in measure['source_time_cells']),
                         'arrival coordinate outside the retained source-time measure')
        record = measure['original_no_arrival_step']['incoming_memory']
        incoming = self.memory(record['source_relative_clock'],record['recent_arrival_times'])
        return self.append_arrival(self.elapse(incoming,time-incoming.clock))

    def retain_on_phase_change(self, memory, successor):
        """A new raw field phase keeps the same APD memory and physical unit."""
        _closed(self)
        _closed(successor)
        self.record()
        self._check_memory(memory)
        channel._require(type(successor) is APDWindowHistorySource, 'closed shared APD successor required')
        following = successor.record()
        original = self.record()['original_shared_source']
        target = following['original_shared_source']
        channel._require(successor.seconds_per_unit == self.seconds_per_unit and
                         successor.maximum_threshold == self.maximum_threshold and
                         target['background_rate'] == original['background_rate'] and
                         target['collection'] == original['collection'] and
                         all(a['gammas'] == b['gammas'] and a['radiation_regime'] == b['radiation_regime']
                             for a, b in zip(original['programmes'], target['programmes'])),
                         'phase change must preserve the same natural bath, APD, thresholds and clock')
        successor._check_memory(memory)
        return memory


_EXPECTED_EXECUTION = _execution_signature()
