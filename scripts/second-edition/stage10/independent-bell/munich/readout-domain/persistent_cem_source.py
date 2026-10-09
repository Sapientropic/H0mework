"""Joint accepted-fragment and APD instrument of a source-issued SI inlet.

The four fragment marks specify acceptance at the original logic deadlines.
They are latent until the CEM observation; an APD arrival does not read them.
Each SI cell stops at its first APD event or the next source boundary.
Both branches retain the fragment state, queue and PC control together.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import apd_window_history as apd
import munich_atomic_programme as atomic
import persistent_reload_source as persistent
import window_cem_source as window


SCHEMA = 'stage10-persistent-SI-CEM-APD-cell/v1'
ZERO = dipole.ComplexRadical()


def _copy(value):
    return json.loads(channel._canonical(value))


def _bindings():
    return {Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
            for module in (dipole, full, channel, local, joint, apd, atomic, persistent, window)} | {
            Path(__file__).name: hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


def _marked_record(matrix):
    return [[mark, i, j, value.serialize()] for (mark, i, j), value in sorted(matrix.items())]


def _read_marked(record):
    channel._require(type(record) is list, 'complete four-mark matrix record required')
    result = {}
    for item in record:
        channel._require(type(item) is list and len(item) == 4, 'four-mark source coordinate required')
        mark, i, j, raw = item
        channel._key((mark, i, j), joint.DIMENSION, 3)
        channel._require((mark, i, j) not in result, 'duplicate marked coordinate')
        value = channel._complex_record(raw)
        channel._require(bool(value), 'canonical nonzero marked coordinate required')
        result[mark, i, j] = value
    channel._require(_marked_record(result) == record and
                     all(result.get((mark, j, i), ZERO) == value.conjugate()
                         for (mark, i, j), value in result.items()),
                     'canonical Hermitian complete four-mark matrix required')
    return result


def forget_fragments(matrix):
    result = {}
    for (mark, i, j), value in matrix.items():
        channel._key((mark, i, j), joint.DIMENSION, 3)
        local._add(result, (i, j), value)
    return result


class _JointProjection:
    def __init__(self, cell):
        self.record_value = _copy(cell)
        self.raw = apd.APDWindowHistorySource.from_record(cell['physical_cell']['APD_source'])
        channel._require(apd.APDWindowHistorySource.record(self.raw) == cell['physical_cell']['APD_source'],
                         'the loaded APD source must retain its complete original record')
        self.counter = apd.APDWindowHistorySource.first_arrival_source(self.raw)
        self.window_phase = window.WindowCEMPhase.from_record(cell['window_phase'])
        channel._require(window.WindowCEMPhase.record(self.window_phase) == cell['window_phase'],
                         'the loaded CEM phase must retain its complete original record')
        self.dimension, self.threshold, self.duration = joint.DIMENSION, 7, Q(cell['duration'])

    def record(self):
        return _copy(self.record_value)

    def action(self, matrix):
        blocks, result = {}, {}
        for (address, i, j), value in matrix.items():
            channel._key((address, i, j), self.dimension, self.threshold)
            arrival, mark = divmod(address, 4)
            local._add(blocks.setdefault(mark, {}), (arrival, i, j), value)
        for mark, block in blocks.items():
            for (arrival, i, j), value in self.counter.action(block).items():
                local._add(result, (4*arrival+mark, i, j), value)
            # Ion birth is already in the physical GKSL.  Only its gain is
            # split into accepted/unaccepted fragments, without reionizing.
            for arrival, state in self.counter._blocks(block).items():
                for side, kappa in enumerate(self.window_phase.kappas):
                    target = window.mark_index(window.index_mark(mark).with_click(side))
                    for (i, j), value in self.window_phase.ion_birth_action(state, side).items():
                        local._add(result, (4*arrival+mark, i, j), -kappa*value)
                        local._add(result, (4*arrival+target, i, j), kappa*value)
        return result


class SourceKernel(channel.SourceKernel):
    def __init__(self, source, coefficient_bits=160):
        channel._require(type(source) is PersistentCEMCell, 'closed common SI cell required; arbitrary G is not input')
        channel._require(type(coefficient_bits) is int and 64 <= coefficient_bits <= 512,
                         'registered coefficient precision required')
        record = PersistentCEMCell.record(source)
        self.source = _JointProjection(record)
        self.dimension, self.threshold, self.bits = joint.DIMENSION, 7, coefficient_bits
        self.columns, self.exact_columns, self.errors = {}, {}, {}


class PersistentCEMCell:
    def __init__(self, owner, inlet, *, duration_seconds=None):
        channel._require(type(owner) is persistent.PersistentReloadSource and
                         type(inlet) is persistent.PersistentState,
                         'same closed persistent source and source-issued SI inlet required')
        frame = persistent.PersistentReloadSource._state(owner, inlet)
        clock = Q(frame['memory']['source_relative_clock'])
        channel._require(frame['field_mode'] == 'SI' and clock == Q(frame['field_started_at']),
                         'original SI entry required; a later target marked state is not input')
        PersistentCEMCell._assemble(self, owner, frame, None, None, duration_seconds)

    def _assemble(self, owner, frame, initial, parent, duration_seconds):
        clock = Q(frame['memory']['source_relative_clock'])
        atomic_owner = atomic.MunichAtomicProgramme.from_record(frame['source_owner']['atomic_owner'])
        source, model = atomic.MunichAtomicProgramme.si_window_source(atomic_owner, tuple(frame['field_settings']))
        elapsed = clock-Q(frame['field_started_at'])
        channel._require(0 <= elapsed < source.duration, 'joint SI cell begins outside its original logic interval')
        index = next(i for i, item in enumerate(source.partition) if
                     Q(item['interval_start']) <= elapsed < Q(item['interval_start'])+Q(item['duration']))
        phase = source.phase(index)
        unit = source.seconds_per_unit
        width = min(phase.interval_start+phase.duration-elapsed, Q(frame['source_owner']['maximum_cell_seconds'])/unit,
                    persistent.PersistentReloadSource._next_poll(owner, clock)-clock)
        if duration_seconds is not None:
            proposed = full.nonnegative(duration_seconds)/unit
            channel._require(0 < proposed <= width, 'SI cell crosses a waveform, window or PC boundary')
            width = proposed
        cell = persistent.PersistentReloadSource._cell(owner, frame, width)
        raw = joint.JointCounterGenerator.from_record(cell['APD_source']['original_shared_source'])
        for side in (0, 1):
            expected = phase.sources[side].program.record()
            expected['duration'] = str(width)
            channel._require(raw.sources[side].program.record() == expected,
                             'CEM and APD must act on the same original SI waveform')
        channel._require(cell['capture_enabled'] == [False, False], 'SI source must retain capture-off control')
        self._record = {'schema': SCHEMA, 'source_inlet': frame, 'duration': str(width),
            'source_parent': parent, 'continued_initial_marked_state': None if initial is None else _marked_record(initial),
            'physical_cell': cell, 'window_phase': phase.record(), 'SI_model_source': model,
            'source_bindings': _bindings(), 'source_initial_mark': [0, 0],
            'state_space': 'two first-arrival blocks times four accepted-fragment blocks times full33 pair',
            'fragment_mark_is_an_observed_arrival': False, 'initial_APD_queue_reset': False,
            'CEM_background_applied_before_logic_cutoff': False,
            'actual_initial_control_identified': False, 'controller_advance': False}
        self._seal = channel._digest(self._record)

    def record(self):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('common SI execution guard changed')
        _guard()
        channel._require(type(self) is PersistentCEMCell and set(vars(self)) == {'_record', '_seal'} and
                         channel._digest(self._record) == self._seal and self._record['source_bindings'] == _bindings(),
                         'common SI cell or callback changed')
        return _copy(self._record)

    @classmethod
    def from_record(cls, record):
        _guard()
        channel._require(cls is PersistentCEMCell and type(record) is dict and record.get('schema') == SCHEMA,
                         'closed common SI cell record required')
        frame = record['source_inlet']
        unit = Q(frame['source_owner']['atomic_owner']['atomic_base']['seconds_per_unit'])
        if record['source_parent'] is None:
            owner = persistent.PersistentReloadSource.from_record(frame['source_owner'])
            state = persistent._restore_state(frame)
            result = cls(owner, state, duration_seconds=Q(record['duration'])*unit)
        else:
            parent = record['source_parent']
            source = cls.from_record(parent['certificate']['source_cell'])
            result = PersistentCEMCell.successor(source, parent['certificate'],
                       measure=parent['arrival_measure'], time=parent['arrival_time'],
                       duration_seconds=Q(record['duration'])*unit)
        channel._require(PersistentCEMCell.record(result) == record, 'CEM, APD, SI inlet or clock source changed')
        return result

    def _initial(self):
        record = PersistentCEMCell.record(self)
        if record['source_parent'] is not None:
            return _read_marked(record['continued_initial_marked_state'])
        frame = record['source_inlet']
        return {(0, i, j): value for (i, j), value in
                channel._read_input(frame['quantum_centre'], joint.DIMENSION).items()}

    def jump_rate(self, marked):
        _guard()
        raw = _JointProjection(PersistentCEMCell.record(self)).raw
        blocks, result = {}, {}
        for (mark, i, j), value in marked.items():
            channel._key((mark, i, j), joint.DIMENSION, 3)
            local._add(blocks.setdefault(mark, {}), (i, j), value)
        for mark, block in blocks.items():
            for (i, j), value in apd.APDWindowHistorySource.jump_rate(raw, block).items():
                local._add(result, (mark, i, j), value)
        return result

    def _fibre(self, marked, time, error, *, arrival):
        frame = PersistentCEMCell.record(self)['source_inlet']
        owner = persistent.PersistentReloadSource.from_record(frame['source_owner'])
        detector = _JointProjection(PersistentCEMCell.record(self)).raw
        memory = persistent._read_memory(detector, frame['memory'])
        at_poll = time == persistent.PersistentReloadSource._next_poll(owner, memory.clock)
        memory = apd.APDWindowHistorySource.elapse(detector, memory, time-memory.clock)
        frame['memory'] = memory.record()
        if arrival and at_poll and frame['source_owner']['arrival_poll_order'] == 'poll_then_arrival':
            frame = persistent.PersistentReloadSource._poll(owner, frame)
        if arrival:
            memory = apd.APDWindowHistorySource.append_arrival(detector, memory)
            frame['memory'] = memory.record()
        frame['quantum_centre'] = channel._input_record(forget_fragments(marked))
        frame['global_error'] = str(error)
        if at_poll and (not arrival or frame['source_owner']['arrival_poll_order'] == 'arrival_then_poll'):
            frame = persistent.PersistentReloadSource._poll(owner, frame)
        controls = {key: frame[key] for key in ('source_owner', 'memory', 'stage', 'loaded_flags',
                    'field_mode', 'field_settings', 'field_started_at', 'phase_started_at')}
        return {'schema': SCHEMA+'/time-fibre', 'source_cell': PersistentCEMCell.record(self),
                'accepted_fragment_poststate': _marked_record(marked), 'persistent_control_and_memory': controls,
                'global_trace_norm_error': str(error), 'time_coordinate': str(time),
                'state_is_rate_density': arrival, 'CEM_logic_bits_observed': False,
                'fragment_mark_forgotten_in_next_source': False, 'queue_has_invented_timestamp': False}

    def certify(self, pieces, *, mode_bits=60, coefficient_bits=160, exponential_bits=160):
        window._precisions(mode_bits, coefficient_bits, exponential_bits)
        record, initial = PersistentCEMCell.record(self), PersistentCEMCell._initial(self)
        centre, rounding = window._center(initial, coefficient_bits)
        old = Q(record['source_inlet']['global_error'])
        norm = sum((persistent.bsm._entry_norm({(i, j): value}, bits=coefficient_bits)
                    for (mark, i, j), value in initial.items()), Q(0))
        model = Q(record['physical_cell']['source_model_delta'])*norm
        error, elapsed, paid = old+model+rounding, Q(0), []
        kernel = SourceKernel(self, coefficient_bits)
        channel._require(type(pieces) is list, 'complete untrusted common SI curve required')
        for piece in pieces:
            width, begin, end, prices, diagnostics = channel._piece(kernel, piece, mode_bits, exponential_bits)
            gap = channel._difference(begin, centre)
            error += gap+sum(prices.values(), Q(0))
            elapsed += width
            channel._require(elapsed <= kernel.source.duration, 'joint SI curve crosses its source boundary')
            paid.append({'duration': str(width), 'initial_join_error': str(gap),
                         **{key: str(value) for key, value in prices.items()}, 'modes': diagnostics})
            centre = end
        channel._require(elapsed == kernel.source.duration, 'joint SI curve must cover its whole cell')
        marked = {(address, i, j): dipole.ComplexRadical(a, b)
                  for (address, i, j), (a, b) in centre.items() if address < 4}
        time = Q(record['source_inlet']['memory']['source_relative_clock'])+elapsed
        return {'schema': SCHEMA+'/certificate', 'source_cell': record,
                'trial_pieces': _copy(pieces), 'precision': dict(mode_bits=mode_bits,
                coefficient_bits=coefficient_bits, exponential_bits=exponential_bits),
                'initial_radical_error': str(rounding), 'piece_error_records': paid,
                'old_error_before_model': str(old), 'source_model_payment': str(model),
                'upstream_after_model': str(old+model), 'global_terminal_error': str(error),
                'complete_counter_fragment_centre': [[c, i, j, str(a), str(b)] for (c, i, j), (a, b) in sorted(centre.items())],
                'no_APD_fragment_poststate': _marked_record(marked),
                'no_APD_time_fibre': PersistentCEMCell._fibre(self, marked, time, error, arrival=False),
                'source_columns_checked': len(kernel.columns), 'absent_coordinates_priced': True,
                'CEM_background_applied': False, 'old_and_model_paid_once': True}

    def verify(self, certificate):
        record = PersistentCEMCell.record(self)
        channel._require(type(certificate) is dict and certificate.get('schema') == SCHEMA+'/certificate' and
                         certificate.get('source_cell') == record, 'same joint SI certificate required')
        expected = PersistentCEMCell.certify(self, certificate['trial_pieces'], **certificate['precision'])
        channel._require(expected == certificate, 'joint SI source, curve, mark, queue or price changed')
        return True

    def first_arrival_measure(self, certificate, cells=None):
        PersistentCEMCell.verify(self, certificate)
        record = PersistentCEMCell.record(self)
        start = Q(record['source_inlet']['memory']['source_relative_clock'])
        stop = start+Q(record['duration'])
        cells = ((start, stop),) if cells is None else tuple(tuple(map(full.exact, c)) for c in cells)
        channel._require(all(len(c) == 2 and start <= c[0] <= c[1] <= stop for c in cells) and
                         all(a[1] <= b[0] for a, b in zip(cells, cells[1:])),
                         'ordered disjoint source APD time cells required')
        raw = _JointProjection(record).counter
        rate_bound = sum(max(atom.outgoing) for atom in raw.sources)+raw.background_rate
        kernel = SourceKernel(self, certificate['precision']['coefficient_bits'])
        quantum = 1 << certificate['precision']['mode_bits']
        price, elapsed, local_error, result = Q(certificate['initial_radical_error']), Q(0), Q(0), {}
        for piece, paid in zip(certificate['trial_pieces'], certificate['piece_error_records']):
            width = Q(piece['duration'])
            price += sum(Q(paid[key]) for key in ('initial_join_error', 'source_residual_error',
                         'radical_coefficient_error', 'scalar_exponential_error'))
            for left, right in cells:
                a, z = max(Q(0), left-start-elapsed), min(width, right-start-elapsed)
                if a >= z:
                    continue
                local_error += rate_bound*(z-a)*price
                for mode in piece['modes']:
                    channel._require(mode['lambda'] == [0, 0], 'APD measure consumes the common polynomial residual curve')
                    for degree, encoded in enumerate(mode['coefficients']):
                        curve = channel._hermitian(channel._coefficient(encoded, quantum, kernel))
                        state = {(address, i, j): dipole.ComplexRadical(r, s)
                                 for (address, i, j), (r, s) in curve.items() if address < 4}
                        weight = width*((z/width)**(degree+1)-(a/width)**(degree+1))/(degree+1)
                        for key, value in PersistentCEMCell.jump_rate(self, state).items():
                            local._add(result, key, weight*value)
            elapsed += width
        inherited = Q(certificate['upstream_after_model']) if any(a < b for a, b in cells) else Q(0)
        return {'schema': SCHEMA+'/first-APD-measure', 'certificate': certificate,
                'source_time_cells': [[str(a), str(b)] for a, b in cells],
                'complete_fragment_poststate': _marked_record(result), 'global_trace_norm_error': str(inherited+local_error),
                'whole_old_and_model_error_once': str(inherited), 'local_curve_error': str(local_error),
                'common_APD_jump_norm_upper': str(rate_bound), 'CEM_logic_bits_observed': False,
                'arrival_queue_recipe': 'at the same latent time s: elapse incoming queue, append s once',
                'terminal_at_least_one_branch_used_as_first_arrival': False}

    def arrival_fibre_at(self, measure, time):
        expected = PersistentCEMCell.first_arrival_measure(self, measure['certificate'], measure['source_time_cells'])
        channel._require(measure == expected, 'same marked APD mother measure required')
        time = full.exact(time)
        channel._require(any(Q(a) <= time <= Q(b) and Q(a) < Q(b) for a, b in measure['source_time_cells']),
                         'APD time outside its marked mother measure')
        cert, record = measure['certificate'], PersistentCEMCell.record(self)
        kernel = SourceKernel(self, cert['precision']['coefficient_bits'])
        quantum = 1 << cert['precision']['mode_bits']
        relative = time-Q(record['source_inlet']['memory']['source_relative_clock'])
        elapsed, marked = Q(0), {}
        for piece in cert['trial_pieces']:
            width = Q(piece['duration'])
            if elapsed <= relative <= elapsed+width:
                u = (relative-elapsed)/width
                for mode in piece['modes']:
                    channel._require(mode['lambda'] == [0, 0], 'APD density consumes the common polynomial curve')
                    for degree, encoded in enumerate(mode['coefficients']):
                        curve = channel._hermitian(channel._coefficient(encoded, quantum, kernel))
                        for (address, i, j), (r, s) in curve.items():
                            if address < 4:
                                local._add(marked, (address, i, j), dipole.ComplexRadical(r, s)*u**degree)
                break
            elapsed += width
        rate = PersistentCEMCell.jump_rate(self, marked)
        error = Q(measure['common_APD_jump_norm_upper'])*Q(cert['global_terminal_error'])
        fibre = PersistentCEMCell._fibre(self, rate, time, error, arrival=True)
        fibre['source_recipe'] = {'kind': 'same marked SI first-APD density', 'mother_measure': measure,
                                 'time_coordinate': str(time)}
        return fibre

    def stopped_instrument(self, certificate, cells=None):
        measure = PersistentCEMCell.first_arrival_measure(self, certificate, cells)
        old = Q(certificate['upstream_after_model'])
        endpoint = Q(certificate['global_terminal_error'])-old
        return {'schema': SCHEMA+'/stopped-instrument', 'certificate': certificate,
                'no_APD_time_fibre': certificate['no_APD_time_fibre'], 'first_APD_time_measure': measure,
                'global_trace_norm_error': str(old+endpoint+Q(measure['local_curve_error'])),
                'whole_old_and_model_error_once': str(old), 'endpoint_local_error': str(endpoint),
                'integrated_arrival_local_error': measure['local_curve_error'],
                'whole_trace_preserving_on_full_time_cell': cells is None,
                'accepted_fragment_state_and_APD_history_jointly_retained': True,
                'CEM_logic_observation_completed': False, 'controller_advance': False}

    def successor(self, certificate, *, measure=None, time=None, duration_seconds=None):
        PersistentCEMCell.verify(self, certificate)
        channel._require((measure is None) == (time is None), 'APD successor requires its mother measure and exact latent time together')
        if measure is None:
            fibre = certificate['no_APD_time_fibre']
        else:
            channel._require(type(measure) is dict and measure.get('certificate') == certificate,
                             'APD successor must belong to the same joint SI cell')
            fibre = PersistentCEMCell.arrival_fibre_at(self, measure, time)
        record = PersistentCEMCell.record(self)
        frame = _copy(record['source_inlet'])
        frame.update(fibre['persistent_control_and_memory'])
        marked = _read_marked(fibre['accepted_fragment_poststate'])
        frame['quantum_centre'] = channel._input_record(forget_fragments(marked))
        frame['global_error'] = fibre['global_trace_norm_error']
        frame['source_recipe'] = {'kind': 'joint SI source restriction', 'parent_cell_digest': channel._digest(record)}
        owner = persistent.PersistentReloadSource.from_record(frame['source_owner'])
        parent = {'certificate': _copy(certificate), 'arrival_measure': None if measure is None else _copy(measure),
                  'arrival_time': None if time is None else str(full.exact(time))}
        result = object.__new__(PersistentCEMCell)
        PersistentCEMCell._assemble(result, owner, frame, marked, parent, duration_seconds)
        return result

    def observe_cem(self, certificate):
        PersistentCEMCell.verify(self, certificate)
        record = PersistentCEMCell.record(self)
        owner = atomic.MunichAtomicProgramme.from_record(record['source_inlet']['source_owner']['atomic_owner'])
        source, _ = atomic.MunichAtomicProgramme.si_window_source(owner, tuple(record['source_inlet']['field_settings']))
        fibre = certificate['no_APD_time_fibre']
        clock = Q(fibre['time_coordinate'])
        channel._require(clock-Q(record['source_inlet']['field_started_at']) == source.duration,
                         'original CEM logic interval must finish before its observation')
        initial = _read_marked(fibre['accepted_fragment_poststate'])
        marked = {(window.index_mark(mark), i, j): value for (mark, i, j), value in initial.items()}
        final = window.WindowCEMSource.background_action(source, marked)
        error, outcomes = Q(certificate['global_terminal_error']), []
        for mark in window.MARKS:
            poststate = {(i, j): value for (candidate, i, j), value in final.items() if candidate == mark}
            centre = {key: (value.real.as_rational(), value.imag.as_rational()) for key, value in poststate.items()}
            outcomes.append({'clicks': list(mark.clicks), 'poststate': channel._input_record(poststate),
                             'trace': channel._observation(centre, error)})
        return {'schema': SCHEMA+'/CEM-observation', 'certificate': certificate,
                'complete_four_outcomes': outcomes, 'global_trace_norm_error': str(error),
                'persistent_control_and_memory': fibre['persistent_control_and_memory'],
                'CEM_background_applied_once': True, 'fragment_registration_reapplied': False,
                'APD_time_word': 'source_parent preserves every preceding latent APD coordinate',
                'arrival_queue_reset': False, 'PC_stage_reset': False, 'controller_advance': False}


def _signature():
    functions = (_copy, _bindings, _marked_record, _read_marked, forget_fragments, _signature, _guard,
        _JointProjection.__init__, _JointProjection.record, _JointProjection.action, SourceKernel.__init__,
        PersistentCEMCell.__init__, PersistentCEMCell._assemble, PersistentCEMCell.record, PersistentCEMCell.from_record.__func__,
        PersistentCEMCell._initial, PersistentCEMCell.jump_rate, PersistentCEMCell._fibre,
        PersistentCEMCell.certify, PersistentCEMCell.verify, PersistentCEMCell.first_arrival_measure,
        PersistentCEMCell.arrival_fibre_at, PersistentCEMCell.stopped_instrument,
        PersistentCEMCell.successor, PersistentCEMCell.observe_cem, window.WindowCEMSource.background_action,
        persistent.PersistentReloadSource.record, persistent.PersistentReloadSource._state,
        persistent.PersistentReloadSource._cell, persistent.PersistentReloadSource._poll,
        persistent._restore_state, atomic.MunichAtomicProgramme.si_window_source,
        window.WindowCEMPhase.ion_birth_action, apd.APDWindowHistorySource.jump_rate,
        apd.APDWindowHistorySource.from_record.__func__, window.WindowCEMPhase.from_record.__func__,
        apd.APDWindowHistorySource.first_arrival_source, joint.JointCounterGenerator.action,
        channel.SourceKernel.column, channel.SourceKernel.action, channel._piece, channel._coefficient,
        channel._hermitian, window._center, persistent.bsm._entry_norm)
    return tuple((id(f), id(f.__code__)) for f in functions)


def _guard():
    if not (_signature is _SIGNATURE and _signature.__code__ is _SIGNATURE_CODE and _signature() == _EXPECTED):
        raise ValueError('common SI execution closure changed')


_SIGNATURE = _signature
_SIGNATURE_CODE = _signature.__code__
_GUARD_FUNCTION = _guard
_GUARD_CODE = _guard.__code__
_EXPECTED = _signature()
