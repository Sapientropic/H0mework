"""Original CEM physical outcome -> persistent native CP/time instrument.

The CEM completion creates a new confirmation epoch.  A retained PC-ready
label is confirmed for that epoch only by a subsequent source polling event.
The initial quantum coimage remains unnormalised.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import persistent_cem_source as cem
import persistent_reload_source as persistent
import atomic_dipole as dipole
import atomic_full_forward as full
import apd_window_history as apd
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint


SCHEMA = 'stage10-CEM-native-persistent-coimage/v1'
_copy, _digest, _require = persistent._copy, persistent._digest, persistent._require
_STATES, _SOURCES = set(), set()
_CEM_CHECKS = {}


def _code():
    return persistent._code() | {Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                                for module in (cem, channel.modes)} | {
        Path(__file__).name: hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


@dataclass(frozen=True)
class RawReturnPolicy:
    command: str = 'return-native'
    target_stage: str | None = None
    flag_updates: tuple = (None, None)
    phase_action: str = 'source_policy'

    def __post_init__(self):
        _require(self.command == 'return-native' and type(self.command) is str, 'original native return command required')
        _require(self.target_stage is None or type(self.target_stage) is str and self.target_stage,
                 'retain or an original named PC stage required; hidden occupancy is not a control')
        _require(type(self.flag_updates) is tuple and len(self.flag_updates) == 2 and
                 all(v is None or type(v) is bool for v in self.flag_updates), 'raw PC flag actions required')
        _require(self.phase_action in ('source_policy', 'retain', 'restart_at_return'), 'declared raw phase action required')

    def record(self):
        RawReturnPolicy.__post_init__(self)
        _require(type(self) is RawReturnPolicy and set(vars(self)) == {'command', 'target_stage', 'flag_updates', 'phase_action'},
                 'closed raw return policy required')
        return {'command': self.command, 'target_stage': self.target_stage,
                'flag_updates': list(self.flag_updates), 'phase_action': self.phase_action}

    @classmethod
    def from_record(cls, record):
        _require(cls is RawReturnPolicy and type(record) is dict and set(record) == {'command', 'target_stage', 'flag_updates', 'phase_action'},
                 'declared raw return policy, without hidden-occupancy decisions, required')
        return cls(record['command'], record['target_stage'], tuple(record['flag_updates']), record['phase_action'])


class NativeState:
    def __init__(self, *args, **kwargs):
        raise ValueError('CEM-source generated native state required; a target matrix is not input')

    def record(self):
        if _closed is not _CLOSED or _closed.__code__ is not _CLOSED_CODE:
            raise ValueError('native CEM execution closure changed')
        _closed()
        _require(type(self) is NativeState and set(vars(self)) == {'_frame', '_seal'} and self._seal in _STATES and
                 _digest(self._frame) == self._seal, 'native CEM coimage/state/callback changed')
        return _copy(self._frame)


def _issue(frame):
    state = object.__new__(NativeState)
    state._frame, state._seal = _copy(frame), _digest(frame)
    _STATES.add(state._seal)
    return state


def _checked_observation(source, certificate):
    raw = cem.PersistentCEMCell.record(source)
    key = _digest({'source': raw, 'certificate': certificate})
    if key not in _CEM_CHECKS:
        rebuilt = cem.PersistentCEMCell.from_record(raw)
        observation = cem.PersistentCEMCell.observe_cem(rebuilt, certificate)
        _CEM_CHECKS[key] = rebuilt, _copy(observation)
    rebuilt, observation = _CEM_CHECKS[key]
    _require(cem.PersistentCEMCell.record(rebuilt) == raw, 'verified CEM snapshot/source changed')
    return rebuilt, _copy(observation)


def _restore(frame, source=None):
    _require(type(frame) is dict, 'complete source-owned native state record required')
    _require(type(source) is NativeCEMCoimage, 'complete closed owner required; a state digest is not source authority')
    NativeCEMCoimage.record(source)
    _require(frame['coimage_owner_digest'] == source._seal, 'same native CEM source required')
    recipe = frame['source_recipe']
    if recipe['kind'] == 'CEM completion native coimage':
        state = NativeCEMCoimage.initial_state(source)
    elif recipe['kind'] == 'native CEM no-arrival CP next':
        inlet = _restore(recipe['incoming_state'], source)
        cert = recipe['certificate']
        unit = Q(frame['source_owner']['atomic_owner']['atomic_base']['seconds_per_unit'])
        _, state = NativeCEMCoimage.certify_step(source, inlet, cert['trial_pieces'],
                      duration_seconds=Q(recipe['cell_source']['duration'])*unit, **cert['precision'])
    elif recipe['kind'] == 'native CEM first-arrival density next':
        state = NativeCEMCoimage.arrival_next_at(source, recipe['mother_measure'], recipe['time_coordinate'])
    else:
        raise ValueError('native CEM state has no original source coimage')
    _require(NativeState.record(state) == frame, 'native CEM matrix, queue, PC, epoch or source changed')
    return state


def _confirm(owner, frame):
    clock = Q(frame['memory']['source_relative_clock'])
    result = persistent.PersistentReloadSource._poll(owner, frame)
    epoch = _copy(frame['confirmation_epoch'])
    epoch['native_polls_seen'] += 1
    epoch['last_native_poll'] = str(clock)
    ready = persistent.PersistentReloadSource._rule(owner, result['stage'])['ready']
    epoch['confirmed_at_last_poll'] = ready
    if ready and epoch['first_confirmed_at'] is None:
        epoch['first_confirmed_at'] = str(clock)
    result['confirmation_epoch'] = epoch
    return result


class NativeCEMCoimage:
    def __init__(self, source, certificate, clicks, *, return_policy=None):
        _closed()
        _require(type(source) is cem.PersistentCEMCell, 'closed original PersistentCEMCell required')
        _require(type(clicks) is tuple and len(clicks) == 2 and all(type(x) is int and x in (0, 1) for x in clicks),
                 'two original physical CEM observer bits required')
        return_policy = RawReturnPolicy() if return_policy is None else return_policy
        _require(type(return_policy) is RawReturnPolicy, 'closed declared raw return policy required')
        source, observation = _checked_observation(source, certificate)
        matches = [outcome for outcome in observation['complete_four_outcomes'] if tuple(outcome['clicks']) == clicks]
        _require(len(matches) == 1, 'unique original physical CEM outcome required')
        selected = matches[0]
        controls = _copy(observation['persistent_control_and_memory'])
        owner = persistent.PersistentReloadSource.from_record(controls['source_owner'])
        policy = RawReturnPolicy.record(return_policy)
        old_stage = controls['stage']
        if policy['target_stage'] is not None:
            persistent.PersistentReloadSource._rule(owner, policy['target_stage'])
            controls['stage'] = policy['target_stage']
        controls['loaded_flags'] = [old if new is None else new for old, new in zip(controls['loaded_flags'], policy['flag_updates'])]
        clock = controls['memory']['source_relative_clock']
        if policy['phase_action'] == 'restart_at_return' or (policy['phase_action'] == 'source_policy' and
                old_stage != controls['stage'] and controls['source_owner']['phase_policy'] == 'restart_on_stage_change'):
            controls['phase_started_at'] = clock
        controls['field_mode'], controls['field_settings'], controls['field_started_at'] = 'native', None, clock
        quantum = channel._initial(channel._read_input(selected['poststate'], joint.DIMENSION), joint.DIMENSION)
        error = Q(observation['global_trace_norm_error'])
        centre_trace, radical = full.radical_midpoint(joint._trace(quantum).real, 160)
        normalizer = {'centre': str(centre_trace), 'radical_trace_error': str(radical), 'source_error': str(error),
                      'interval': [str(max(Q(0), centre_trace-error-radical)), str(max(Q(0), centre_trace+error+radical))],
                      'positive_lower_certified': centre_trace-error-radical > 0,
                      'caller_normalizer_used': False, 'state_normalized': False}
        self._frame = {'schema': SCHEMA, 'CEM_cell': cem.PersistentCEMCell.record(source), 'CEM_certificate': _copy(certificate),
                       'original_CEM_observation': observation, 'physical_clicks': list(clicks), 'raw_return_policy': policy,
                       'native_control_and_memory': controls, 'native_quantum_coimage': selected['poststate'],
                       'upstream_trace_norm_error': str(error), 'source_trace_normalizer': normalizer,
                       'CEM_occurrence': _digest({'cell': cem.PersistentCEMCell.record(source), 'certificate': certificate, 'clicks': list(clicks)}),
                       'source_code': _code(), 'CEM_background_reapplied': False, 'queue_reset': False,
                       'PC_decision_reads_hidden_occupancy': False, 'input_target_quantum_state': False,
                       'actual_return_policy_identified': False, 'controller_advance': False}
        self._seal = _digest(self._frame)
        _SOURCES.add(self._seal)

    def record(self):
        if _closed is not _CLOSED or _closed.__code__ is not _CLOSED_CODE:
            raise ValueError('native CEM execution closure changed')
        _closed()
        _require(type(self) is NativeCEMCoimage and set(vars(self)) == {'_frame', '_seal'} and self._seal in _SOURCES and
                 _digest(self._frame) == self._seal and self._frame['source_code'] == _code(), 'native CEM source snapshot/callback changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls, record):
        _closed()
        _require(cls is NativeCEMCoimage and type(record) is dict and record.get('schema') == SCHEMA, 'closed native CEM source record required')
        source = cem.PersistentCEMCell.from_record(record['CEM_cell'])
        result = cls(source, record['CEM_certificate'], tuple(record['physical_clicks']),
                     return_policy=RawReturnPolicy.from_record(record['raw_return_policy']))
        _require(NativeCEMCoimage.record(result) == record, 'CEM/native hardware, observer, return command or price changed')
        return result

    def initial_state(self):
        record = NativeCEMCoimage.record(self)
        frame = _copy(record['native_control_and_memory'])
        frame.update(quantum_centre=record['native_quantum_coimage'], global_error=record['upstream_trace_norm_error'],
                     coimage_owner_digest=self._seal, source_recipe={'kind': 'CEM completion native coimage'},
                     confirmation_epoch={'CEM_occurrence': record['CEM_occurrence'], 'activated_at': frame['memory']['source_relative_clock'],
                       'native_polls_seen': 0, 'last_native_poll': None, 'confirmed_at_last_poll': False, 'first_confirmed_at': None},
                     quantum_coimage_is_unnormalized=True, literal_cohort_reconstructed=False)
        return _issue(frame)

    def _state(self, state):
        _require(type(state) is NativeState, 'new source-owned NativeState required; old PersistentState is not a CEM coimage')
        frame = NativeState.record(state)
        NativeCEMCoimage.record(self)
        _require(frame['coimage_owner_digest'] == self._seal, 'native coimage belongs to another CEM occurrence or return source')
        owner = persistent.PersistentReloadSource.from_record(frame['source_owner'])
        persistent._read_memory(persistent.PersistentReloadSource._apd(owner), frame['memory'])
        persistent.PersistentReloadSource._rule(owner, frame['stage'])
        return frame

    def cell_source(self, state, duration):
        frame = NativeCEMCoimage._state(self, state)
        owner = persistent.PersistentReloadSource.from_record(frame['source_owner'])
        return persistent.PersistentReloadSource._cell(owner, frame, duration)

    def certify_step(self, state, pieces, *, duration_seconds=None, mode_bits=60, coefficient_bits=160, exponential_bits=160):
        record = NativeCEMCoimage.record(self)
        frame = NativeCEMCoimage._state(self, state)
        owner = persistent.PersistentReloadSource.from_record(frame['source_owner'])
        unit = Q(frame['source_owner']['atomic_owner']['atomic_base']['seconds_per_unit'])
        clock = Q(frame['memory']['source_relative_clock'])
        poll = persistent.PersistentReloadSource._next_poll(owner, clock)
        width = min(Q(frame['source_owner']['maximum_cell_seconds'])/unit, poll-clock)
        if duration_seconds is not None:
            proposed = full.nonnegative(duration_seconds)/unit
            _require(0 < proposed <= width, 'native CEM cell crosses its source cell or PC boundary')
            width = proposed
        cell = persistent.PersistentReloadSource._cell(owner, frame, width)
        precision = dict(mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        certificate = persistent._curve(cell, channel._read_input(frame['quantum_centre'], joint.DIMENSION), pieces, Q(frame['global_error']), precision)
        following = _copy(frame)
        shared = apd.APDWindowHistorySource.from_record(cell['APD_source'])
        memory = apd.APDWindowHistorySource.elapse(shared, persistent._read_memory(shared, frame['memory']), width)
        following['memory'] = memory.record()
        following['quantum_centre'], following['global_error'] = certificate['no_arrival_poststate'], certificate['global_terminal_error']
        at_poll = memory.clock == poll
        if at_poll:
            following = _confirm(owner, following)
        following['source_recipe'] = {'kind': 'native CEM no-arrival CP next', 'incoming_state': frame,
                                      'cell_source': cell, 'certificate': certificate}
        next_state = _issue(following)
        return {'schema': SCHEMA+'/event-step', 'source_record': record, 'incoming_state': frame, 'cell_source': cell,
                'capture_APD_certificate': certificate, 'no_arrival_next_state': NativeState.record(next_state),
                'native_PC_poll_occurred': at_poll, 'new_confirmation_epoch': following['confirmation_epoch'],
                'source_old_model_local_error_paid_once': True, 'CEM_bits_reapplied': False, 'queue_reset': False,
                'controller_advance': False}, next_state

    def verify_step(self, report):
        _require(type(report) is dict and report.get('schema') == SCHEMA+'/event-step' and
                 report['source_record'] == NativeCEMCoimage.record(self), 'same native CEM event-step required')
        initial = _restore(report['incoming_state'], self)
        cert = report['capture_APD_certificate']
        unit = Q(report['incoming_state']['source_owner']['atomic_owner']['atomic_base']['seconds_per_unit'])
        expected, _ = NativeCEMCoimage.certify_step(self, initial, cert['trial_pieces'],
                       duration_seconds=Q(report['cell_source']['duration'])*unit, **cert['precision'])
        _require(expected == report, 'native CEM CP action, queue, confirmation, model price or source changed')
        return True

    def first_arrival_measure(self, step, time_cells=None):
        NativeCEMCoimage.verify_step(self, step)
        cell, cert = step['cell_source'], step['capture_APD_certificate']
        start = Q(step['incoming_state']['memory']['source_relative_clock'])
        stop = start+Q(cell['duration'])
        cells = ((start, stop),) if time_cells is None else tuple(tuple(map(full.exact, c)) for c in time_cells)
        _require(all(len(c) == 2 and start <= c[0] <= c[1] <= stop for c in cells) and
                 all(a[1] <= b[0] for a,b in zip(cells,cells[1:])), 'ordered disjoint native source time restrictions required')
        detector = apd.APDWindowHistorySource.from_record(cell['APD_source'])
        kernel = persistent.SourceKernel(cell, cert['precision']['coefficient_bits'])
        rate = sum(max(atom.outgoing) for atom in detector._raw.sources)+detector._raw.background_rate
        quantum, elapsed, price, error, result = 1 << cert['precision']['mode_bits'], Q(0), Q(cert['initial_radical_error']), Q(0), {}
        for piece, paid in zip(cert['trial_pieces'], cert['piece_error_records']):
            width = Q(piece['duration'])
            price += sum(Q(paid[k]) for k in ('initial_join_error','source_residual_error','radical_coefficient_error','scalar_exponential_error'))
            for left,right in cells:
                a,z = max(Q(0),left-start-elapsed), min(width,right-start-elapsed)
                if a >= z:
                    continue
                error += rate*(z-a)*price
                for mode in piece['modes']:
                    _require(mode['lambda'] == [0,0], 'native APD time measure requires original polynomial residual curves')
                    for degree,encoded in enumerate(mode['coefficients']):
                        raw = channel._hermitian(channel._coefficient(encoded,quantum,kernel))
                        matrix = {(i,j):dipole.ComplexRadical(r,s) for (c,i,j),(r,s) in raw.items() if c == 0}
                        weight = width*((z/width)**(degree+1)-(a/width)**(degree+1))/(degree+1)
                        for key,value in apd.APDWindowHistorySource.jump_rate(detector,matrix).items():
                            local._add(result,key,weight*value)
            elapsed += width
        inherited = Q(cert['upstream_after_model']) if any(a < b for a,b in cells) else Q(0)
        return {'schema':SCHEMA+'/first-arrival-measure','event_step':step,'source_time_cells':[[str(a),str(b)] for a,b in cells],
                'complete_event_poststate':channel._input_record(result),'global_trace_norm_error':str(inherited+error),
                'old_and_model_error_once':str(inherited),'local_curve_error':str(error),'source_jump_norm_upper':str(rate),
                'queue_at_time_recipe':'elapse the original CEM queue to s, append s once; confirm only at a subsequent raw native poll',
                'terminal_at_least_one_poststate_used':False,'controller_advance':False}

    def arrival_next_at(self, measure, time):
        step, time = measure['event_step'], full.exact(time)
        _require(NativeCEMCoimage.first_arrival_measure(self, step, measure['source_time_cells']) == measure, 'same native CEM time mother required')
        _require(any(Q(a) <= time <= Q(b) and Q(a)<Q(b) for a,b in measure['source_time_cells']), 'arrival outside native CEM source time measure')
        cell,cert = step['cell_source'],step['capture_APD_certificate']
        start = Q(step['incoming_state']['memory']['source_relative_clock'])
        kernel = persistent.SourceKernel(cell,cert['precision']['coefficient_bits'])
        quantum,elapsed,matrix = 1 << cert['precision']['mode_bits'],Q(0),{}
        for piece in cert['trial_pieces']:
            width = Q(piece['duration'])
            if elapsed <= time-start <= elapsed+width:
                u = (time-start-elapsed)/width
                for mode in piece['modes']:
                    _require(mode['lambda']==[0,0], 'native APD density requires the same polynomial witness')
                    for degree,encoded in enumerate(mode['coefficients']):
                        raw = channel._hermitian(channel._coefficient(encoded,quantum,kernel))
                        for (count,i,j),(r,s) in raw.items():
                            if count==0:
                                local._add(matrix,(i,j),dipole.ComplexRadical(r,s)*u**degree)
                break
            elapsed += width
        frame = _copy(step['incoming_state'])
        owner = persistent.PersistentReloadSource.from_record(frame['source_owner'])
        detector = apd.APDWindowHistorySource.from_record(cell['APD_source'])
        memory = persistent._read_memory(detector,frame['memory'])
        at_poll = time == persistent.PersistentReloadSource._next_poll(owner,memory.clock)
        memory = apd.APDWindowHistorySource.elapse(detector,memory,time-memory.clock)
        frame['memory'] = memory.record()
        if at_poll and frame['source_owner']['arrival_poll_order']=='poll_then_arrival':
            frame = _confirm(owner,frame)
        frame['memory'] = apd.APDWindowHistorySource.append_arrival(detector,memory).record()
        frame['quantum_centre'] = channel._input_record(apd.APDWindowHistorySource.jump_rate(detector,matrix))
        frame['global_error'] = str(Q(measure['source_jump_norm_upper'])*Q(cert['global_terminal_error']))
        if at_poll and frame['source_owner']['arrival_poll_order']=='arrival_then_poll':
            frame = _confirm(owner,frame)
        frame['source_recipe'] = {'kind':'native CEM first-arrival density next','mother_measure':measure,'time_coordinate':str(time)}
        frame['state_is_rate_density'] = True
        return _issue(frame)

    def stopped_instrument(self, step, time_cells=None):
        measure = NativeCEMCoimage.first_arrival_measure(self,step,time_cells)
        cert = step['capture_APD_certificate']
        old = Q(cert['upstream_after_model'])
        local_endpoint = Q(cert['global_terminal_error'])-old
        return {'schema':SCHEMA+'/stopped-instrument','event_step':step,'no_arrival_next_state':step['no_arrival_next_state'],
                'first_arrival_time_measure':measure,'whole_old_and_model_error_once':str(old),
                'endpoint_local_error':str(local_endpoint),'time_local_error':measure['local_curve_error'],
                'global_trace_norm_error':str(old+local_endpoint+Q(measure['local_curve_error'])),
                'whole_trace_preserving_on_full_time_cell':time_cells is None,'CEM_background_reapplied':False,
                'input_target_state_or_normalizer':False,'controller_advance':False}


def _signature():
    functions = (_code,_issue,_checked_observation,_restore,_confirm,_signature,_closed,RawReturnPolicy.__init__,RawReturnPolicy.__post_init__,
        RawReturnPolicy.record,RawReturnPolicy.from_record.__func__,NativeState.record,NativeCEMCoimage.__init__,
        NativeCEMCoimage.record,NativeCEMCoimage.from_record.__func__,NativeCEMCoimage.initial_state,NativeCEMCoimage._state,
        NativeCEMCoimage.cell_source,NativeCEMCoimage.certify_step,NativeCEMCoimage.verify_step,
        NativeCEMCoimage.first_arrival_measure,NativeCEMCoimage.arrival_next_at,NativeCEMCoimage.stopped_instrument,
        cem.PersistentCEMCell.record,cem.PersistentCEMCell.from_record.__func__,cem.PersistentCEMCell.observe_cem,
        cem.PersistentCEMCell.verify,cem.PersistentCEMCell.certify,cem._read_marked,
        channel._read_input,channel._input_record,channel._initial,channel._coefficient,channel._hermitian,
        joint._trace,local._add,full.radical_midpoint,full.exact,full.nonnegative)
    return (tuple((id(f),id(f.__code__)) for f in functions),_copy,_digest,_require,joint.DIMENSION,dipole.ION,
            tuple(dipole.STATES),tuple(dipole.INDEX.items()))


def _closed():
    if not (_closed is _CLOSED and _closed.__code__ is _CLOSED_CODE and _signature is _SIGNATURE and
            _signature.__code__ is _SIGNATURE_CODE and _signature()==_EXPECTED):
        raise ValueError('native CEM execution closure changed')
    persistent._guard()
    cem._guard()


_CLOSED,_CLOSED_CODE = _closed,_closed.__code__
_SIGNATURE,_SIGNATURE_CODE = _signature,_signature.__code__
_EXPECTED = _signature()
