"""Source-generated recurrent joint reload, with complete ready and pending faces.

The numerical face is the existing stage/shared-counter/full-matrix coimage.
The source carrier retains its literal CEM histories and the complete operation
recipe; a projected ready matrix does not recover a literal atom cohort.
"""
from fractions import Fraction as Q
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import cem_pair_source as cem
import fluorescence_channel as channel
import joint_reload_source as reload
import receipt_triggered_programme as response


SCHEMA = 'stage10-recurrent-joint-reload-programme/v1'


def _add(target, source):
    for key, value in source.items():
        current = target.get(key, dipole.ComplexRadical()) + value
        if current:
            target[key] = current
        else:
            target.pop(key, None)


def _trace(matrix):
    value = sum((v for (i, j), v in matrix.items() if i == j), dipole.ComplexRadical())
    channel._require(not value.imag, 'Hermitian source trace required')
    center, error = full.radical_midpoint(value.real, 160)
    return center, error


def _coarsened_record(source, initial):
    native = source.intake(initial)
    groups = {}
    for (history, counter, i, j), value in native.items():
        key = tuple(channel._canonical(cem.history_record(h)) for h in history.traps)
        groups.setdefault(key, {})[i, j] = dipole.complex_exact(value)
    for matrix in groups.values():
        channel._initial(matrix, reload.DIMENSION)
    return [{'trap_histories': [json.loads(h) for h in key],
             'initial_counter': 0, 'matrix': channel._input_record(matrix)}
            for key, matrix in sorted(groups.items())]


def _read_coarsened(records):
    channel._require(type(records) is list, 'complete original CEM input groups required')
    result = {}
    for item in records:
        channel._require(set(item) == {'trap_histories', 'initial_counter', 'matrix'} and item['initial_counter'] == 0,
                         'literal reset-counter CEM input required')
        histories = tuple(response._read_history(h) for h in item['trap_histories'])
        channel._require(len(histories) == 2, 'two original source histories required')
        for (i, j), value in channel._read_input(item['matrix'], reload.DIMENSION).items():
            key = histories, 0, i, j
            channel._require(key not in result, 'duplicate original CEM input coordinate')
            result[key] = value
    return result


def taylor_trials(source, stage, matrix, *, order=6, mode_bits=60, coefficient_bits=160):
    """Untrusted polynomial proposal; the original residual checker prices it."""
    channel._require(type(order) is int and 0 <= order <= 32, 'finite trial order in [0,32] required')
    kernel = reload.SourceKernel(source, coefficient_bits, stage=stage)
    width, quantum = source._window(stage).duration, 1 << mode_bits
    coefficients = {(0, i, j): tuple(full.radical_midpoint(part, coefficient_bits)[0]
                    for part in (value.real, value.imag)) for (i, j), value in matrix.items()}
    polynomial = []
    for degree in range(order+1):
        polynomial.append([[c, i, j, round(a*quantum), round(b*quantum)]
                           for (c, i, j), (a, b) in sorted(coefficients.items())
                           if round(a*quantum) or round(b*quantum)])
        coefficients = {key: (a*width/(degree+1), b*width/(degree+1))
                        for key, (a, b) in kernel.action(coefficients).items()}
    return [{'duration': str(width), 'modes': [{'lambda': [0, 0], 'coefficients': polynomial}]}]


class JointReloadProgramme:
    def __init__(self, source, *, seconds_per_unit):
        channel._require(type(source) is reload.JointReloadSource, 'closed original joint reload source required')
        self.source = reload.JointReloadSource.from_record(source.record())
        self.seconds_per_unit = full.exact(seconds_per_unit)
        channel._require(self.seconds_per_unit > 0, 'positive source physical time unit required')

    def record(self):
        return {'schema': SCHEMA, 'raw_source': self.source.record(),
                'seconds_per_source_unit': str(self.seconds_per_unit),
                'public_presence_integration_seconds': str(Q(1, 25)),
                'all_raw_windows_match_public_40ms': all(w.duration*self.seconds_per_unit == Q(1, 25)
                                                        for w in self.source.windows),
                'time_reader': 'sum of generated raw integrated-count window durations',
                'numeric_carrier': 'source stage and complete 1089-dimensional pair matrix',
                'native_carrier': 'literal original CEM histories and source window/decision recipe',
                'ready_semantics': 'recognized saturated counts; not actual double occupancy',
                'fuel_semantics': 'finite observation of recurrent source; all pending mass retained',
                'cohort_recovered_from_numeric_projection': False, 'Unix_or_UID_time_used': False,
                'actual_hardware_uniquely_identified': False, 'controller_advance': False}

    @classmethod
    def from_record(cls, record):
        channel._require(type(record) is dict and record.get('schema') == SCHEMA, 'registered recurrent source required')
        result = cls(reload.JointReloadSource.from_record(record['raw_source']),
                     seconds_per_unit=record['seconds_per_source_unit'])
        channel._require(result.record() == record, 'recurrent source identity or scope changed')
        return result

    def run(self, initial, *, windows, input_error=0, start_time=0, trial_provider=None,
            taylor_order=6, mode_bits=60, coefficient_bits=160, exponential_bits=160):
        channel._require(type(windows) is int and windows >= 0, 'finite nonnegative window observation required')
        source_record = self.record()
        source = reload.JointReloadSource.from_record(source_record['raw_source'])
        physical_unit = Q(source_record['seconds_per_source_unit'])
        native = source.intake(initial)
        original = _coarsened_record(source, initial)
        projected = source.forget_history(native)
        matrix = {}
        for (stage, counter, i, j), value in projected.items():
            channel._require(stage == 0 and counter == 0, 'original post-CEM diagnostic input required')
            _add(matrix, {(i, j): value})
        channel._initial(matrix, reload.DIMENSION)
        clock, inherited = full.exact(start_time), full.nonnegative(input_error)
        channel._require(clock >= 0, 'nonnegative original source time required')
        pending, ready, steps = {(0, clock): matrix}, {}, []
        local_error = Q(0)
        for depth in range(windows):
            following, level = {}, []
            for (stage, begin), state in sorted(pending.items()):
                if not state:
                    continue
                pieces = (taylor_trials(source, stage, state, order=taylor_order, mode_bits=mode_bits,
                                       coefficient_bits=coefficient_bits) if trial_provider is None else
                          trial_provider(depth, stage, begin, dict(state)))
                report = reload.certify_window(source, state, pieces, stage=stage, upstream_error=0,
                          mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
                end = begin + Q(report['duration'])
                local_error += Q(report['trace_norm_error_bound'])
                endpoint = {(stage, c, i, j): dipole.ComplexRadical(Q(a), Q(b))
                            for c, i, j, a, b in report['counter_poststate_center']}
                branch_states = source.projected_window_end(endpoint)
                for values in branch_states.values():
                    for (next_stage, counter, i, j), value in values.items():
                        if next_stage == reload.READY:
                            target = ready.setdefault(end, {})
                            _add(target, {(i, j): value})
                        else:
                            channel._require(counter == 0, 'source pending boundary resets its counter')
                            target = following.setdefault((next_stage, end), {})
                            _add(target, {(i, j): value})
                level.append({'depth': depth, 'stage': stage, 'start_time': str(begin), 'end_time': str(end),
                              'certificate': report,
                              'native_operation': {'window': reload.WINDOW_AT[stage],
                                 'retain_each_source_count': list(range(source._window(stage).threshold+1)),
                                 'low_next': source._next(stage, False), 'high_next': source._next(stage, True),
                                 'capture_enabled': list(reload.CAPTURE_AT[stage])}})
            steps.append(level)
            pending = following
        total = {}
        for state in (*ready.values(), *pending.values()):
            _add(total, state)
        input_mass, input_radical = _trace(matrix)
        total_mass, total_radical = _trace(total)
        global_error = inherited + local_error
        channel._require(abs(total_mass-input_mass) <= local_error+input_radical+total_radical,
                         'source ready/pending complete mass enclosure excludes initial trace')
        def face(stage, time, state):
            mass, radical = _trace(state)
            return {'stage': stage, 'source_time': str(time),
                    'source_time_support': [str(time), str(time)],
                    'physical_time_seconds': str(time*physical_unit),
                    'physical_time_support_seconds': [str(time*physical_unit)]*2,
                    'complete_matrix': channel._input_record(state),
                    'trace_center': str(mass),
                    'trace_bounds_using_shared_error': [str(mass-global_error-radical), str(mass+global_error+radical)]}
        return {'schema': SCHEMA, 'source_record': source_record, 'original_coarsened_input': original,
                'windows_observed': windows, 'start_time': str(clock), 'input_error': str(inherited),
                'steps': steps, 'ready': [face(reload.READY, t, s) for t, s in sorted(ready.items())],
                'pending': [face(stage, t, s) for (stage, t), s in sorted(pending.items())],
                'input_trace_center': str(input_mass), 'ready_plus_pending_trace_center': str(total_mass),
                'local_residual_error': str(local_error), 'global_trace_norm_error': str(global_error),
                'precision': [mode_bits, coefficient_bits, exponential_bits],
                'whole_upstream_error_paid_once': True, 'full_native_input_and_operation_recipe_retained': True,
                'all_pending_branches_retained': True, 'fuel_exhaustion_is_stop': False,
                'ready_implies_actual_double_occupancy': False, 'literal_cohorts_recovered_from_projection': False,
                'physical_probability_interpretation_requires_positive_input': True,
                'solver_reexecuted_by_checker': False, 'actual_hardware_uniquely_identified': False,
                'controller_advance': False}

    def verify(self, report, *, initial=None, input_error=None):
        channel._require(type(report) is dict and report.get('source_record') == self.record(),
                         'same recurrent joint source required')
        raw = _read_coarsened(report['original_coarsened_input']) if initial is None else initial
        inherited = report['input_error'] if input_error is None else input_error
        fresh = type(self).from_record(report['source_record'])
        cursor = iter(item for level in report['steps'] for item in level)
        def trials(depth, stage, clock, matrix):
            item = next(cursor, None)
            channel._require(item is not None and (item['depth'], item['stage'], Q(item['start_time'])) ==
                             (depth, stage, clock), 'same generated source window order required')
            return item['certificate']['trial_pieces']
        bits, coefficient_bits, exponential_bits = report['precision']
        expected = fresh.run(raw, windows=report['windows_observed'], input_error=inherited,
                  start_time=report['start_time'], trial_provider=trials, mode_bits=bits,
                  coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        channel._require(next(cursor, None) is None and expected == report, 'complete recurrent source certificate mismatch')
        return True
