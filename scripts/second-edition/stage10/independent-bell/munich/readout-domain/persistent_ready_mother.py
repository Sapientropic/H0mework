"""First PC-ready measure of the persistent capture/shared-APD source.

The complete arrival word remains in the time-ordered source measure.  A
capped counter is used only to check its first-poll quantum marginal.  That
marginal never becomes a queue with guessed arrival times.
"""
from fractions import Fraction as Q
import hashlib
from pathlib import Path

import persistent_reload_source as persistent
import atomic_dipole as dipole
import atomic_full_forward as full
import apd_window_history as apd
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import joint_reload_resolvent as native
import trap_reload_source as trap


SCHEMA = 'stage10-persistent-first-PC-ready-mother/v1'
MAX_EXPANDED_BITS = 4096
_ISSUED = set()
_copy = persistent._copy
_digest = persistent._digest
_require = persistent._require


def _code():
    paths = (Path(__file__), Path(persistent.__file__), Path(native.__file__),
             Path(native.background.__file__), Path(native.reload.__file__), Path(channel.modes.__file__))
    return {**persistent._code(), **{p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}


def _unit(record):
    return Q(record['atomic_owner']['atomic_base']['seconds_per_unit'])


def _positive_input_mass(frame):
    """Source coimages give an upper mass without normalising their centres."""
    recipe = frame['source_recipe']
    if recipe['kind'] == 'source-owned basis primitive':
        return Q(1), True
    if recipe['kind'] == 'raw field change identity CP action':
        return _positive_input_mass(recipe['incoming_state'])
    if recipe['kind'] == 'APD-count PC successor':
        recipe = recipe['parent']
    if recipe['kind'] == 'capture-on no-APD branch':
        mass, _ = _positive_input_mass(recipe['cell_source']['incoming_state'])
        return mass, False
    if recipe['kind'] == 'source first-arrival density next':
        step = recipe['mother_measure']['event_step']
        mass, _ = _positive_input_mass(step['incoming_state'])
        detector = apd.APDWindowHistorySource.from_record(step['cell_source']['APD_source'])
        rate = sum(max(atom.outgoing) for atom in detector._raw.sources) + detector._raw.background_rate
        return mass * rate, False
    raise ValueError('source positive input genealogy required')


def _capture_law(records):
    result = []
    for side, record in enumerate(records):
        capture = trap.ReloadSource.from_record(record)
        entries = []
        for ground in trap.GROUND:
            amplitude = capture.couplings[ground] * dipole.sqrt_rational(capture.occupations[ground])
            expected = {(dipole.INDEX[ground], dipole.ION): amplitude} if amplitude else {}
            _require(capture.birth_operators[ground] == expected, 'raw source capture jump changed')
            loss = dipole.matrix_product(dipole.matrix_adjoint(expected), expected)
            coupling = capture.couplings[ground]
            rate = capture.occupations[ground] * (coupling.real*coupling.real + coupling.imag*coupling.imag)
            _require(loss == ({(dipole.ION, dipole.ION): dipole.ComplexRadical(rate)} if rate else {}),
                     'raw capture loss/recycling trace identity failed')
            entries.append({'ground': dipole.INDEX[ground], 'jump': channel._input_record(expected),
                            'loss': channel._input_record(loss)})
        result.append({'side': side, 'source_jumps': entries, 'observed_APD_jump': False})
    return result


def _dyadic_exponent(value):
    _require(0 < value <= 1, 'strict source path probability lower bound required')
    n, d = value.numerator, value.denominator
    exponent = max(0, d.bit_length() - n.bit_length())
    if n << exponent < d:
        exponent += 1
    return exponent


def _contraction(record, frame):
    rules = {r['name']: r for r in record['rules']}
    reachable, pending = set(), [frame['stage']]
    while pending:
        stage = pending.pop()
        if stage in reachable:
            continue
        reachable.add(stage)
        if not rules[stage]['ready']:
            pending.extend((rules[stage]['low_next'], rules[stage]['high_next']))
    paths, failed = {}, []
    for stage in sorted(reachable):
        path, current = [], stage
        while not rules[current]['ready'] and current not in path:
            path.append(current)
            current = rules[current]['high_next']
        if not rules[current]['ready']:
            failed.append(stage)
        else:
            paths[stage] = path + [current]
    unit = _unit(record)
    source = persistent.PersistentReloadSource.from_record(record)
    shared = persistent.PersistentReloadSource._apd(source)
    rate = shared._raw.background_rate
    clock = Q(frame['memory']['source_relative_clock'])
    first_gap = persistent.PersistentReloadSource._next_poll(source, clock) - clock
    period = Q(record['poll_period_seconds']) / unit
    window = shared.window
    width = min(first_gap, period, window) / 2
    threshold = max(rules[s]['threshold'] for s in reachable)
    length = max((len(path) - 1 for path in paths.values()), default=0)
    positive = not failed and rate > 0
    poll_exponent = _dyadic_exponent(rate * width / (threshold + rate * width)) * threshold if rate > 0 else None
    exponent = poll_exponent * length if positive else None
    delta = Q(1, 1 << exponent) if exponent is not None and exponent <= MAX_EXPANDED_BITS else None
    return {'reachable_stages': sorted(reachable), 'all_high_paths': paths, 'failed_high_paths': failed,
            'raw_BG_rate_per_source_unit': str(rate), 'seconds_per_source_unit': str(unit),
            'public_rolling_window_source_units': str(window), 'forcing_interval_width': str(width),
            'count_threshold_cover': threshold, 'block_polls': length,
            'strong_stopping_contract': positive, 'delta_dyadic_exponent': exponent,
            'forcing_one_poll_dyadic_exponent': poll_exponent,
            'initial_all_high_path_polls': len(paths[frame['stage']])-1 if frame['stage'] in paths else None,
            'delta_lower': str(delta) if delta is not None else None,
            'delta_expression': None if exponent is None else {'numerator': 1, 'denominator_power_of_two': exponent},
            'BG_path_rule': 'each of N disjoint subintervals has a BG arrival at every poll on the all-high path',
            'scalar_inequality': '1-exp(-x) >= x/(1+x); replace each rational lower bound by a dyadic lower bound',
            'extra_optical_arrivals_cannot_erase_rolling_count': True,
            'capture_is_unobserved_CPTP': _capture_law(record['capture_sources']),
            'no_hidden_occupancy_control': record['control_reads_only'],
            'normalizer_is_not_input': True}


def _compile(record, initial):
    source = persistent.PersistentReloadSource.from_record(record)
    start = Q(initial['memory']['source_relative_clock'])
    stop = persistent.PersistentReloadSource._next_poll(source, start)
    shared = persistent.PersistentReloadSource._apd(source)
    gate = max(start, stop - shared.window)
    maximum = Q(record['maximum_cell_seconds']) / _unit(record)
    cuts, elapsed = [start], start
    while elapsed < stop:
        following = min(stop, elapsed + maximum)
        if elapsed < gate < following:
            following = gate
        cuts.append(following)
        elapsed = following
    cells = []
    for a, b in zip(cuts, cuts[1:]):
        frame = _copy(initial)
        memory = persistent._read_memory(shared, initial['memory'])
        frame['memory'] = apd.APDWindowHistorySource.elapse(shared, memory, a - start).record()
        cell = persistent.PersistentReloadSource._cell(source, frame, b - a)
        cells.append({'start': str(a), 'stop': str(b), 'count_before_cell_is_forgotten': a == gate and gate > start,
                      'persistent_cell': cell})
    survivors = [t for t in initial['memory']['recent_arrival_times'] if stop - shared.window < Q(t) <= stop]
    return cells, {'start': str(start), 'poll': str(stop), 'new_arrival_count_gate': str(gate),
                   'surviving_old_arrival_word': survivors, 'half_open_window': '(poll-40ms,poll]'}


class _CountProjection:
    def __init__(self, cell, threshold):
        original = apd.APDWindowHistorySource.from_record(cell['APD_source'])._raw
        record = original.record()
        record['threshold'], record['counter_levels'] = threshold, threshold + 1
        self.raw = joint.JointCounterGenerator.from_record(record)
        self.captures = tuple(trap.ReloadSource.from_record(r) for r in cell['capture_sources'])
        self.enabled = tuple(cell['capture_enabled'])
        self.duration, self.threshold = self.raw.duration, threshold

    def action(self, state):
        answer = self.raw.action(state)
        for count, block in self.raw._blocks(state).items():
            for key, value in persistent._capture_action(block, self.captures, self.enabled).items():
                local._add(answer, (count, *key), value)
        return answer


class ReadyCounterKernel(channel.SourceKernel):
    def __init__(self, mother, cell_index, coefficient_bits=160):
        record = PersistentReadyMother.record(mother)
        _require(type(cell_index) is int and 0 <= cell_index < len(record['compiled_first_poll_cells']), 'source cell index required')
        _require(type(coefficient_bits) is int and 64 <= coefficient_bits <= 512, 'registered coefficient precision required')
        threshold = record['initial_poll_rule']['threshold']
        self.source = _CountProjection(record['compiled_first_poll_cells'][cell_index]['persistent_cell'], threshold)
        self.dimension, self.threshold, self.bits = joint.DIMENSION, threshold, coefficient_bits
        self.columns, self.exact_columns, self.errors = {}, {}, {}


def _initial_centre(frame, bits):
    initial = channel._initial(channel._read_input(frame['quantum_centre'], joint.DIMENSION), joint.DIMENSION)
    result, rounding = {}, Q(0)
    for (i, j), value in initial.items():
        a, da = full.radical_midpoint(value.real, bits)
        b, db = full.radical_midpoint(value.imag, bits)
        channel._add(result, (0, i, j), a, b)
        rounding += da + db
    return result, rounding


def _counter_record(state):
    return [[c, i, j, str(a), str(b)] for (c, i, j), (a, b) in sorted(state.items())]


class PersistentReadyMother:
    def __init__(self, source, state):
        _guard()
        _require(type(source) is persistent.PersistentReloadSource and type(state) is persistent.PersistentState,
                 'closed persistent source and its source-issued coimage required')
        record = persistent.PersistentReloadSource.record(source)
        initial = persistent.PersistentReloadSource._state(source, state)
        persistent._restore_state(initial)
        _require(initial['field_mode'] == 'native', 'first-ready mother requires the native persistent field')
        cells, geometry = _compile(record, initial)
        rule = persistent.PersistentReloadSource._rule(source, initial['stage'])
        _require(not rule['ready'], 'first-ready inlet must precede the PC ready event')
        mass, normalized = _positive_input_mass(initial)
        contraction = _contraction(record, initial)
        first_raw = _CountProjection(cells[0]['persistent_cell'], rule['threshold']).raw
        self._frame = {'schema': SCHEMA, 'persistent_source': record, 'incoming_state': initial,
                       'initial_poll_rule': rule, 'compiled_first_poll_cells': cells, 'first_poll_geometry': geometry,
                       'source_CPTP_law': native._window_law(first_raw), 'stopping': contraction,
                       'positive_source_input_mass_upper': str(mass), 'normalized_source_input': normalized,
                       'complete_future_is_normalized': normalized and contraction['strong_stopping_contract'],
                       'whole_time_measure_recipe': {
                           'kind': 'first entry into PC-ready, from the same quantum and arrival-word source',
                           'incoming_quantum_and_time_coimage': initial,
                           'no_arrival': 'time-ordered original common atomic GKSL + enabled capture - D_shared - BG*identity',
                           'arrival': 'original D_shared + one independent BG identity jump; capture is unobserved',
                           'arrival_word': 'at each latent s append s; retain the last N with t-40ms<s<=t',
                           'poll': 'only at raw polling lattice, inspect original rolling count and follow low/high PC edge',
                           'ready': 'stop at the first resulting rule.ready; integrate full poststate on the same arrival simplex',
                           'optical_phase': record['phase_policy'], 'arrival_poll_order': record['arrival_poll_order'],
                           'all_finite_arrival_words_and_all_poll_indices': True,
                           'input_target_ready_matrix': False},
                       'source_code': _code(), 'controller_advance': False,
                       'actual_initial_history_or_PC_policy_identified': False}
        self._seal = _digest(self._frame)
        _ISSUED.add(self._seal)

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('first-ready source execution closure changed')
        _guard()
        persistent._guard()
        _require(type(self) is PersistentReadyMother and set(vars(self)) == {'_frame', '_seal'} and
                 self._seal in _ISSUED and _digest(self._frame) == self._seal and self._frame['source_code'] == _code(),
                 'first-ready source snapshot/callback changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls, record):
        _require(cls is PersistentReadyMother and type(record) is dict and record.get('schema') == SCHEMA,
                 'closed first-ready source record required')
        source = persistent.PersistentReloadSource.from_record(record['persistent_source'])
        state = persistent._restore_state(record['incoming_state'])
        result = cls(source, state)
        _require(PersistentReadyMother.record(result) == record, 'first-ready source/control/time identity changed')
        return result

    def tail_upper(self, polls):
        record = PersistentReadyMother.record(self)
        _require(type(polls) is int and polls >= 0, 'nonnegative finite raw poll count required')
        stopping = record['stopping']
        if not stopping['strong_stopping_contract']:
            return {'upper': record['positive_source_input_mass_upper'], 'vanishing_tail': False, 'polls': polls}
        blocks = polls // stopping['block_polls']
        exponent = stopping['delta_dyadic_exponent']
        bound = Q(1) if not blocks else (Q(1, 1 + blocks * Q(stopping['delta_lower'])) if stopping['delta_lower'] is not None else None)
        single_exponent = stopping['forcing_one_poll_dyadic_exponent']
        if polls >= 1 and stopping['initial_all_high_path_polls'] == 1 and single_exponent <= MAX_EXPANDED_BITS:
            first_bound = 1 - Q(1, 1 << single_exponent)
            bound = first_bound if bound is None else min(bound, first_bound)
        mass = Q(record['positive_source_input_mass_upper'])
        return {'upper': str(mass * bound) if bound is not None else None, 'polls': polls, 'complete_blocks': blocks,
                'vanishing_tail': True, 'strict_Bernoulli_expression': {'input_mass_upper': str(mass),
                 'numerator_power_of_two': exponent, 'denominator': '2^exponent + complete_blocks'},
                'numerical_first_ready_measure_extended': False}

    def certify_first_poll(self, witness, *, mode_bits=60, coefficient_bits=160, exponential_bits=160):
        record = PersistentReadyMother.record(self)
        _require(type(witness) is list and len(witness) == len(record['compiled_first_poll_cells']),
                 'one untrusted complete curve per source cell required; ready matrix is not input')
        _require(type(mode_bits) is int and 32 <= mode_bits <= 256 and type(exponential_bits) is int and
                 64 <= exponential_bits <= 1024, 'registered mode/scalar precision required')
        centre, local_error = _initial_centre(record['incoming_state'], coefficient_bits)
        old = Q(record['incoming_state']['global_error'])
        paid, model_total = [], Q(0)
        for index, (source_cell, pieces) in enumerate(zip(record['compiled_first_poll_cells'], witness)):
            _require(type(pieces) is list, 'untrusted source-cell curve pieces required')
            kernel = ReadyCounterKernel(self, index, coefficient_bits)
            if source_cell['count_before_cell_is_forgotten']:
                reset = {}
                for (_, i, j), (a, b) in centre.items():
                    channel._add(reset, (0, i, j), a, b)
                centre = reset
            model = Q(source_cell['persistent_cell']['source_model_delta']) * channel._entry_norm(centre)
            model_total += model
            local_error += model
            elapsed, prices = Q(0), []
            for piece in pieces:
                width, begin, end, errors, diagnostics = channel._piece(kernel, piece, mode_bits, exponential_bits)
                gap = channel._difference(begin, centre)
                local_error += gap + sum(errors.values(), Q(0))
                elapsed += width
                _require(elapsed <= kernel.source.duration, 'first-poll curve exceeds raw source cell')
                prices.append({'duration': str(width), 'initial_join_error': str(gap),
                               **{k: str(v) for k, v in errors.items()}, 'modes': diagnostics})
                centre = end
            _require(elapsed == kernel.source.duration, 'first-poll curve must cover the entire source cell')
            paid.append({'source_model_payment': str(model), 'piece_errors': prices,
                         'source_columns_checked': len(kernel.columns)})
        old_count = len(record['first_poll_geometry']['surviving_old_arrival_word'])
        rule = record['initial_poll_rule']
        rules = {r['name']: r for r in record['persistent_source']['rules']}
        ready, pending, count_faces = {}, {}, []
        for count in range(rule['threshold'] + 1):
            matrix = {(i, j): dipole.ComplexRadical(a, b) for (c, i, j), (a, b) in centre.items() if c == count}
            high = old_count + count >= rule['threshold']
            stage = rule['high_next'] if high else rule['low_next']
            changes = rule['high_flags'] if high else rule['low_flags']
            flags = [before if after is None else after for before, after in zip(record['incoming_state']['loaded_flags'], changes)]
            branch = ready if rules[stage]['ready'] else pending
            for key, value in matrix.items():
                local._add(branch, key, value)
            count_faces.append({'capped_new_count': count, 'rolling_count_at_least_threshold': high,
                                'PC_stage': stage, 'loaded_flags': flags, 'PC_ready': rules[stage]['ready'],
                                'poststate': channel._input_record(matrix)})
        tail = PersistentReadyMother.tail_upper(self, 1)
        physical_tail = (Q(tail['upper']) if tail['upper'] is not None else
                         Q(record['positive_source_input_mass_upper']))
        return {'schema': SCHEMA + '/first-poll-and-whole-mother', 'source_record': record, 'untrusted_curves': _copy(witness),
                'precision': {'mode_bits': mode_bits, 'coefficient_bits': coefficient_bits, 'exponential_bits': exponential_bits},
                'source_cell_prices': paid, 'first_poll_counter_poststate': _counter_record(centre), 'count_faces': count_faces,
                'generated_first_ready_poststate': channel._input_record(ready), 'first_poll_pending_poststate': channel._input_record(pending),
                'upstream_error_once': str(old), 'source_model_payment': str(model_total), 'new_local_error': str(local_error),
                'first_poll_joint_error': str(old + local_error), 'source_generated_remaining_mass_upper': str(physical_tail),
                'remaining_mass_source_tail': tail,
                'whole_future_ready_centre': channel._input_record(ready), 'whole_future_ready_error': str(old + local_error + physical_tail),
                'whole_future_time_mother': record['whole_time_measure_recipe'], 'whole_stopping': record['stopping'],
                'time_resolved_numerical_measure_certified': False, 'first_poll_marginal_used_as_queue': False,
                'old_error_applied_to_whole_absorption_once': True, 'capture_or_arrival_declared_ready': False,
                'ready_is_PC_confirmation_not_double_occupancy': True, 'controller_advance': False}

    def verify(self, report):
        _require(type(report) is dict and report.get('schema') == SCHEMA + '/first-poll-and-whole-mother' and
                 report['source_record'] == PersistentReadyMother.record(self), 'same first-ready mother required')
        expected = PersistentReadyMother.certify_first_poll(self, report['untrusted_curves'], **report['precision'])
        _require(expected == report, 'first-ready quantum/time/control/price report changed')
        return True

    def ready_matrix(self, report):
        PersistentReadyMother.verify(self, report)
        return channel._read_input(report['whole_future_ready_centre'], joint.DIMENSION), Q(report['whole_future_ready_error'])

    def certify_history(self, word, witnesses, *, mode_bits=60, coefficient_bits=160, exponential_bits=160):
        record = PersistentReadyMother.record(self)
        _require(type(word) is list and word and type(witnesses) is list and len(word) == len(witnesses),
                 'finite original no-arrival/arrival word and source curves required')
        source = persistent.PersistentReloadSource.from_record(record['persistent_source'])
        # The constructor independently replayed this coimage.  Only the sealed
        # snapshot is reissued here, never a caller-supplied matrix or PC state.
        state = persistent._issue(record['incoming_state'])
        steps, arrivals, first_ready = [], 0, None
        for index, (event, curve) in enumerate(zip(word, witnesses)):
            _require(type(event) is dict and (set(event) == {'kind'} and event['kind'] == 'no_arrival' or
                     set(event) == {'kind', 'source_time'} and event['kind'] == 'arrival'),
                     'only original no-arrival or latent source-time arrival is admitted')
            step, no_arrival = persistent.PersistentReloadSource.certify_step(source, state, curve,
                         mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
            if event['kind'] == 'no_arrival':
                state = no_arrival
                measure = None
            else:
                time = full.exact(event['source_time'])
                start = Q(step['incoming_state']['memory']['source_relative_clock'])
                _require(time > start, 'arrival word times must strictly advance the source clock')
                measure = persistent.PersistentReloadSource.first_arrival_measure(source, step)
                state = persistent.PersistentReloadSource.arrival_next_at(source, measure, time)
                arrivals += 1
            frame = persistent.PersistentState.record(state)
            rules = {r['name']: r for r in record['persistent_source']['rules']}
            is_ready = rules[frame['stage']]['ready']
            steps.append({'original_CP_step': step, 'first_arrival_time_mother': measure,
                          'generated_next': frame, 'first_PC_ready': is_ready})
            if is_ready:
                _require(index == len(word)-1, 'first-ready word must stop at its first PC-ready occurrence')
                first_ready = frame['memory']['source_relative_clock']
        following = persistent.PersistentState.record(state)
        return {'schema': SCHEMA + '/time-history-fibre', 'source_record': record,
                'latent_event_word': _copy(word), 'untrusted_source_curves': _copy(witnesses),
                'precision': {'mode_bits': mode_bits, 'coefficient_bits': coefficient_bits, 'exponential_bits': exponential_bits},
                'source_CP_steps': steps, 'generated_next_state': following,
                'generated_ready_poststate': following['quantum_centre'] if first_ready is not None else None,
                'global_error': following['global_error'], 'first_ready_source_time': first_ready,
                'number_of_density_arrival_coordinates': arrivals,
                'state_is_time_density': arrivals > 0, 'ready_was_decided_only_at_source_poll': True,
                'one_fibre_is_not_the_integrated_whole_mother': True,
                'actual_arrival_archive_reconstructed': False, 'controller_advance': False}

    def verify_history(self, report):
        _require(type(report) is dict and report.get('schema') == SCHEMA + '/time-history-fibre' and
                 report['source_record'] == PersistentReadyMother.record(self), 'same whole first-ready time mother required')
        expected = PersistentReadyMother.certify_history(self, report['latent_event_word'],
                    report['untrusted_source_curves'], **report['precision'])
        _require(expected == report, 'first-ready source time/queue/CP history changed')
        return True


def _signature():
    functions = (_code, _unit, _positive_input_mass, _capture_law, _dyadic_exponent, _contraction, _compile,
                 _initial_centre, _counter_record, _signature, _guard,
                 PersistentReadyMother.__init__, PersistentReadyMother.record, PersistentReadyMother.from_record.__func__,
                 PersistentReadyMother.tail_upper, PersistentReadyMother.certify_first_poll, PersistentReadyMother.verify,
                 PersistentReadyMother.ready_matrix, PersistentReadyMother.certify_history, PersistentReadyMother.verify_history,
                 ReadyCounterKernel.__init__, _CountProjection.__init__, _CountProjection.action,
                 native._window_law, native.background._atomic_law, native.background._schur,
                 channel.SourceKernel.column, channel.SourceKernel.action, channel.SourceKernel.coefficient_error,
                 channel._piece, channel._coefficient, channel._hermitian, channel._key, channel._initial, channel._entry_norm,
                 channel._difference, channel._add, channel._read_input, channel._input_record,
                 joint.JointCounterGenerator.__init__, joint.JointCounterGenerator.record,
                 joint.JointCounterGenerator.from_record.__func__, joint.JointCounterGenerator.action,
                 joint.JointCounterGenerator._blocks, joint.JointCounterGenerator.lift,
                 joint.JointCounterGenerator.independent_atomic_action, joint.JointCounterGenerator.detected_action,
                 joint._source, joint._matrix, joint.atom_pair_index, joint._operator_left, joint._operator_right,
                 joint.passive_transfer, local.CounterGenerator.__init__, local.CounterGenerator.atomic_action,
                 local.CounterGenerator._drift, local.CounterGenerator._check_trace, local._matrix,
                 local._apply_recycling, local._add, local._sum, full.radical_midpoint, full._sqrt,
                 dipole.matrix_product, dipole.matrix_adjoint, channel.modes.complex_exponential)
    return (tuple((id(f), id(f.__code__)) for f in functions), _copy, _digest, _require,
            MAX_EXPANDED_BITS, joint.DIMENSION, tuple(dipole.STATES), tuple(dipole.INDEX.items()), dipole.ION)


def _guard():
    _require(_signature is _SIGNATURE and _signature.__code__ is _SIGNATURE_CODE and _signature() == _EXPECTED,
             'first-ready source execution closure changed')


_SIGNATURE = _signature
_SIGNATURE_CODE = _signature.__code__
_GUARD = _guard
_GUARD_CODE = _guard.__code__
_EXPECTED = _signature()
