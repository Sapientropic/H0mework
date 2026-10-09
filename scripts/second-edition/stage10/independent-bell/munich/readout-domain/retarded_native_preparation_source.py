"""The same high-poll mother generates its raw two-pump joint update.

The queue/PC/field source is retained as a joint CP law.  Its quantum coimage
uses the complete local pump actions, because recent-count saturation makes
every intervening poll high before expiry.  A quantum marginal error never
becomes an error for the incoming fine queue measure.
"""
from fractions import Fraction as Q
from pathlib import Path
import copy
import hashlib
import json

import retarded_native_local_flow as native
import apd_window_history as apd
import common_optical_readout as common
import fourier_reference_local_programme_source as shared
import gaussian_atomic_pulse_source as gaussian

coimage, frame, factors, fourier = native.coimage, native.frame, native.factors, native.fourier
atomic, reference, exact = frame.atomic, fourier.reference_local, fourier.exact
dipole, full, joint, local, channel = native.dipole, native.full, native.joint, native.local, native.channel
SCHEMA = 'stage10-same-high-poll-raw-preparation-joint-source/v1'
PHASE_SCHEMA = SCHEMA+'/source-issued-factor-phase'
_NATIVE_CHECK, _SHARED_CHECK, _GAUSSIAN_CHECK = native._CHECK, shared._GUARD, gaussian._CHECK
_ISSUED, _PHASE_ISSUED, _LAW_ISSUED, _CLOCK_ISSUED, _VERIFIED_NATIVE, _OLD_PHASES = {}, {}, {}, {}, {}, {}
_CLOCK_TEMPLATES = {}
CLOCK_POLICIES = ('continuous', 'restart_on_preparation', 'restart_on_pump', 'source_PC_policy')
PUMP_ROLES = ('pump1to1', 'pump2to1')


def _require(value, message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _sum(*matrices):
    result = {}
    for matrix in matrices:
        result = local._sum(result, matrix)
    return result


def _bindings():
    modules = (native, apd, common, shared, gaussian, factors, fourier, atomic, reference, exact, joint, local, channel, full, dipole)
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), *(Path(m.__file__) for m in modules))}


def _plans(owner, raw):
    plans = reference._raw_plans(owner, raw)
    _require(all(len(side) in (2, 3) and all(p['raw_controls']['kind'] == 'preparation' for p in side[:2]) and
                 (len(side) == 2 or side[2]['raw_controls']['kind'] == 'excitation') for side in plans),
             'two original pumps and their optional next excitation role required')
    _require(all(plans[0][i]['raw_controls']['duration_seconds'] == plans[1][i]['raw_controls']['duration_seconds']
                 for i in range(2)), 'this joint source requires the same two physical pump boundaries on both sides')
    return plans


def _pc_steps(rules, initial, count):
    """Execute the original high rule; a finite cycle only skips repeated work."""
    _require(type(count) is int and count >= 0 and type(rules) is dict and initial['stage'] in rules,
             'original PC rules, face and exact poll count required')
    states, seen, changes = [_copy(initial)], {}, []
    while len(states)-1 < count:
        current = states[-1]; key = current['stage'], tuple(current['loaded_flags']), current['observed_capped_count']
        if key in seen:
            start, length = seen[key], len(states)-1-seen[key]
            final = start+(count-start) % length
            last = max((k+(count-k)//length*length if k > start else k
                        for k in changes if k <= count), default=None)
            return _copy(states[final]), last
        seen[key] = len(states)-1
        following = coimage._high(rules[current['stage']], current['loaded_flags'])
        _require(following['stage'] in rules, 'high successor must belong to the original PC inventory')
        following['PC_ready'] = rules[following['stage']]['ready']
        if following['stage'] != current['stage']:
            changes.append(len(states))
        states.append(following)
    return _copy(states[-1]), max(changes, default=None)


def _support(facts, successors, rules, durations):
    durations = tuple(map(full.nonnegative, durations))
    _require(len(durations) == 2 and all(durations) and type(successors) is list and successors,
             'every original high face and both positive pump durations required')
    cover = facts['requested_threshold_cover']
    _require(type(cover) is int and facts['source_recent_count_lower'] >= cover > 0 and
             all(rule['threshold'] <= cover for rule in rules.values()),
             'the original recent-count cover must include every intervening PC threshold')
    lo, hi = map(Q, facts['first_subsequent_native_poll_support_seconds'])
    expiry, period = Q(facts['earliest_possible_recent_expiry_seconds']), Q(facts['source_poll_period_seconds'])
    _require(period > 0 and hi+sum(durations, Q(0)) < expiry,
             'the entire high-poll time family and both pumps must precede the earliest possible expiry')
    boundaries = (durations[0], sum(durations, Q(0)))
    faces = []
    for index, initial in enumerate(successors):
        _require(initial['PC_ready'], 'every original high-poll face must enter preparation from Ready')
        rows = []
        for elapsed in boundaries:
            count = int(elapsed//period); state, changed = _pc_steps(rules, initial, count)
            rows.append({'elapsed_after_high_poll_seconds': str(elapsed), 'original_future_poll_count': count,
                         'original_PC_successor': state, 'last_stage_change_poll_index': changed})
        faces.append({'original_Ready_face_index': index, 'original_high_poll_PC_state': _copy(initial),
                      'source_pump_boundary_PC_states': rows})
    return {'source_high_poll_seconds_support': list(map(str, (lo, hi))),
            'source_preparation_end_seconds_support': list(map(str, (lo+boundaries[-1], hi+boundaries[-1]))),
            'physical_pump_durations_seconds': list(map(str, durations)), 'threshold_cover': cover,
            'earliest_possible_recent_expiry_seconds': str(expiry),
            'source_all_Ready_face_PC_updates': faces, 'all_intervening_APD_observations_are_high': True,
            'PC_stage_and_flags_fixed_by_label': False, 'hidden_arrival_timestamp_selected': False}


def _clock_record(policy, offsets):
    _require(type(policy) is str and policy in CLOCK_POLICIES and type(offsets) in (tuple, list) and len(offsets) == 2 and
             all(type(row) in (tuple, list) and len(row) == 2 for row in offsets),
             'one fixed restart law and four fixed AOM phase-step coordinates required; future phase tables are not input')
    rows = []
    for side in offsets:
        row = []
        for value in side:
            lo, hi = (tuple(map(full.exact, value)) if type(value) in (tuple, list) and len(value) == 2 else
                      (full.exact(value), full.exact(value)))
            _require(lo <= hi, 'ordered exact fixed phase-step intervals required')
            row.append({'phase_step_radians': list(map(str, (lo, hi))), 'centre': str((lo+hi)/2), 'radius': str((hi-lo)/2)})
        rows.append(row)
    return {'schema': SCHEMA+'/fixed-raw-lambda-pump-clock', 'restart_policy': policy, 'AOM_role_order': list(PUMP_ROLES),
            'two_side_fixed_phase_step_coordinates': rows, 'offsets_rechosen_at_each_record': False,
            'coordinates_apply_to_every_preparation_generation': True, 'future_phase_table_supplied': False}


def _pump_prefix(plans, side, index):
    return sum((Q(p['raw_controls']['duration_seconds']) for p in plans[side][:index]), Q(0))


def _clock_age(raw, clock, side, index, local_elapsed, poll, PC_origin, face_index):
    prefix = _pump_prefix(raw['source_generated_local_plans'], side, index)
    old_prefix = _pump_prefix(raw['original_source_local_plans'], side, index)
    ready = Q(raw['original_source_ready_seconds']); policy = clock['restart_policy']
    if policy == 'continuous': return poll+prefix+local_elapsed-ready-old_prefix
    if policy == 'restart_on_preparation': return prefix+local_elapsed-old_prefix
    if policy == 'restart_on_pump': return local_elapsed
    baseline = Q(raw['source_original_Ready_PC_phase_origins_seconds'][face_index])
    return poll+prefix+local_elapsed-PC_origin-(ready+old_prefix-baseline)


def _clock_age_range(raw, clock, side, index, local_elapsed, face_index):
    prefix = _pump_prefix(raw['source_generated_local_plans'], side, index)
    old_prefix = _pump_prefix(raw['original_source_local_plans'], side, index)
    ready = Q(raw['original_source_ready_seconds']); policy = clock['restart_policy']
    lo, hi = map(Q, raw['source_expiry_free_preparation_support']['source_high_poll_seconds_support'])
    if policy == 'continuous': return lo+prefix+local_elapsed-ready-old_prefix, hi+prefix+local_elapsed-ready-old_prefix
    if policy in ('restart_on_preparation', 'restart_on_pump'):
        age = prefix+local_elapsed-old_prefix if policy == 'restart_on_preparation' else local_elapsed
        return age, age
    initial = raw['source_expiry_free_preparation_support']['source_all_Ready_face_PC_updates'][face_index]['original_high_poll_PC_state']
    rules = {r['name']: r for r in raw['raw_PC_rules']}
    _, changed = _pc_steps(rules, initial, int((prefix+local_elapsed)//Q(raw['source_poll_period_seconds'])))
    baseline = ready+old_prefix-Q(raw['source_original_Ready_PC_phase_origins_seconds'][face_index])
    if changed is not None and raw['original_PC_phase_policy'] == 'restart_on_stage_change':
        age = prefix+local_elapsed-changed*Q(raw['source_poll_period_seconds'])-baseline
        return age, age
    transition = raw['original_high_poll_flow']['source_generated_return_and_high_poll']['source_return_high_transitions'][face_index]
    if initial['stage'] != transition['return_stage'] and raw['original_PC_phase_policy'] == 'restart_on_stage_change':
        age = prefix+local_elapsed-baseline; return age, age
    age_lo, age_hi = map(Q, raw['source_high_poll_clock_families'][face_index]['source_final_frame_age_interval_seconds'])
    return age_lo+prefix+local_elapsed-baseline, age_hi+prefix+local_elapsed-baseline


def _clock_cuts(raw, clock, index):
    start = _pump_prefix(raw['source_generated_local_plans'], 0, index)
    duration = Q(raw['source_generated_local_plans'][0][index]['raw_controls']['duration_seconds'])
    cuts = {Q(0), duration}
    if clock['restart_policy'] == 'source_PC_policy' and raw['original_PC_phase_policy'] == 'restart_on_stage_change':
        period = Q(raw['source_poll_period_seconds']); rules = {r['name']: r for r in raw['raw_PC_rules']}
        for k in range(int(start//period)+1, int((start+duration)//period)+1):
            if k*period >= start+duration: continue
            for row in raw['source_expiry_free_preparation_support']['source_all_Ready_face_PC_updates']:
                initial = row['original_high_poll_PC_state']
                if _pc_steps(rules, initial, k)[0]['stage'] != _pc_steps(rules, initial, k-1)[0]['stage']:
                    cuts.add(k*period-start); break
    return sorted(cuts)


def _phase_angles(phase, clock, side, generation, age_offset, gamma):
    _require(type(generation) is int and generation >= 0 and side in (0, 1), 'source generation and side required')
    return [Q(clock['two_side_fixed_phase_step_coordinates'][side][PUMP_ROLES.index(t.name)]['centre'])*generation-
            t.angular_frequency*gamma*age_offset for t in phase.programme().tones]


def _phase_variation(frequency, age_interval, anchor_age, phase_radius, gamma_hi):
    a, b = map(full.exact, age_interval)
    _require(a <= b and phase_radius >= 0 and gamma_hi > 0, 'source phase-age envelope, radius and positive clock required')
    difference = max(abs(a-anchor_age), abs(b-anchor_age))
    return min(Q(2), phase_radius+abs(frequency)*gamma_hi*difference)


def _line_covariance(phase):
    raw = atomic.AtomicPhase.record(phase); programme = phase.programme()
    projector = frame._projector('D2')
    owner = atomic.MunichAtomicProgramme.from_record(raw['parent'])
    static = _sum(programme.static, atomic.AtomicBase.off_diagonal_zeeman(owner.atomic_base(), raw['side']))
    _require(not frame._commutator(projector, static), 'full static and Zeeman source must commute with the common line chart')
    for raising in programme.excitations:
        _require(frame._commutator(projector, raising) == raising, 'all original off-resonant pump edges must have the same line charge')
    for jump in programme.bath.jumps:
        charge = -1 if jump.label[0] == 'D2' else 0
        _require(frame._commutator(projector, jump.matrix) == {k: charge*v for k, v in jump.matrix.items() if charge*v},
                 'every original resolved bath jump must transform in its own line chart')
    return {'full_static_Z_and_all_raw_raising_edges_checked': True, 'complete_resolved_bath_jump_inventory_checked': len(programme.bath.jumps),
            'same_source_equation': 'Phi_commonPhase = Ad(U_D2) Phi_relativeBeat Ad(U_D2^dag)',
            'relative_beat_phase_discarded': False}


def _rotate_template(state, angle, bits):
    result, error = {}, Q(0)
    for (i, j), pair in state.items():
        charge = int(dipole.STATES[i].family == 'D2')-int(dipole.STATES[j].family == 'D2')
        centre, radius = fourier.scalar.complex_exponential(0, charge*angle, bits=bits) if charge*angle else ((1, 0), Q(0))
        result[i, j] = fourier._multiply_pair(pair, centre); error += radius*(abs(pair[0])+abs(pair[1]))
    result, rounding = exact._dyadic_state(result, bits)
    return result, error+rounding


def _prepare_clock_template(original, phase, clock_cells, template, precision):
    _require(len(clock_cells) == 1, 'shared operator templates require one source clock cell; direct curves cover restart cells')
    angles = tuple(map(Q, clock_cells[0]['phase_angles'])); common_angle = angles[0]
    relative = tuple(a-common_angle for a in angles); covariance = _line_covariance(phase)
    key = _digest({'phase': phase.record(), 'angles': list(map(str, angles)), 'template': template,
                   'precision': precision, 'source_bindings': _bindings()})
    if key in _CLOCK_TEMPLATES: return copy.deepcopy(_CLOCK_TEMPLATES[key])
    if original is not None: shared._validate_zero_template(original, template, precision)
    if original is not None and not any(relative):
        prepared = shared._prepare_template(original, template, precision)
        begin, end, error, proof = prepared['begin'], prepared['end'], prepared['error'], prepared['certificate']
        old_reused = True
    else:
        columns = _PumpColumns(phase, {}, precision['coefficient_bits'], relative)
        width, _, _, prices, details, begin, end = fourier._piece(columns, template, Q(0), precision['mode_bits'],
                                                               precision['exponential_bits'], return_complex_endpoints=True)
        _require(width == phase.programme().base.duration and all(len(m['coefficients']) == 1 for m in template['modes']),
                 'the entire original constant-matrix template duration must be covered')
        error = sum(prices.values(), Q(0)); proof = {'raw_template_digest': _digest(template),
            'whole_original_relative_beat_source_prices': {k: str(v) for k, v in prices.items()}, **details}
        old_reused = False
    begin, e0 = _rotate_template(begin, common_angle, precision['coefficient_bits'])
    end, e1 = _rotate_template(end, common_angle, precision['coefficient_bits'])
    result = {'begin': begin, 'end': end, 'error': error+e0+e1, 'certificate': {'raw_template_digest': _digest(template),
        'common_line_frame_covariance': covariance, 'exact_common_carrier_angle': str(common_angle),
        'true_relative_beat_angles': list(map(str, relative)), 'original_operator_template_proof_reused': old_reused,
        'source_template_certificate': _copy(proof), 'complete_rotation_endpoint_prices': list(map(str, (e0, e1)))}}
    _CLOCK_TEMPLATES[key] = result
    return copy.deepcopy(result)


class RawPumpClockMember:
    def __init__(self, *args, **kwargs):
        raise ValueError('clock members are emitted from the same source raw-lambda family; a future phase table is not input')

    def record(self):
        _CHECK()
        _require(type(self) is RawPumpClockMember and set(vars(self)) == {'_owner', '_value', '_seal'} and
                 _CLOCK_ISSUED.get(id(self)) == (self._owner, self._seal) and _digest(self._value) == self._seal and
                 self._value['source_bindings'] == _bindings() and self._owner.record()['source_digest'] == self._value['source_family_digest'],
                 'the fixed same-history raw-lambda clock member changed')
        return _copy(self._value)


def _port_jump(raw, port, matrix, background):
    _require(type(port) is int and port in range(4), 'original physical APD port required')
    matrix = joint._matrix(matrix); result = {}
    for label, operators in raw.detected_operators:
        if label[-1] != port:
            continue
        left = local._sum(joint._operator_left(matrix, 0, operators[0]), joint._operator_left(matrix, 1, operators[1]))
        image = local._sum(joint._operator_right(left, 0, dipole.matrix_adjoint(operators[0])),
                           joint._operator_right(left, 1, dipole.matrix_adjoint(operators[1])))
        result = local._sum(result, image)
    for key, value in matrix.items():
        local._add(result, key, background*value)
    return result


def _joint_commute(matrix, side, hamiltonian):
    left, right = joint._operator_left(matrix, side, hamiltonian), joint._operator_right(matrix, side, hamiltonian)
    result = {}
    for key, value in left.items(): local._add(result, key, dipole.ComplexRadical(0, -1)*value)
    for key, value in right.items(): local._add(result, key, dipole.ComplexRadical(0, 1)*value)
    return result


def _compiled_law(law):
    return repr((vars(law._raw), tuple(vars(atom) for atom in law._raw.sources),
                 tuple((vars(p), vars(p.bath)) for p in law._programmes)))


class _PumpJointLaw:
    def __init__(self, first, second, optics, cover):
        _CHECK()
        records = tuple(atomic.AtomicPhase.record(p) for p in (first, second))
        optical = common.CommonOpticalReadout.record(optics)
        _require(type(first) is type(second) is atomic.AtomicPhase and
                 records[0]['parent'] == records[1]['parent'] == optical['common_atomic_owner'] and
                 tuple(p['side'] for p in records) == (0, 1) and
                 all(p['kind'] == 'preparation' for p in records) and
                 records[0]['duration_seconds'] == records[1]['duration_seconds'],
                 'same-owner complete two-side preparation phases and optical source required')
        programmes = tuple(atomic.AtomicPhase.programme(p) for p in (first, second))
        transfer, background = common.CommonOpticalReadout._parameters(optics, common.ALL_PORTS)
        raw = joint.JointCounterGenerator(*(p.base for p in programmes), threshold=1,
                                         background_rate=background, collection=transfer)
        unit = Q(records[0]['parent']['atomic_base']['seconds_per_unit'])
        detector = apd.APDWindowHistorySource(raw, seconds_per_unit=unit, maximum_threshold=cover)
        self._phases, self._optics, self._programmes, self._raw, self._apd = (first, second), optics, programmes, raw, detector
        self._value = {'schema': SCHEMA+'/complete-pump-joint-law', 'raw_phase_sources': list(records),
                       'common_optical_source': optical, 'original_APD_source': detector.record(),
                       'all_resolved_natural_environment_groups_preserved': True,
                       'four_port_backgrounds': optical['background_rates'],
                       'full_Z_and_all_original_tones_kept': True,
                       'source_model_mean_price': '0', 'source_bindings': _bindings()}
        self._seal = _digest(self._value); self._compiled = _compiled_law(self)
        _LAW_ISSUED[id(self)] = self._seal, self._phases, self._optics, self._programmes, self._raw, self._apd

    def record(self):
        _CHECK()
        _require(type(self) is _PumpJointLaw and set(vars(self)) ==
                 {'_phases', '_optics', '_programmes', '_raw', '_apd', '_value', '_seal', '_compiled'} and
                 _LAW_ISSUED.get(id(self)) == (self._seal, self._phases, self._optics, self._programmes, self._raw, self._apd) and
                 self._compiled == _compiled_law(self) and
                 _digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
                 [atomic.AtomicPhase.record(p) for p in self._phases] == self._value['raw_phase_sources'] and
                 common.CommonOpticalReadout.record(self._optics) == self._value['common_optical_source'] and
                 apd.APDWindowHistorySource.record(self._apd) == self._value['original_APD_source'] and
                 self._raw.record() == self._value['original_APD_source']['original_shared_source'] and
                 [p.record() for p in self._programmes] == [atomic.AtomicPhase.programme(p).record() for p in self._phases],
                 'raw pump bath, exact tones, APD or executed source changed')
        return _copy(self._value)

    def generator_images(self, elapsed_seconds, matrix, *, phase_angles=None, bits=192):
        raw = _PumpJointLaw.record(self); gaussian._precision(bits)
        elapsed = full.nonnegative(elapsed_seconds)
        _require(elapsed <= Q(raw['raw_phase_sources'][0]['duration_seconds']), 'original pump-local time required')
        unit = self._apd.seconds_per_unit; time = elapsed/unit; matrix = joint._matrix(matrix)
        pending = self._apd.no_arrival_action(matrix); phase_error = Q(0)
        phase_angles = ((Q(0), Q(0)),)*2 if phase_angles is None else phase_angles
        _require(type(phase_angles) in (tuple, list) and len(phase_angles) == 2 and all(len(row) == 2 for row in phase_angles),
                 'source-induced phase angles for both complete pump tone inventories required')
        for side, programme in enumerate(self._programmes):
            owner = atomic.MunichAtomicProgramme.from_record(raw['raw_phase_sources'][side]['parent'])
            h = atomic.AtomicBase.off_diagonal_zeeman(owner.atomic_base(), side)
            for number, (tone, raising) in enumerate(zip(programme.tones, programme.excitations)):
                angle = full.exact(phase_angles[side][number])-tone.angular_frequency*time
                centre, error = fourier.scalar.complex_exponential(0, angle, bits=bits) if angle else ((1, 0), Q(0))
                forward = {k: v*dipole.ComplexRadical(*centre) for k, v in raising.items()}
                h = _sum(h, forward, dipole.matrix_adjoint(forward))
                phase_error += 4*error*atomic._operator_upper(raising, bits)
            pending = local._sum(pending, _joint_commute(matrix, side, h))
        jumps = [_port_jump(self._raw, port, matrix, Q(value)) for port, value in
                 enumerate(raw['four_port_backgrounds'])]
        _require(_sum(*jumps) == self._apd.jump_rate(matrix), 'the four original ports must sum to the shared APD jump')
        total = _sum(pending, *jumps)
        return {'schema': SCHEMA+'/pump-joint-generator-image', 'pump_source_record': raw,
                'physical_local_seconds': str(elapsed), 'complete_initial_matrix': channel._input_record(matrix),
                'no_arrival_generator_per_second': channel._input_record({k: v*(1/unit) for k, v in pending.items()}),
                'four_port_jump_images_per_second': [channel._input_record({k: v*(1/unit) for k, v in jump.items()}) for jump in jumps],
                'complete_forget_arrival_generator_per_second': channel._input_record({k: v*(1/unit) for k, v in total.items()}),
                'scalar_generator_error_per_second_per_input_norm': str(phase_error/unit),
                'coherent_detected_and_undetected_cross_terms_cancel_before_marginal': True}


class _PumpColumns:
    column = fourier._Columns.column

    def __init__(self, phase, initial, bits, phase_angles=None):
        raw = atomic.AtomicPhase.record(phase)
        lifted = exact.ExactLocalPhaseSource(phase, factors._embed(initial, raw['side']))
        self.tensor = exact._TensorColumns(lifted, bits); self.side = raw['side']; self.bits = bits; self.cache = {}
        self.frequencies = tuple(t.angular_frequency for t in self.tensor.programme.tones)
        self.components = tuple(self.tensor.operations)
        self.phase_angles = tuple(Q(0) for _ in self.frequencies) if phase_angles is None else tuple(map(full.exact, phase_angles))
        _require(len(self.phase_angles) == len(self.frequencies), 'the original complete tone phase inventory is required')

    def action(self, component, state):
        result, error = fourier._Columns.action(self, component, state)
        if component == 'static' or not self.phase_angles[component[0]]: return result, error
        number, sign = component; centre, scalar_error = fourier.scalar.complex_exponential(0, sign*self.phase_angles[number], bits=self.bits)
        scaled = {k: fourier._multiply_pair(v, centre) for k, v in result.items()}
        scaled, rounding = exact._dyadic_state(scaled, self.bits)
        return scaled, (abs(centre[0])+abs(centre[1])+scalar_error)*error+scalar_error*fourier._norm(result)+rounding


def _local_coimage(phase, initial, old, clock, pieces, precision, phase_clock_cells=None):
    _CHECK(); raw = atomic.AtomicPhase.record(phase)
    _require(type(precision) is dict and set(precision) == {'mode_bits', 'coefficient_bits', 'exponential_bits'},
             'complete original Fourier source precision required')
    mb, cb, eb = (precision[k] for k in ('mode_bits', 'coefficient_bits', 'exponential_bits'))
    _require(type(mb) is int and 32 <= mb <= 256 and type(cb) is int and 64 <= cb <= 512 and
             type(eb) is int and 64 <= eb <= 1024 and type(pieces) is list, 'registered complete source curve precision required')
    initial = channel._initial(initial, full.DIMENSION); old = full.nonnegative(old)
    unit = Q(raw['parent']['atomic_base']['seconds_per_unit']); centre, rounding = native._centre(initial, cb)
    duration = Q(raw['duration_seconds'])/unit
    cells = ([{'physical_interval_seconds': ['0', raw['duration_seconds']], 'phase_angles': ['0', '0'],
               'physical_phase_argument_at_cell_start_seconds': '0'}] if phase_clock_cells is None else phase_clock_cells)
    _require(type(cells) is list and cells and Q(cells[0]['physical_interval_seconds'][0]) == 0 and
             Q(cells[-1]['physical_interval_seconds'][1]) == Q(raw['duration_seconds']) and
             all(Q(c['physical_interval_seconds'][0]) < Q(c['physical_interval_seconds'][1]) for c in cells) and
             all(Q(a['physical_interval_seconds'][1]) == Q(b['physical_interval_seconds'][0]) for a, b in zip(cells, cells[1:])),
             'source-generated phase-clock cells must cover the whole pump exactly')
    columns_by_cell = {}; columns = None
    elapsed = Q(0); price = old+rounding; payments = []
    for piece in pieces:
        cell_index = next((i for i, c in enumerate(cells) if Q(c['physical_interval_seconds'][0]) <= elapsed*unit < Q(c['physical_interval_seconds'][1])), None)
        _require(cell_index is not None, 'complete original source phase-clock coverage required')
        cell = cells[cell_index]
        _require((elapsed+full.exact(piece['duration']))*unit <= Q(cell['physical_interval_seconds'][1]),
                 'a trial piece cannot cross an original phase-clock restart boundary')
        if cell_index not in columns_by_cell: columns_by_cell[cell_index] = _PumpColumns(phase, initial, cb, cell['phase_angles'])
        columns = columns_by_cell[cell_index]
        width, begin, end, prices, details = fourier._piece(columns, piece, elapsed, mb, eb)
        join = fourier._difference(begin, centre); price += join+sum(prices.values(), Q(0)); elapsed += width
        _require(elapsed <= duration, 'pump curve must stay within its original physical phase')
        payments.append({'duration': str(width), 'join_price': str(join),
                         'original_full_G_prices': {k: str(v) for k, v in prices.items()}, **details}); centre = end
    _require(elapsed == duration, 'pump curve must cover its entire original physical phase')
    clock_prices = []
    for cell in cells:
        a, b = map(Q, cell['physical_interval_seconds']); age = Q(cell['physical_phase_argument_at_cell_start_seconds'])
        absolute = max(abs(age), abs(age+b-a))
        paid = reference._phase_clock_price(phase, (absolute, absolute+b-a), clock, frame.bsm._entry_norm(initial, bits=cb), cb)
        paid['actual_phase_argument_start_seconds'] = str(age); paid['absolute_age_interval_is_a_conservative_envelope'] = True
        clock_prices.append(paid)
    clock_price = {'source_generated_phase_clock_cells': cells, 'cell_clock_prices': clock_prices,
                   'total_trace_norm_payment': str(sum((Q(c['total_trace_norm_payment']) for c in clock_prices), Q(0)))}
    price, outward = reference._outward_error(price+Q(clock_price['total_trace_norm_payment']), cb)
    return {'full_local_poststate': channel._input_record({k: dipole.ComplexRadical(*v) for k, v in centre.items()}),
            'trace_norm_error': str(price), 'old_factor_error_once': str(old), 'source_reference_clock_price': clock_price,
            'error_outward_rounding': str(outward), 'piece_error_records': payments,
            'original_full_local_component_columns_checked': sum(len(c.tensor.columns) for c in columns_by_cell.values()),
            'source_model_mean_payment': '0', 'all_full33_output_coordinates_priced': True}


def _shared_coimage(phase_source, witness, templates, precision):
    raw = _PumpFactorPhaseSource.record(phase_source)
    original = RetardedNativePreparationSource._template_phase(phase_source._owner, raw['side'], raw['phase_index'])
    old = shared._FactorPhaseSource.record(original)
    _require(old['source_phase'] == raw['source_phase'] and old['reference_clock'] == raw['reference_clock'],
             'reused template proofs must concern exactly the same complete raw pump and clock')
    _require(type(precision) is dict and set(precision) == {'mode_bits', 'coefficient_bits', 'exponential_bits'},
             'complete original shared-template precision required')
    mb, cb, eb = (precision[k] for k in ('mode_bits', 'coefficient_bits', 'exponential_bits'))
    _require(type(mb) is int and 32 <= mb <= 256 and type(cb) is int and 64 <= cb <= 512 and
             type(eb) is int and 64 <= eb <= 1024 and type(templates) is list and templates,
             'complete original source templates and registered precision required')
    _require(type(witness) is dict and set(witness) == {'template_digest', 'weights'} and
             witness['template_digest'] == shared._digest(templates) and type(witness['weights']) is list and
             len(witness['weights']) == len(templates), 'complete untrusted same-template weights required')
    clock_cells = raw['source_phase_clock_cells']
    _require(len(clock_cells) == 1, 'actual clock restart cells require direct complete source curves; a whole old template cannot cross them')
    quantum = 1 << mb; begin, end, payment, records = {}, {}, Q(0), []
    for template, weight in zip(templates, witness['weights']):
        _require(type(weight) is list and len(weight) == 2 and all(type(v) is int for v in weight), 'exact dyadic complex weights required')
        if weight == [0, 0]:
            shared._validate_zero_template(original, template, precision)
            records.append({'template_digest': shared._digest(template), 'weight': weight, 'weighted_original_price': '0'})
            continue
        prepared = _prepare_clock_template(original, atomic._read_phase(raw['source_phase']), clock_cells, template, precision)
        a, b = (Q(v, quantum) for v in weight)
        fourier._add_rational(begin, prepared['begin'], (a, b)); fourier._add_rational(end, prepared['end'], (a, b))
        price = (abs(a)+abs(b))*prepared['error']; payment += price
        records.append({'template_digest': shared._digest(template), 'weight': weight,
                        'weighted_original_price': str(price), 'original_template_certificate': _copy(prepared['certificate'])})
    initial = channel._read_input(raw['complete_initial_local_factor'], full.DIMENSION)
    centre, rounding = native._centre(initial, cb); join = fourier._difference(fourier._hermitian(begin), centre)
    age = Q(clock_cells[0]['physical_phase_argument_at_cell_start_seconds']); duration = Q(raw['physical_duration_seconds'])
    absolute = max(abs(age), abs(age+duration))
    clock = reference._phase_clock_price(atomic._read_phase(raw['source_phase']), (absolute, absolute+duration),
                                        raw['reference_clock'], frame.bsm._entry_norm(initial, bits=cb), cb)
    error, outward = reference._outward_error(Q(raw['factor_upstream_error'])+rounding+join+payment+Q(clock['total_trace_norm_payment']), cb)
    return {'full_local_poststate': channel._input_record({k: dipole.ComplexRadical(*v) for k, v in fourier._hermitian(end).items()}),
            'trace_norm_error': str(error), 'old_factor_error_once': raw['factor_upstream_error'],
            'source_reference_clock_price': clock, 'error_outward_rounding': str(outward),
            'source_input_join_price': str(join), 'weighted_original_template_price': str(payment),
            'original_operator_template_certificates': records, 'old_Ready_state_used_as_new_input': False}


class _PumpFactorPhaseSource:
    def __init__(self, *args, **kwargs):
        raise ValueError('pump factors are issued only by the same high-poll source and their checked predecessor')

    def record(self):
        _CHECK()
        _require(type(self) is _PumpFactorPhaseSource and set(vars(self)) == {'_owner', '_value', '_seal'} and
                 _PHASE_ISSUED.get(id(self)) == (self._owner, self._seal) and _digest(self._value) == self._seal and
                 self._value['source_bindings'] == _bindings() and
                 RetardedNativePreparationSource.record(self._owner)['source_digest'] == self._value['preparation_source_digest'],
                 'source-issued pump factor, complete input or predecessor changed')
        return _copy(self._value)

    def certify(self, pieces, *, mode_bits=96, coefficient_bits=192, exponential_bits=192):
        raw = _PumpFactorPhaseSource.record(self); _require(raw['phase_index'] < 2, 'the next excitation is a separate source responsibility')
        precision = dict(mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        result = _local_coimage(atomic._read_phase(raw['source_phase']),
            channel._read_input(raw['complete_initial_local_factor'], full.DIMENSION), raw['factor_upstream_error'], raw['reference_clock'], pieces, precision,
            raw['source_phase_clock_cells'])
        return {'schema': PHASE_SCHEMA+'/coimage', 'source_record': raw, 'untrusted_curve': _copy(pieces), 'precision': precision, **result}

    def certify_shared(self, witness, templates, *, mode_bits=60, coefficient_bits=160, exponential_bits=160):
        raw = _PumpFactorPhaseSource.record(self); _require(raw['phase_index'] < 2, 'only the original two pump templates are reused')
        precision = dict(mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        result = _shared_coimage(self, witness, templates, precision)
        return {'schema': PHASE_SCHEMA+'/coimage', 'source_record': raw, 'untrusted_shared_witness': _copy(witness),
                'shared_templates_digest': _digest(templates), 'precision': precision, **result}

    def verify(self, report, templates=None):
        raw = _PumpFactorPhaseSource.record(self)
        _require(type(report) is dict and report.get('schema') == PHASE_SCHEMA+'/coimage' and report.get('source_record') == raw,
                 'same issued pump factor and preceding phase certificate required')
        rebuilt = (self.certify(report['untrusted_curve'], **report['precision']) if 'untrusted_curve' in report else
                   self.certify_shared(report['untrusted_shared_witness'], templates, **report['precision']))
        _require(rebuilt == report, 'complete pump action, clock, endpoint or original price changed')
        return True


class RetardedNativePreparationSource:
    def __init__(self, source, high_poll_report, raw_two_side_clock_plans=None):
        _CHECK()
        _require(type(source) is native.RetardedNativeLocalFlow, 'closed same-occurrence complete native high-poll flow required; rho is not input')
        original = native.RetardedNativeLocalFlow.record(source); key = id(source), _digest(high_poll_report)
        if key not in _VERIFIED_NATIVE:
            native.RetardedNativeLocalFlow.verify(source, high_poll_report); _VERIFIED_NATIVE[key] = _copy(high_poll_report)
        _require(_VERIFIED_NATIVE[key] == high_poll_report and high_poll_report['original_CEM_return_coimage'] == original,
                 'the entire checked high-poll report must belong to the very same source pointer and event')
        parent = source._coimage._source._value['source_issued_two_pump_source']['reference_local_parent']
        owner = atomic.MunichAtomicProgramme.from_record(parent['working_atomic_owner'])
        raw_plans = ([[p['raw_controls'] for p in side] for side in parent['source_generated_local_plans']]
                     if raw_two_side_clock_plans is None else raw_two_side_clock_plans)
        plans = _plans(owner, raw_plans); facts = original['source_generated_return_and_high_poll']
        geometry = parent['reference_first_poll_ready']['same_physical_geometry']
        rules = {rule['name']: rule for rule in geometry['raw_PC_rules']}
        successors = [row['original_high_successor'] for row in high_poll_report['source_all_Ready_face_native_families']]
        _require(len(successors) == len(facts['source_return_high_transitions']) and
                 successors == [row['first_native_high_successor'] for row in facts['source_return_high_transitions']],
                 'all original Ready faces must remain in the source update')
        support = _support(facts, successors, rules, [p['raw_controls']['duration_seconds'] for p in plans[0][:2]])
        optics = common.CommonOpticalReadout.from_record(parent['working_common_optical_source'])
        laws = tuple(_PumpJointLaw(*(atomic._read_phase(plans[side][index]['source_phase']) for side in (0, 1)),
                                  optics, support['threshold_cover']) for index in range(2))
        matrix = channel._read_input(high_poll_report['complete_quantum_endpoint'], joint.DIMENSION)
        inventory, terms = factors._factor_inventory(factors._decompose(matrix))
        ready_faces = [f for f in parent['reference_first_poll_ready']['count_faces'] if f['PC_ready']]
        first_rule = parent['reference_native_source_record']['normalized_native_assembler']['original_PRM_source']['initial_poll_rule']
        original_origins = [geometry['physical_seconds']['stop'] if f['PC_stage'] != first_rule['name'] and
                            geometry['phase_policy'] == 'restart_on_stage_change' else geometry['physical_seconds']['field_phase_origin'] for f in ready_faces]
        self._native, self._parent, self._laws = source, parent, laws
        self._value = {'schema': SCHEMA, 'same_CEM_occurrence': original['original_CEM_occurrence'],
            'checked_high_poll_report_digest': _digest(high_poll_report), 'original_high_poll_flow': original,
            'original_high_poll_complete_mother': _copy(high_poll_report['whole_quantum_time_field_queue_successor_mother']),
            'complete_initial_quantum_coimage': high_poll_report['complete_quantum_endpoint'],
            'whole_native_error_once': high_poll_report['complete_native_trace_norm_error'],
            'native_infinite_Gaussian_Duhamel_budget': high_poll_report['continuing_Gaussian_native_difference_price'],
            'source_trace_normalizer': _copy(high_poll_report['source_trace_normalizer']),
            'reference_clock': _copy(parent['reference_clock']), 'working_atomic_owner': owner.record(),
            'working_common_optical_source': optics.record(), 'working_aperture_source': _copy(parent['working_aperture_source']),
            'source_generated_local_plans': plans, 'local_factor_inventory': inventory, 'source_tensor_factor_ids': terms,
            'original_source_local_plans': _copy(parent['source_generated_local_plans']),
            'original_source_ready_seconds': parent['source_ready_physical_clock_seconds'],
            'source_original_Ready_PC_phase_origins_seconds': original_origins,
            'source_high_poll_clock_families': [r['source_time_family'] for r in high_poll_report['source_all_Ready_face_native_families']],
            'numeric_anchor_receipt_seconds': high_poll_report['source_record_anchor_receipt_seconds'],
            'source_preparation_generation': 1,
            'source_expiry_free_preparation_support': support, 'raw_PC_rules': list(rules.values()),
            'original_PC_phase_policy': geometry['phase_policy'], 'source_poll_phase_seconds': facts['source_poll_phase_seconds'],
            'source_poll_period_seconds': facts['source_poll_period_seconds'], 'source_joint_pump_laws': [law.record() for law in laws],
            'source_pump_field_command': 'enter the supplied raw pump programme after each original confirming high poll; field_started_at and optical phase origin are separate coordinates',
            'pump_field_clock_is_the_PC_phase_started_at': False,
            'source_phase_clock_family': {'restart_policies': list(CLOCK_POLICIES), 'AOM_roles': list(PUMP_ROLES),
                'fixed_offset_coordinate_domain': 'four unrestricted real phase-step offsets; exact interval members preserve continuous coordinates',
                'first_programme_complex_amplitudes_are_the_initial_phase_coordinates': True,
                'later_offsets_are_generation_times_the_same_fixed_step': True, 'member_chosen_as_actual_hardware': False},
            'source_raw_commands_same_on_every_queue_fibre': True,
            'phase_age_action_same_on_every_Ready_time_fibre_assumed': False,
            'incoming_quantum_queue_measure_replaced_by_product': False, 'queue_reset': False,
            'source_new_joint_CP_action_and_arrival_word_law_defined': True,
            'fine_queue_measure_numerically_computed': False, 'actual_hardware_member_asserted': False,
            'controller_advance': False, 'source_bindings': _bindings()}
        self._seal = _digest(self._value); _ISSUED[id(self)] = source, self._seal, laws

    def record(self):
        _CHECK()
        _require(type(self) is RetardedNativePreparationSource and set(vars(self)) == {'_native', '_parent', '_laws', '_value', '_seal'} and
                 _ISSUED.get(id(self)) == (self._native, self._seal, self._laws) and _digest(self._value) == self._seal and
                 self._value['source_bindings'] == _bindings() and native.RetardedNativeLocalFlow.record(self._native) == self._value['original_high_poll_flow'] and
                 [law.record() for law in self._laws] == self._value['source_joint_pump_laws'],
                 'same CEM source, original mother, raw pumps or executed joint action changed')
        return {**_copy(self._value), 'source_digest': self._seal}

    def clock_member(self, restart_policy, phase_step_offsets):
        raw = self.record(); point = _clock_record(restart_policy, phase_step_offsets)
        cohort = _digest({'common_atomic_owner': raw['working_atomic_owner'], 'common_optical_source': raw['working_common_optical_source'],
                          'original_local_plans': raw['original_source_local_plans'], 'original_ready_seconds': raw['original_source_ready_seconds'],
                          'raw_PC_rules': raw['raw_PC_rules'], 'source_phase_policy': raw['original_PC_phase_policy']})
        value = {**point, 'source_family_digest': raw['source_digest'], 'working_atomic_owner': raw['working_atomic_owner'],
                 'original_programme_clock_reference_seconds': raw['original_source_ready_seconds'],
                 'same_raw_lambda_cohort_digest': cohort,
                 'same_history_raw_lambda_clock_digest': _digest({'cohort': cohort, 'fixed_clock_parameters': point}), 'source_bindings': _bindings()}
        result = object.__new__(RawPumpClockMember); result._owner, result._value, result._seal = self, value, _digest(value)
        _CLOCK_ISSUED[id(result)] = self, result._seal
        return result

    def _clock_member(self, member):
        _require(type(member) is RawPumpClockMember and member._owner is self,
                 'an explicit member of this same fixed raw-lambda clock family is required; no nominal restart is selected')
        return RawPumpClockMember.record(member)

    def clock_fibre(self, receipt_seconds, face_index, elapsed_seconds, clock_member):
        raw = self.record(); point = self._clock_member(clock_member); PC = self.pc_fibre(receipt_seconds, face_index, elapsed_seconds)
        elapsed = full.nonnegative(elapsed_seconds); first = Q(raw['source_expiry_free_preparation_support']['physical_pump_durations_seconds'][0])
        index, local_time = (0, elapsed) if elapsed < first else (1, elapsed-first)
        ages, phases = [], []
        gamma = Q(raw['reference_clock']['Gamma_numerical_centre'])
        for side in (0, 1):
            age = _clock_age(raw, point, side, index, local_time, Q(PC['source_high_poll_seconds']), Q(PC['phase_started_at_seconds']), face_index)
            phase = atomic._read_phase(raw['source_generated_local_plans'][side][index]['source_phase'])
            angles = _phase_angles(phase, point, side, raw['source_preparation_generation'], age-local_time, gamma)
            ages.append(str(age)); phases.append(list(map(str, angles)))
        return {'source_receipt_and_PC_fibre': PC, 'clock_member_digest': clock_member._seal,
                'same_history_raw_lambda_clock_digest': point['same_history_raw_lambda_clock_digest'],
                'pump_phase_index': index, 'pump_field_started_at_seconds': str(Q(PC['source_high_poll_seconds'])+(first if index else 0)),
                'two_side_physical_phase_arguments_seconds': ages, 'two_side_complete_tone_phase_angles': phases,
                'field_clock_zero_is_an_optical_phase_restart_identity': False}

    def _phase_clock_cells(self, member, side, index):
        raw = self.record(); point = self._clock_member(member); cuts = _clock_cuts(raw, point, index)
        prefix = _pump_prefix(raw['source_generated_local_plans'], side, index)
        gamma = Q(raw['reference_clock']['Gamma_numerical_centre']); result = []
        for a, b in zip(cuts, cuts[1:]):
            # Right-hand source action at a restart; the isolated boundary
            # has zero time mass and still uses the original arrival/poll order.
            fibre = self.clock_fibre(raw['numeric_anchor_receipt_seconds'], 0, prefix+a, member)
            age = Q(fibre['two_side_physical_phase_arguments_seconds'][side]); phase = atomic._read_phase(raw['source_generated_local_plans'][side][index]['source_phase'])
            angles = _phase_angles(phase, point, side, raw['source_preparation_generation'], age-a, gamma)
            result.append({'physical_interval_seconds': list(map(str, (a, b))), 'phase_angles': list(map(str, angles)),
                           'physical_phase_argument_at_cell_start_seconds': str(age), 'source_clock_member_digest': member._seal})
        return result

    def _phase_family_price(self, member, last_index, bits):
        raw = self.record(); point = self._clock_member(member)
        gamma_hi = max(Q(raw['reference_clock']['Gamma_numerical_centre']), Q(raw['reference_clock']['angular_Gamma_enclosure_per_second'][1]))
        total, records = Q(0), []
        for index in range(last_index+1):
            cuts = _clock_cuts(raw, point, index)
            for a, b in zip(cuts, cuts[1:]):
                for side in (0, 1):
                    prefix = _pump_prefix(raw['source_generated_local_plans'], side, index); local_time = (a+b)/2
                    anchor = self.clock_fibre(raw['numeric_anchor_receipt_seconds'], 0, prefix+local_time, member)
                    age_anchor = Q(anchor['two_side_physical_phase_arguments_seconds'][side])
                    ranges = [_clock_age_range(raw, point, side, index, local_time, face)
                              for face in range(len(raw['source_high_poll_clock_families']))]
                    age_delta = max(abs(t-age_anchor) for pair in ranges for t in pair)
                    programme = atomic._read_phase(raw['source_generated_local_plans'][side][index]['source_phase']).programme()
                    for tone, raising in zip(programme.tones, programme.excitations):
                        radius = Q(point['two_side_fixed_phase_step_coordinates'][side][PUMP_ROLES.index(tone.name)]['radius'])*raw['source_preparation_generation']
                        variation = max(_phase_variation(tone.angular_frequency, pair, age_anchor, radius, gamma_hi) for pair in ranges)
                        price = 4*gamma_hi*(b-a)*atomic._operator_upper(raising, bits)*variation
                        total += price; records.append({'pump_phase_index': index, 'side': side, 'raw_AOM_role': tone.name,
                            'physical_interval_seconds': list(map(str, (a, b))), 'source_phase_age_difference_to_numeric_anchor_upper_seconds': str(age_delta),
                            'fixed_parameter_phase_radius_radians': str(radius), 'original_full_raising_operator_norm_upper': str(atomic._operator_upper(raising, bits)),
                            'induced_Duhamel_price_per_input_norm': str(price)})
        mass = Q(raw['source_trace_normalizer']['bounds'][1]); operator = min(Q(2), total)
        return {'schema': SCHEMA+'/whole-phase-clock-member-family-price', 'fixed_clock_member': point,
                'source_all_Ready_time_faces_and_fixed_phase_box_kept': True, 'same_source_PC_phase_age_envelopes_used': True,
                'complete_original_tone_prices': records, 'operator_difference_per_input_norm': str(operator),
                'same_positive_CEM_mother_mass_upper': str(mass), 'quantum_coimage_family_payment': str(operator*mass),
                'point_member_does_not_identify_actual_hardware': True, 'fine_queue_TV_claimed': False}

    def pc_fibre(self, receipt_seconds, face_index, elapsed_seconds=0):
        raw = self.record(); facts = raw['original_high_poll_flow']['source_generated_return_and_high_poll']
        receipt, elapsed = full.exact(receipt_seconds), full.nonnegative(elapsed_seconds)
        lo, hi = map(Q, facts['receipt_support_seconds'])
        _require(lo <= receipt <= hi and elapsed <= sum(map(Q, raw['source_expiry_free_preparation_support']['physical_pump_durations_seconds']), Q(0)),
                 'original receipt coordinate and complete pump-local time required')
        faces = [f for f in self._parent['reference_first_poll_ready']['count_faces'] if f['PC_ready']]
        _require(type(face_index) is int and 0 <= face_index < len(faces), 'every original Ready face is a source coordinate')
        returned = receipt+Q(facts['CEM_completion_offset_seconds']); period = Q(raw['source_poll_period_seconds'])
        poll = coimage._next_poll(returned, Q(raw['source_poll_phase_seconds']), period)
        policy = raw['original_high_poll_flow']['source_record']['raw_return_policy']
        origin = coimage._phase_origin(self._parent, policy, faces[face_index], returned)
        transition = facts['source_return_high_transitions'][face_index]; initial = transition['first_native_high_successor']
        if initial['stage'] != transition['return_stage'] and raw['original_PC_phase_policy'] == 'restart_on_stage_change': origin = poll
        state, changed = _pc_steps({r['name']: r for r in raw['raw_PC_rules']}, initial, int(elapsed//period))
        if changed is not None and raw['original_PC_phase_policy'] == 'restart_on_stage_change': origin = poll+changed*period
        return {'source_receipt_coordinate_seconds': str(receipt), 'source_Ready_face_index': face_index,
                'source_high_poll_seconds': str(poll), 'physical_clock_seconds': str(poll+elapsed),
                'original_PC_successor': state, 'phase_started_at_seconds': str(origin),
                'pump_field_started_at_seconds': str(poll), 'pump_origin_chosen_as_actual_unique_time': False}

    def generator_images(self, receipt_seconds, face_index, elapsed_seconds, matrix, *, clock_member, bits=192):
        raw = self.record(); fibre = self.pc_fibre(receipt_seconds, face_index, elapsed_seconds)
        clocks = self.clock_fibre(receipt_seconds, face_index, elapsed_seconds, clock_member)
        elapsed = full.nonnegative(elapsed_seconds); durations = list(map(Q, raw['source_expiry_free_preparation_support']['physical_pump_durations_seconds']))
        index = int(elapsed >= durations[0]); local_time = elapsed-(durations[0] if index else 0)
        images = self._laws[index].generator_images(local_time, matrix, phase_angles=clocks['two_side_complete_tone_phase_angles'], bits=bits)
        point = self._clock_member(clock_member); phase_box = Q(0)
        gamma_hi = max(Q(raw['reference_clock']['Gamma_numerical_centre']), Q(raw['reference_clock']['angular_Gamma_enclosure_per_second'][1]))
        for side in (0, 1):
            programme = self._laws[index]._programmes[side]
            for tone, raising in zip(programme.tones, programme.excitations):
                radius = Q(point['two_side_fixed_phase_step_coordinates'][side][PUMP_ROLES.index(tone.name)]['radius'])*raw['source_preparation_generation']
                phase_box += 4*gamma_hi*atomic._operator_upper(raising, bits)*min(Q(2), radius)
        pending = channel._read_input(images['no_arrival_generator_per_second'], joint.DIMENSION)
        current = joint._matrix(matrix); physical = Q(fibre['physical_clock_seconds']); tail_error = Q(0)
        original_field = native.actual._field_record(self._native._record_source._source)
        pulses = self._native._record_source._source._measure._certificate._source._law._field._pulses
        for side, (pulse, origin) in enumerate(zip(pulses, map(Q, original_field['emission_origins_seconds']))):
            h, error = gaussian.GaussianAtomicPulseSource.hamiltonian(pulse, physical-origin, bits=bits)
            quiet = channel._read_input(pulse.record()['complete_static_H_per_second'], full.DIMENSION)
            drive = local._sum(h, {k: -v for k, v in quiet.items()})
            pending = local._sum(pending, _joint_commute(current, side, drive)); tail_error += 2*error
        jumps = [channel._read_input(v, joint.DIMENSION) for v in images['four_port_jump_images_per_second']]
        return {**images, 'source_preparation_record_digest': raw['source_digest'], 'same_source_PC_and_clock_fibre': fibre,
                'source_fixed_clock_member_and_phase_fibre': clocks,
                'fixed_phase_box_generator_difference_per_second_per_input_norm': str(phase_box),
                'image_phase_offsets_are_numeric_interval_centres': True,
                'image_reference_Gamma_centre_is_not_the_entire_Gamma_family': True,
                'source_pump_phase_index': index, 'no_arrival_generator_per_second': channel._input_record(pending),
                'complete_forget_arrival_generator_per_second': channel._input_record(_sum(pending, *jumps)),
                'scalar_generator_error_per_second_per_input_norm': str(Q(images['scalar_generator_error_per_second_per_input_norm'])+tail_error),
                'original_ongoing_Gaussian_drive_in_actual_generator': True, 'Gaussian_physical_turnoff_assumed': False}

    def arrival_word(self, receipt_seconds, face_index, memory, word, *, clock_member):
        raw = self.record(); fibre = self.pc_fibre(receipt_seconds, face_index)
        point = self._clock_member(clock_member)
        start = Q(fibre['source_high_poll_seconds']); detector = self._laws[0]._apd; unit = detector.seconds_per_unit
        detector._check_memory(memory)
        facts = raw['original_high_poll_flow']['source_generated_return_and_high_poll']
        _require(memory.clock*unit == start and len(memory.recent) >= raw['source_expiry_free_preparation_support']['threshold_cover'] and
                 all(t*unit > Q(facts['recent_arrival_support_seconds'][0]) for t in memory.recent),
                 'a latent queue fibre of this same recent-count high-poll mother is required')
        _require(type(word) in (tuple, list), 'the original ordered physical-port arrival word is required')
        stop = start+sum(map(Q, raw['source_expiry_free_preparation_support']['physical_pump_durations_seconds']), Q(0))
        previous, routes, incoming = start, [], memory.record()
        boundary = start+Q(raw['source_expiry_free_preparation_support']['physical_pump_durations_seconds'][0])
        switched = False
        for item in word:
            _require(type(item) in (tuple, list) and len(item) == 2 and type(item[1]) is int and item[1] in range(4),
                     'exact arrival time and original physical APD port required')
            time = full.exact(item[0]); _require(previous < time <= stop, 'arrival word must strictly advance in the original two-pump interval')
            if not switched and time >= boundary:
                memory = detector.elapse(memory, boundary/unit-memory.clock)
                memory = detector.retain_on_phase_change(memory, self._laws[1]._apd); detector = self._laws[1]._apd; switched = True
            memory = detector.append_arrival(detector.elapse(memory, time/unit-memory.clock))
            routes.append({'physical_arrival_seconds': str(time), 'physical_port': item[1], 'memory_after_original_jump': memory.record(),
                           'PC_after_arrival_then_poll': self.pc_fibre(receipt_seconds, face_index, time-start)})
            previous = time
        if not switched:
            memory = detector.elapse(memory, boundary/unit-memory.clock)
            memory = detector.retain_on_phase_change(memory, self._laws[1]._apd); detector = self._laws[1]._apd
        memory = detector.elapse(memory, stop/unit-memory.clock)
        return {'schema': SCHEMA+'/source-arrival-word-memory-coimage', 'source_record_digest': raw['source_digest'],
                'fixed_same_history_raw_lambda_clock_member': point,
                'source_receipt_and_Ready_fibre': fibre, 'incoming_latent_memory': incoming, 'word_coordinates': routes,
                'complete_outgoing_memory': memory.record(), 'outgoing_PC_and_phase_epoch': self.pc_fibre(receipt_seconds, face_index, stop-start),
                'quantum_word_law': 'Phi0(stop,t_n) J_port_n(t_n) ... J_port_1(t_1) Phi0(t_1,start), with this source generator_images',
                'old_mother_retained_without_product_replacement': True, 'word_measure_numerically_integrated': False,
                'actual_arrival_word_selected': False, 'fine_queue_TV_inferred_from_quantum_error': False}

    def _template_phase(self, side, index):
        self.record(); _require(type(side) is int and side in (0, 1) and type(index) is int and index in (0, 1), 'original pump template phase required')
        prepared = self._native._coimage._source._prepared; programme = prepared._source; key = id(programme), side, index
        if key not in _OLD_PHASES:
            certificates, templates = map(json.loads, prepared._witnesses)
            row = certificates[side][0]
            _OLD_PHASES[key] = shared.FourierReferenceLocalProgrammeSource.phase_source(programme, side, row['factor_id'],
                row['complete_phase_certificates'][:index], templates[side])
        phase = _OLD_PHASES[key]
        _require(shared._FactorPhaseSource.record(phase)['source_phase'] == self._value['source_generated_local_plans'][side][index]['source_phase'],
                 'changed raw controls require a fresh original phase proof; an old operator template cannot be relabelled')
        return phase

    def phase_source(self, side, factor_id, preceding_certificates=(), shared_phase_templates=None, *, clock_member):
        raw = self.record(); _require(type(side) is int and side in (0, 1), 'original local source side required')
        point = self._clock_member(clock_member)
        item = next((v for v in raw['local_factor_inventory'][side] if v['factor_id'] == factor_id), None)
        _require(item is not None and type(preceding_certificates) in (list, tuple), 'complete same-mother factor inventory and actual checked prefix required')
        current = item['initial_local_matrix']; error = '0'; prefix = []
        for index in range(len(preceding_certificates)+1):
            _require(index < 2, 'the next excitation phase-clock family is a separate uncomputed source responsibility')
            plan = raw['source_generated_local_plans'][side][index]; phase = atomic._read_phase(plan['source_phase'])
            result = object.__new__(_PumpFactorPhaseSource); result._owner = self
            result._value = {'schema': PHASE_SCHEMA, 'preparation_source_digest': raw['source_digest'], 'side': side,
                'factor_id': factor_id, 'phase_index': index, 'source_phase': plan['source_phase'], 'complete_initial_local_factor': current,
                'factor_upstream_error': error, 'source_duration': str(phase.programme().base.duration),
                'physical_duration_seconds': plan['raw_controls']['duration_seconds'], 'reference_clock': raw['reference_clock'],
                'fixed_same_history_clock_member': point,
                'source_phase_clock_cells': self._phase_clock_cells(clock_member, side, index),
                'numeric_receipt_and_Ready_anchor': [raw['numeric_anchor_receipt_seconds'], 0],
                'verified_preceding_phase_certificate_digests': list(prefix), 'whole_mother_error_paid_per_factor': False,
                'source_bindings': _bindings()}
            result._seal = _digest(result._value); _PHASE_ISSUED[id(result)] = self, result._seal
            if index == len(preceding_certificates): return result
            report = preceding_certificates[index]
            result.verify(report, None if shared_phase_templates is None else shared_phase_templates[index])
            current, error = report['full_local_poststate'], report['trace_norm_error']; prefix.append(_digest(report))

    def complete_prefix(self, certificates, shared_phase_templates=None, *, clock_member, bits=192):
        raw = self.record(); gaussian._precision(bits)
        point = self._clock_member(clock_member)
        _require(type(certificates) in (tuple, list) and len(certificates) == 2 and
                 (shared_phase_templates is None or type(shared_phase_templates) in (tuple, list) and len(shared_phase_templates) == 2),
                 'the complete two-side original pump certificate inventories required')
        endpoints = [[{}, {}], [{}, {}]]; checked = [[], []]; next_phases = [[], []]
        for side, inventory in enumerate(raw['local_factor_inventory']):
            rows = certificates[side]
            _require(type(rows) in (tuple, list) and [r.get('factor_id') for r in rows] == [r['factor_id'] for r in inventory],
                     'every same-mother signed factor must be consumed exactly once')
            for row in rows:
                _require(type(row) is dict and set(row) == {'factor_id', 'complete_phase_certificates'} and
                         type(row['complete_phase_certificates']) in (tuple, list) and len(row['complete_phase_certificates']) == 2,
                         'exactly both complete original pump coimages required')
                prefix = []; templates = None if shared_phase_templates is None else shared_phase_templates[side]
                for index, report in enumerate(row['complete_phase_certificates']):
                    phase = self.phase_source(side, row['factor_id'], prefix, templates, clock_member=clock_member)
                    phase.verify(report, None if templates is None else templates[index]); prefix.append(report)
                    endpoints[index][side][row['factor_id']] = (channel._read_input(report['full_local_poststate'], full.DIMENSION), Q(report['trace_norm_error']))
                checked[side].append(_copy(row))
                if len(raw['source_generated_local_plans'][side]) == 3:
                    next_phases[side].append({'factor_id': row['factor_id'], 'complete_anchor_factor_after_both_pumps': prefix[-1]['full_local_poststate'],
                        'local_factor_numeric_error': prefix[-1]['trace_norm_error'], 'raw_next_excitation_phase': raw['source_generated_local_plans'][side][2],
                        'fixed_same_history_clock_member': point, 'verified_pump_prefix_digests': [_digest(r) for r in prefix],
                        'next_excitation_phase_clock_family_generated': False, 'source_time_family_must_be_consumed_by_next_field_producer': True})
        squares = []
        for index in range(2):
            matrix, payment, terms = {}, Q(0), []
            for left, right in raw['source_tensor_factor_ids']:
                a, ea = endpoints[index][0][left]; b, eb = endpoints[index][1][right]
                price, na, nb = factors._tensor_price(a, b, ea, eb, bits); payment += price
                factors._add(matrix, factors._tensor(a, b))
                terms.append({'source_factor_ids': [left, right], 'complete_local_errors': list(map(str, (ea, eb))),
                              'complete_local_norms': list(map(str, (na, nb))), 'source_tensor_price': str(price)})
            family = self._phase_family_price(clock_member, index, bits)
            error, outward = reference._outward_error(Q(raw['whole_native_error_once'])+payment+Q(family['quantum_coimage_family_payment']), bits)
            squares.append({'pump_phase_index': index, 'complete_quantum_coimage': channel._input_record(matrix),
                'whole_trace_norm_error': str(error), 'whole_native_error_transported_once': raw['whole_native_error_once'],
                'source_local_and_tensor_price': str(payment), 'source_whole_phase_clock_family_price': family,
                'error_outward_rounding': str(outward), 'source_tensor_terms': terms,
                'source_joint_CP_to_quantum_coimage_law': 'forget every original port word and queue fibre; sum J plus G0 equals both complete local pump generators',
                'all_PC_polls_and_all_Ready_time_faces_kept': True})
        return {'schema': SCHEMA+'/complete-two-pump-quantum-coimage', 'source_record': raw,
            'fixed_same_history_raw_lambda_clock_member': point,
            'complete_local_factor_certificates': checked, 'source_owned_shared_templates': _copy(shared_phase_templates), 'scalar_bits': bits,
            'source_quantum_coimage_squares': squares, 'complete_quantum_endpoint': squares[-1]['complete_quantum_coimage'],
            'complete_preparation_trace_norm_error': squares[-1]['whole_trace_norm_error'], 'next_excitation_raw_factor_inlets': next_phases,
            'next_excitation_phase_clock_family_generated': False,
            'source_trace_normalizer': raw['source_trace_normalizer'], 'source_preparation_time_and_PC_family': raw['source_expiry_free_preparation_support'],
            'whole_quantum_time_field_queue_preparation_mother': {'original_complete_high_poll_mother': raw['original_high_poll_complete_mother'],
                'same_source_joint_preparation_action': raw['source_joint_pump_laws'], 'all_source_time_and_PC_updates': raw['source_expiry_free_preparation_support'],
                'arrival_word_action_evaluator': 'RetardedNativePreparationSource.generator_images / arrival_word',
                'original_field_and_bath_history_retained': True, 'incoming_joint_measure_replaced_by_quantum_marginal': False},
            'continuing_Gaussian_TP_composition_contract': {'original_infinite_tail_budget': raw['native_infinite_Gaussian_Duhamel_budget'],
                'budget_already_in_whole_native_error': True, 'same_infinite_tail_charged_again': False,
                'source_perturbation': 'same H_atom(t) tensor identity on the retained field and queue; both flows have the same bath and record jumps',
                'norm_law': 'Duhamel commutator price 4*norm(original raising)*J times the same positive CEM mother mass; TP composition from return through both pumps',
                'price_scope': 'complete quantum coimage; no fine queue or field measure TV inferred'},
            'full_joint_queue_density_numerically_computed': False, 'free_prepared_target_used': False,
            'actual_hardware_member_asserted': False, 'controller_advance': False, 'source_bindings': _bindings()}

    def verify(self, report, *, clock_member):
        _require(type(report) is dict and report.get('schema') == SCHEMA+'/complete-two-pump-quantum-coimage' and
                 report.get('source_record') == self.record(), 'the complete same-source two-pump report is required')
        _require(report['fixed_same_history_raw_lambda_clock_member'] == self._clock_member(clock_member),
                 'the history consumer must retain this very fixed raw-lambda clock member')
        expected = self.complete_prefix(report['complete_local_factor_certificates'], report['source_owned_shared_templates'],
                                        clock_member=clock_member, bits=report['scalar_bits'])
        _require(expected == report, 'same-mother pump action, complete endpoint, time/PC family or paid price changed')
        return True

    def source_tensors(self, report, *, clock_member):
        """Return the checked inlet; the next field owns its excitation clock."""
        self.verify(report, clock_member=clock_member); raw = self.record()
        endpoints = [{}, {}]
        for side, inventory in enumerate(report['complete_local_factor_certificates']):
            for row in inventory:
                endpoints[side][row['factor_id']] = channel._read_input(row['complete_phase_certificates'][-1]['full_local_poststate'], full.DIMENSION)
        terms = tuple((dict(endpoints[0][a]), dict(endpoints[1][b])) for a, b in raw['source_tensor_factor_ids'])
        expanded = {}
        for a, b in terms: factors._add(expanded, factors._tensor(a, b))
        _require(channel._input_record(expanded) == report['complete_quantum_endpoint'],
                 'the direct field consumer must receive the entire checked coimage')
        return {'source_record': raw, 'checked_two_pump_report_digest': _digest(report),
                'tensor_terms': terms, 'whole_upstream_trace_norm_error': Q(report['complete_preparation_trace_norm_error']),
                'same_positive_CEM_mass_upper': Q(report['source_trace_normalizer']['bounds'][1]),
                'retained_time_state_mother': _copy(report['whole_quantum_time_field_queue_preparation_mother']),
                'source_preparation_end_time_family_seconds': tuple(map(Q, raw['source_expiry_free_preparation_support']['source_preparation_end_seconds_support'])),
                'fixed_same_history_raw_lambda_clock_member': self._clock_member(clock_member),
                'next_excitation_raw_factor_inlets': _copy(report['next_excitation_raw_factor_inlets']),
                'next_excitation_phase_clock_family_generated': False,
                'coimage_is_a_caller_supplied_free_endpoint': False, 'old_error_paid_per_factor': False}


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    helpers = (_require, _copy, _digest, _sum, _bindings, _plans, _pc_steps, _support,
               _clock_record, _pump_prefix, _clock_age, _clock_age_range, _clock_cuts, _phase_angles, _phase_variation,
               _line_covariance, _rotate_template, _prepare_clock_template,
               copy.deepcopy,
               _port_jump, _joint_commute, _compiled_law,
               _local_coimage, _shared_coimage, _function, _signature, _check,
               native.RetardedNativeLocalFlow.record, native.RetardedNativeLocalFlow.verify, native._centre,
               coimage._high, coimage._phase_origin, coimage._next_poll, native.actual._field_record,
               factors._decompose, factors._factor_inventory, factors._tensor, factors._tensor_price,
               fourier._Columns.column, fourier._Columns.action, fourier._piece, fourier.scalar.complex_exponential,
               reference._raw_plans, reference._phase_clock_price, reference._outward_error,
               shared._prepare_template, shared._validate_zero_template, shared._FactorPhaseSource.record,
               shared.FourierReferenceLocalProgrammeSource.phase_source,
               apd.APDWindowHistorySource.jump_rate, apd.APDWindowHistorySource.no_arrival_action,
               apd.APDWindowHistorySource.elapse, apd.APDWindowHistorySource.append_arrival,
               apd.APDWindowHistorySource.retain_on_phase_change, joint._operator_left, joint._operator_right,
               atomic.AtomicPhase.record, atomic.AtomicPhase.programme, atomic.AtomicBase.off_diagonal_zeeman,
               common.CommonOpticalReadout.record, common.CommonOpticalReadout._parameters,
               gaussian.GaussianAtomicPulseSource.hamiltonian, full.exact, full.nonnegative)
    methods = tuple(_function(v) for cls in (_PumpJointLaw, _PumpColumns, _PumpFactorPhaseSource, RawPumpClockMember, RetardedNativePreparationSource)
                    for v in vars(cls).values() if callable(v))
    return tuple(map(_function, helpers)), methods, SCHEMA, PHASE_SCHEMA, CLOCK_POLICIES, PUMP_ROLES


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             native._CHECK is _NATIVE_CHECK and shared._GUARD is _SHARED_CHECK and gaussian._CHECK is _GAUSSIAN_CHECK,
             'same-high-poll preparation executed source closure changed')
    _NATIVE_CHECK(); _SHARED_CHECK(); _GAUSSIAN_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
