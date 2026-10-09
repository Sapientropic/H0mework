"""Recent source-count support generates the first native return decision.

The counter proof covers every latent arrival word on the Ready branch.
Later photons can increase its rolling count.  Until the earliest expiry,
the native observation therefore has one coimage, without assigning hidden
arrival timestamps or replacing the complete quantum/time mother.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import prepared_retarded_gaussian_inlet as inlet
import reference_response_window_source as response
import retarded_actual_record_measure as actual
import native_cem_coimage as native
import native_tone_frame as frame

field, channel = inlet.field, inlet.channel
SCHEMA = 'stage10-source-retarded-native-recent-count-coimage/v1'
_INLET_CHECK, _RESPONSE_CHECK, _ACTUAL_CHECK, _NATIVE_CHECK = (
    inlet._CHECK, response._CHECK, actual._CHECK, native._CLOSED)
_FRAME_CHECK = frame._GUARD
_ISSUED = {}


def _require(value, message):
    if not value:
        raise ValueError(message)


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), *(Path(m.__file__) for m in (inlet, response, actual, native, frame)))}


def _next_poll(time, phase, period):
    _require(period > 0, 'positive source polling period required')
    return phase + max(0, (time-phase)//period + 1)*period


def _high(rule, flags):
    return {'stage': rule['high_next'], 'loaded_flags': [old if change is None else change
        for old, change in zip(flags, rule['high_flags'])], 'observed_capped_count': rule['threshold'],
        'observed_at_least_threshold': True, 'quantum_occupancy_read': False}


def _native_cell(parent, transition):
    original = parent['reference_native_source_record']['normalized_native_assembler']['original_PRM_source']
    value = actual.records._copy(original)
    rule = next(r for r in value['persistent_source']['rules'] if r['name'] == transition['return_stage'])
    value['initial_poll_rule'] = rule
    for cell in value['compiled_first_poll_cells']:
        cell['persistent_cell']['capture_enabled'] = rule['capture_mask']
    return frame._phase_data(value, 0)


def _phase_origin(parent, policy, face, returned):
    geometry = parent['reference_first_poll_ready']['same_physical_geometry']
    rule = parent['reference_native_source_record']['normalized_native_assembler']['original_PRM_source']['initial_poll_rule']
    changed = face['PC_stage'] != rule['name']
    origin = Q(geometry['physical_seconds']['stop'] if changed and geometry['phase_policy'] == 'restart_on_stage_change'
               else geometry['physical_seconds']['field_phase_origin'])
    target = face['PC_stage'] if policy['target_stage'] is None else policy['target_stage']
    if policy['phase_action'] == 'restart_at_return' or (policy['phase_action'] == 'source_policy' and
            target != face['PC_stage'] and geometry['phase_policy'] == 'restart_on_stage_change'):
        origin = returned
    return origin


def _action_column(cell, gamma, phase_elapsed, row, column, bits):
    joint, dipole, full = frame.joint, frame.dipole, frame.full
    _require(type(row) is int and type(column) is int and 0 <= row < joint.DIMENSION and
             0 <= column < joint.DIMENSION, 'complete native pair matrix-unit coordinates required')
    source = frame._ConstantSource(cell)
    count = source.threshold
    matrix = {(row, column): dipole.ComplexRadical(1)}
    image = source.action({(count, row, column): dipole.ComplexRadical(1)})
    _require(all(c == count for c, _, _ in image), 'saturated native coimage must forget every APD arrival')
    result = {(i, j): value for (_, i, j), value in image.items()}
    source_error = Q(0)
    frequencies = {line: Q(value) for line, value in cell['line_carrier_reciprocal_source_units'].items()}
    for side, square in enumerate(cell['full_source_square']):
        h = channel._read_input(square['full33_transformed_H'], full.DIMENSION)
        physical = {}
        for (i, j), value in h.items():
            frequency = frequencies.get(dipole.STATES[j].family, Q(0))-frequencies.get(dipole.STATES[i].family, Q(0))
            centre, error = channel.modes.complex_exponential(0, frequency*gamma*phase_elapsed, bits=bits)
            scalar = dipole.ComplexRadical(*centre)
            physical[i, j] = value*scalar
            source_error += error*frame.bsm._entry_norm({(0, 0): value}, bits=bits)
        for line, rows in cell['line_projectors'].items():
            for key, value in channel._read_input(rows, full.DIMENSION).items():
                frame.local._add(physical, key, frequencies[line]*value)
        for key, value in frame._commute(h, matrix, side).items():
            frame.local._add(result, key, -value)
        for key, value in frame._commute(physical, matrix, side).items():
            frame.local._add(result, key, value)
    return {key: gamma*value for key, value in result.items() if value}, 2*gamma*source_error


def _action_bounds(cell, bits):
    source = frame._ConstantSource(cell)
    frequencies = {line: Q(value) for line, value in cell['line_carrier_reciprocal_source_units'].items()}
    bound = derivative = Q(0)
    for side, (atom, square) in enumerate(zip(source.raw.sources, cell['full_source_square'])):
        h = channel._read_input(square['full33_transformed_H'], frame.full.DIMENSION)
        hnorm = frame.atomic._operator_upper(h, bits)+sum(map(abs, frequencies.values()), Q(0))
        capture = source.captures[side].first_birth_rate if source.enabled[side] else Q(0)
        bound += 2*(hnorm+max(atom.outgoing)+frame.bsm._entry_norm({(0, 0): frame.dipole.ComplexRadical(capture)}, bits=bits))
        for (i, j), value in h.items():
            frequency = frequencies.get(frame.dipole.STATES[j].family, Q(0))-frequencies.get(frame.dipole.STATES[i].family, Q(0))
            derivative += 2*abs(frequency)*frame.bsm._entry_norm({(0, 0): value}, bits=bits)
    return bound, derivative


def _rotating_bound(cell, bits):
    source = frame._ConstantSource(cell)
    bound = Q(0)
    for side, (atom, square) in enumerate(zip(source.raw.sources, cell['full_source_square'])):
        h = channel._read_input(square['full33_transformed_H'], frame.full.DIMENSION)
        capture = source.captures[side].first_birth_rate if source.enabled[side] else Q(0)
        bound += 2*(frame.atomic._operator_upper(h, bits)+max(atom.outgoing)+
            frame.bsm._entry_norm({(0, 0): frame.dipole.ComplexRadical(capture)}, bits=bits))
    frequencies = tuple(Q(value) for value in cell['line_carrier_reciprocal_source_units'].values())
    return bound, 2*sum(map(abs, frequencies), Q(0))


def _ground_ION_face(cell, bits):
    source = frame._ConstantSource(cell)
    total = Q(0); sides = []
    for side, (atom, square) in enumerate(zip(source.raw.sources, cell['full_source_square'])):
        h = channel._read_input(square['full33_transformed_H'], frame.full.DIMENSION)
        operators = [h, *(jump.matrix for jump in atom.jumps)]
        if source.enabled[side]:
            operators.extend(source.captures[side].birth_operators.values())
        support = {i for i, state in enumerate(frame.dipole.STATES) if state.family in ('ground', 'ion')}
        while True:
            following = support | {i for operator in operators for (i, j), value in operator.items()
                                   if value and j in support}
            if following == support:
                break
            support = following
        _require(all(not value or j not in support or i in support for operator in operators
                     for (i, j), value in operator.items()), 'the generated native face must be invariant')
        restricted_h = {(i, j): value for (i, j), value in h.items() if i in support and j in support}
        capture = source.captures[side].first_birth_rate if source.enabled[side] else Q(0)
        bound = 2*(frame.atomic._operator_upper(restricted_h, bits)+max(atom.outgoing[i] for i in support)+
            frame.bsm._entry_norm({(0, 0): frame.dipole.ComplexRadical(capture)}, bits=bits))
        total += bound
        sides.append({'side': side, 'source_generated_invariant_coordinates': sorted(support),
                      'full_H_and_all_natural_capture_jumps_checked': True,
                      'restricted_generator_norm_upper': str(field._price_upper(bound, bits))})
    return total, sides


def _distance(interval, point):
    return max(abs(value-point) for value in interval)


def _facts(parent, gate_seconds, control, policy, threshold_cover=None, receipt_support=None):
    ready = parent['reference_first_poll_ready']
    source = parent['reference_native_source_record']
    geometry = ready['same_physical_geometry']
    _require(ready['source_record'] == source and source['physical_geometry'] == geometry and
             control['reference_local_parent'] == parent,
             'Ready count faces, response and reference physical clock need the same source')
    times = {key: Q(value) for key, value in geometry['physical_seconds'].items()}
    start, poll, window = times['start'], times['stop'], times['rolling_APD_window']
    _require(start < poll == times['next_PC_poll'] and window > 0 and poll-start <= window,
             'new counted arrivals must lie wholly in the source recent integration window')
    faces = [face for face in ready['count_faces'] if face['PC_ready']]
    _require(faces, 'the same source must have an original Ready count face')
    # A zero numerical centre is not a zero source face.  Every structurally
    # admitted Ready count face remains in this universal support bound.
    recent = min(face['capped_new_count'] for face in faces)
    rules = {rule['name']: rule for rule in geometry['raw_PC_rules']}
    cover = max(rule['threshold'] for rule in rules.values())
    threshold_cover = cover if threshold_cover is None else threshold_cover
    _require(type(threshold_cover) is int and threshold_cover >= cover and
             recent >= threshold_cover > 0,
             'recent Ready count faces do not cover every subsequent native threshold')
    unit = Q(control['working_atomic_owner']['atomic_base']['seconds_per_unit'])
    _require(unit == Q(control['raw_receipt_timing']['seconds_per_unit']),
             'the same reference physical unit must interpret the response')
    offset = unit*max(Q(event['CEM_logic_deadline'])
                      for event in control['raw_receipt_timing']['relative_events'])
    gate = tuple(map(Q, gate_seconds))
    support = gate if receipt_support is None else tuple(map(Q, receipt_support))
    _require(len(support) == 2 and gate[0] <= support[0] <= support[1] <= gate[1],
             'the whole receipt support must remain in its original source gate')
    returned = tuple(time+offset for time in support)
    polls = tuple(_next_poll(time, times['poll_phase'], times['poll_period']) for time in returned)
    expiry = start+window
    _require(polls[1] < expiry,
             'the first subsequent native poll reaches the possible recent-arrival expiry')
    transitions = []
    for face in faces:
        stage = face['PC_stage'] if policy['target_stage'] is None else policy['target_stage']
        _require(stage in rules, 'raw return target stage is outside the original PC source')
        flags = [old if change is None else change for old, change in
                 zip(face['loaded_flags'], policy['flag_updates'])]
        following = _high(rules[stage], flags)
        following['PC_ready'] = rules[following['stage']]['ready']
        transitions.append({'original_ready_face_count': face['capped_new_count'],
            'return_stage': stage, 'return_loaded_flags': flags, 'first_native_high_successor': following})
    return {'recent_arrival_support_seconds': [str(start), str(poll)],
        'recent_arrival_support_left_closed': False, 'source_recent_count_lower': recent,
        'raw_native_threshold_cover': cover, 'requested_threshold_cover': threshold_cover,
        'source_rolling_window_seconds': str(window), 'earliest_possible_recent_expiry_seconds': str(expiry),
        'receipt_support_seconds': list(map(str, support)), 'CEM_completion_offset_seconds': str(offset),
        'raw_return_time_support_seconds': list(map(str, returned)),
        'first_subsequent_native_poll_support_seconds': list(map(str, polls)),
        'source_poll_phase_seconds': str(times['poll_phase']), 'source_poll_period_seconds': str(times['poll_period']),
        'all_native_polls_through_horizon_have_high_observation': True,
        'source_return_high_transitions': transitions,
        'hidden_arrival_times_selected': False, 'fine_queue_total_variation_inferred_from_marginal': False,
        'queue_reset': False, 'original_ready_label_reused_as_new_confirmation': False}


def _native_family_envelope(parent, facts, policy, lower, upper, anchor, face_index, bits):
    inlet.density.gaussian._precision(bits)
    lower, upper, anchor = map(inlet.full.nonnegative, (lower, upper, anchor))
    lo, hi = map(Q, facts['receipt_support_seconds'])
    _require(lo <= lower <= anchor <= upper <= hi,
             'the native family must use the same source receipt interval and anchor')
    faces = [f for f in parent['reference_first_poll_ready']['count_faces'] if f['PC_ready']]
    _require(type(face_index) is int and 0 <= face_index < len(faces), 'original source Ready count face required')
    offset = Q(facts['CEM_completion_offset_seconds'])
    phase, period = Q(facts['source_poll_phase_seconds']), Q(facts['source_poll_period_seconds'])
    returned = lower+offset, upper+offset
    polls = tuple(_next_poll(t, phase, period) for t in returned)
    anchor_return = anchor+offset
    anchor_poll = _next_poll(anchor_return, phase, period)
    if polls[0] == polls[1]:
        duration = polls[0]-returned[1], polls[0]-returned[0]
    else:
        # Across a lattice edge the delay is a sawtooth.  Endpoint
        # delays alone do not cover its values inside the interval.
        duration = Q(0), period
    origins = tuple(_phase_origin(parent, policy, faces[face_index], t) for t in returned)
    anchor_origin = _phase_origin(parent, policy, faces[face_index], anchor_return)
    restart = origins == returned
    if restart:
        start_age, end_age = (Q(0), Q(0)), duration
    else:
        _require(origins[0] == origins[1] == anchor_origin, 'one source phase-origin policy required')
        start_age = tuple(t-origins[0] for t in returned)
        end_age = tuple(t-origins[0] for t in polls)
    cell = _native_cell(parent, facts['source_return_high_transitions'][face_index])
    rotating, angular = _rotating_bound(cell, bits)
    restricted_rotating, invariant_faces = _ground_ION_face(cell, bits)
    gamma_hi = max(Q(parent['reference_clock']['Gamma_numerical_centre']),
                   Q(parent['reference_clock']['angular_Gamma_enclosure_per_second'][1]))
    semigroup = min(Q(2), gamma_hi*rotating*_distance(duration, anchor_poll-anchor_return))
    restricted_semigroup = min(Q(2), gamma_hi*restricted_rotating*_distance(duration, anchor_poll-anchor_return))
    start_price = min(Q(2), 2*gamma_hi*angular*_distance(start_age, anchor_return-anchor_origin))
    end_price = min(Q(2), 2*gamma_hi*angular*_distance(end_age, anchor_poll-anchor_origin))
    return {'schema': SCHEMA+'/uniform-native-return-family',     'source_receipt_interval_seconds': list(map(str, (lower, upper))),
        'source_anchor_receipt_seconds': str(anchor), 'source_ready_face_index': face_index,
        'source_return_interval_seconds': list(map(str, returned)),
        'source_first_poll_interval_seconds': list(map(str, polls)),
        'source_native_duration_interval_seconds': list(map(str, duration)),
        'source_initial_frame_age_interval_seconds': list(map(str, start_age)),
        'source_final_frame_age_interval_seconds': list(map(str, end_age)),
        'original_poll_lattice_crossed': polls[0] != polls[1], 'phase_restarted_at_return': restart,
        'source_constant_rotating_generator_norm_upper': str(field._price_upper(rotating, bits)),
        'source_two_atom_line_frame_frequency_norm_upper': str(field._price_upper(angular, bits)),
        'source_uniform_semigroup_difference_price': str(field._price_upper(semigroup, bits)),
        'source_uniform_initial_frame_difference_price': str(field._price_upper(start_price, bits)),
        'source_uniform_final_frame_difference_price': str(field._price_upper(end_price, bits)),
        'whole_native_operator_difference_per_input_norm': str(field._price_upper(min(Q(2), semigroup+start_price+end_price), bits)),
        'ground_ION_input_semigroup_difference_price': str(field._price_upper(restricted_semigroup, bits)),
        'ground_ION_source_generated_invariant_faces': invariant_faces,
        'ground_ION_input_operator_difference_per_input_norm': str(field._price_upper(min(Q(2), restricted_semigroup+end_price), bits)),
        'ground_ION_input_rule': 'both initial line-frame conjugations are identity on the original ground/ION compression',
        'source_family_map': 'Ad(U_end) exp(Gamma*G_rot*duration) Ad(U_start^dag)',
        'source_entire_Gamma_family_covered': True, 'CPTP_contraction_used_in_time_difference': True,
        'anchor_numeric_flow_error_included': False, 'whole_input_error_included': False,
        'ground_ION_projection_error_included': False, 'continuing_Gaussian_difference_included': False,
        'literal_queue_representative_used': False, 'native_endpoint_matrix_claimed': False}

class RetardedNativeCountCoimage:
    def __init__(self, source, control, *, return_policy=None, threshold_cover=None):
        _CHECK(); field._closed(source); field._closed(control)
        _require(type(source) is inlet.PreparedRetardedGaussianInlet and
                 type(control) is response.ReferenceResponseWindowSource,
                 'closed original retarded inlet and same-source response required')
        policy = native.RawReturnPolicy() if return_policy is None else return_policy
        _require(type(policy) is native.RawReturnPolicy, 'original raw return policy required')
        original = inlet.PreparedRetardedGaussianInlet.record(source)
        raw = response.ReferenceResponseWindowSource.record(control)
        parent = original['source_issued_two_pump_source']['reference_local_parent']
        gate = original['retarded_detector_law']['gate_seconds']
        policy_record = native.RawReturnPolicy.record(policy)
        facts = _facts(parent, gate, raw, policy_record, threshold_cover)
        self._source, self._control, self._policy = source, control, policy
        self._value = {'schema': SCHEMA, 'original_retarded_inlet_digest': _digest(original),
            'same_reference_response_digest': _digest(raw), 'raw_return_policy': policy_record,
            'requested_threshold_cover': facts['requested_threshold_cover'], 'source_count_support': facts,
            'source_mother_locator': 'source-issued two-pump parent/reference first-poll Ready/time and queue mother',
            'source_proof': 'every Ready face contains at least N new arrivals after the physical source start; before start+W none can expire',
            'new_arrivals_only_increase_the_rolling_count': True, 'native_quantum_endpoint_claimed': False,
            'actual_return_policy_identified': False, 'actual_hardware_uniquely_identified': False,
            'source_bindings': _bindings(), 'controller_advance': False}
        self._seal = _digest(self._value)
        _ISSUED[id(self)] = self._seal, source, control, policy

    def record(self):
        _CHECK(); field._closed(self)
        _require(type(self) is RetardedNativeCountCoimage and set(vars(self)) ==
            {'_source', '_control', '_policy', '_value', '_seal'} and
            _ISSUED.get(id(self)) == (self._seal, self._source, self._control, self._policy) and
            _digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
            _digest(inlet.PreparedRetardedGaussianInlet.record(self._source)) == self._value['original_retarded_inlet_digest'] and
            _digest(response.ReferenceResponseWindowSource.record(self._control)) == self._value['same_reference_response_digest'] and
            native.RawReturnPolicy.record(self._policy) == self._value['raw_return_policy'],
            'original count support, physical clock, return action or source changed')
        return actual.records._copy(self._value)

    def consume(self, record_source, event, first, second, admitted):
        raw = RetardedNativeCountCoimage.record(self)
        _require(type(record_source) is actual.RetardedActualRecordMeasure,
                 'the complete original actual-record source is required')
        actual.RetardedActualRecordMeasure.record(record_source)
        _require(record_source._source._measure._certificate._inlet is self._source and
            response.ReferenceResponseWindowSource.record(record_source._control) ==
            response.ReferenceResponseWindowSource.record(self._control),
            'the original record must consume this very source-issued retarded inlet')
        actual.RetardedActualRecordMeasure.verify(record_source, event, first, second, admitted)
        _require(not event['empty_admission_is_zero_instrument'], 'an absent CEM occurrence cannot generate a native confirmation epoch')
        parent = self._source._value['source_issued_two_pump_source']['reference_local_parent']
        control = response.ReferenceResponseWindowSource.record(self._control)
        facts = _facts(parent, self._source._value['retarded_detector_law']['gate_seconds'], control,
            raw['raw_return_policy'], raw['requested_threshold_cover'], event['source_receipt_restriction_seconds'])
        return {'schema': SCHEMA+'/original-CEM-return-high-poll', 'source_record': raw,
            'original_CEM_occurrence': _digest(event), 'original_pair': event['original_pair'],
            'source_generated_return_and_high_poll': facts,
            'new_confirmation_epoch': {'activation_time_support_seconds': facts['raw_return_time_support_seconds'],
                'first_native_poll_time_support_seconds': facts['first_subsequent_native_poll_support_seconds'],
                'first_native_poll_observation': 'at least the original rule threshold',
                'confirmation_uses_new_subsequent_source_poll': True},
            'complete_atomic_poststate_at_CEM_completion': actual.records._copy(event['selected_complete_matrix']),
            'CEM_poststate_trace_norm_error': event['complete_event_trace_norm_error'],
            'complete_quantum_time_field_queue_mother': actual.records._copy(event['complete_time_field_and_queue_mother']),
            'source_native_action_family': {'same_reference_native_source': parent['reference_native_source_record'],
                'raw_PC_rules': parent['reference_first_poll_ready']['same_physical_geometry']['raw_PC_rules'],
                'raw_return_policy': raw['raw_return_policy'], 'poll_clock_is_the_original_source_lattice': True,
                'source_generated_constant_cells': [_native_cell(parent, item) for item in facts['source_return_high_transitions']],
                'action_readout': 'native_action_column(receipt_seconds, elapsed_after_return_seconds, row, column)',
                'all_APD_arrivals_are_forgettable_until_the_source_high_poll': True,
                'quantum_state_at_poll_not_replaced_by_CEM_endpoint': True},
            'full_native_state_constructed': False, 'literal_arrival_archive_reconstructed': False,
            'expiry_refinement_mother_retained': True, 'full_nextRaw_history_scored': False,
            'controller_advance': False}

    def native_action_column(self, receipt_seconds, elapsed_after_return_seconds, row, column, *, face_index=0, bits=160):
        raw = RetardedNativeCountCoimage.record(self)
        inlet.density.gaussian._precision(bits)
        facts = raw['source_count_support']
        receipt, elapsed = Q(receipt_seconds), Q(elapsed_after_return_seconds)
        a, b = map(Q, facts['receipt_support_seconds'])
        _require(a <= receipt <= b and elapsed >= 0, 'source native action needs an original receipt coordinate')
        returned = receipt+Q(facts['CEM_completion_offset_seconds'])
        poll = _next_poll(returned, Q(facts['source_poll_phase_seconds']), Q(facts['source_poll_period_seconds']))
        _require(returned+elapsed <= poll, 'this generated native action ends at the first subsequent source poll')
        parent = self._source._value['source_issued_two_pump_source']['reference_local_parent']
        faces = [f for f in parent['reference_first_poll_ready']['count_faces'] if f['PC_ready']]
        _require(type(face_index) is int and 0 <= face_index < len(faces), 'original source Ready count face required')
        origin = _phase_origin(parent, raw['raw_return_policy'], faces[face_index], returned)
        transition = facts['source_return_high_transitions'][face_index]
        cell = _native_cell(parent, transition)
        clock = parent['reference_clock']; gamma = Q(clock['Gamma_numerical_centre'])
        image, error = _action_column(cell, gamma, returned+elapsed-origin, row, column, bits)
        bound, derivative = _action_bounds(cell, bits)
        gamma_hi = max(gamma, Q(clock['angular_Gamma_enclosure_per_second'][1]))
        family = Q(clock['Gamma_numerical_error'])*(bound+gamma_hi*(returned+elapsed-origin)*derivative)
        return {'schema': SCHEMA+'/source-native-generator-column', 'source_record': raw,
            'physical_receipt_seconds': str(receipt), 'raw_return_seconds': str(returned),
            'source_next_native_poll_seconds': str(poll), 'source_native_phase_origin_seconds': str(origin),
            'elapsed_after_return_seconds': str(elapsed), 'source_ready_face_index': face_index,
            'matrix_unit': [row, column], 'source_generated_exact_frame_cell': cell,
            'complete_native_generator_column_per_second': channel._input_record(image),
            'scalar_generator_error_per_second_upper': str(field._price_upper(error, bits)),
            'source_reference_clock': clock,
            'Gamma_family_generator_error_per_second_upper': str(field._price_upper(family, bits)),
            'complete_generator_error_per_second_upper': str(field._price_upper(error+family, bits)),
            'source_generator_norm_upper_per_second': str(field._price_upper(gamma_hi*bound, bits)),
            'source_normalized_generator_derivative_norm_upper': str(field._price_upper(derivative, bits)),
            'full_Zeeman_and_capture_in_source_action': True, 'mean_field_model_used': False,
            'literal_queue_representative_used': False, 'point_action_is_not_integrated_time_family': True,
            'reference_native_action': True, 'continuing_Gaussian_source_tail_retained_by_original_record': True}

    def native_family_envelope(self, lower, upper, anchor, *, face_index=0, bits=192):
        raw = RetardedNativeCountCoimage.record(self)
        parent = self._source._value['source_issued_two_pump_source']['reference_local_parent']
        result = _native_family_envelope(parent, raw['source_count_support'], raw['raw_return_policy'],
            lower, upper, anchor, face_index, bits)
        result['source_record'] = raw
        return result


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None)), repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None))


def _signature():
    functions = (_require, _digest, _bindings, _next_poll, _high, _facts, _native_cell, _phase_origin, _action_column, _action_bounds,
        _rotating_bound, _ground_ION_face, _distance, _native_family_envelope,
        _function, _signature, _check,
        inlet.PreparedRetardedGaussianInlet.record, response.ReferenceResponseWindowSource.record,
        native.RawReturnPolicy.__post_init__, native.RawReturnPolicy.record,
        actual.RetardedActualRecordMeasure.record, actual.RetardedActualRecordMeasure.verify,
        frame._phase_data, frame._ConstantSource.__init__, frame._ConstantSource.action, frame._commute,
        frame.local._add, channel.modes.complex_exponential, frame.bsm._entry_norm, frame.atomic._operator_upper,
        inlet.density.gaussian._precision,
        actual.records._copy, channel._canonical, field._closed)
    methods = tuple(_function(v) for v in vars(RetardedNativeCountCoimage).values() if callable(v))
    return tuple(map(_function, functions)), methods, SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
        inlet._CHECK is _INLET_CHECK and response._CHECK is _RESPONSE_CHECK and
        actual._CHECK is _ACTUAL_CHECK and native._CLOSED is _NATIVE_CHECK and frame._GUARD is _FRAME_CHECK,
        'recent-count source execution changed')
    _INLET_CHECK(); _RESPONSE_CHECK(); _ACTUAL_CHECK(); _NATIVE_CHECK(); _FRAME_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
