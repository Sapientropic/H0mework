"""Finite same-source gate producer for the prepared retarded carrier.

The source-derived pump-end coimage first follows both unconditional local
flows to their true retarded gate cuts.  All pre-gate port/loss words are
forgotten there; the original field/time/queue mother is retained.  The leading
one-nanosecond slice of the original detector gate is propagated by the
actual ``G0+4J`` images emitted by ``RetardedPreparedExcitationFieldSource``.
The original four-port Mark law then runs on the complete 45-Mark stopped
inventory; first-receipt coimages retain their own receipt clock.  Subsequent
physical evolution remains with the original field/time mother.  This leading
slice is a gate-local pre-gate coordinate, not an
excitation-origin-to-gate-start extrapolation.

The finite source-time proposal is deliberately a checked numerical trial.
It keeps the retarded clock, the complete time/PC/queue mother and all Mark
coordinates in the certificate, so a later independent residual consumer can
replace the trial without changing the source mouth.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import hashlib
import json

import bsm_retry_source as bsm
import common_optical_readout as optical
import retarded_prepared_excitation_field_source as excitation
import temporal_response_anchor as response_anchor

field = excitation.field
channel = excitation.channel
joint = excitation.joint
dipole = excitation.dipole
full = excitation.full

SCHEMA = 'stage10-same-preparation-retarded-finite-gate/v3'
_SOURCE_CHECK = excitation._CHECK
_ISSUED = {}


def _require(value, message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), Path(excitation.__file__), Path(bsm.__file__),
             Path(optical.__file__), Path(response_anchor.__file__))}


def _add_mark(result, mark, matrix, factor=Q(1)):
    field._add(result, {(mark, i, j): value for (i, j), value in matrix.items()}, factor)


def _marked_blocks(state):
    _require(type(state) is dict, 'complete source Marked state required')
    result = {}
    for key, value in state.items():
        _require(type(key) is tuple and len(key) == 3 and type(key[0]) is bsm.Mark,
                 'source Mark and full pair matrix address required')
        matrix = joint._matrix({key[1:]: value})
        if matrix:
            result.setdefault(key[0], {}).update(matrix)
    return result


def _record_marked_state(state):
    _marked_blocks(state)
    key = lambda item: (item[0][0].counts, -1 if item[0][0].receipt is None else item[0][0].receipt, *item[0][1:])
    return [[list(mark.counts), mark.receipt, i, j, value.serialize()]
            for (mark, i, j), value in sorted(state.items(), key=key) if value]


def _state_norm(state, bits):
    return sum((bsm._entry_norm(matrix, bits=bits) for matrix in _marked_blocks(state).values()), Q(0))


def _target(gate, mark, port):
    _require(type(mark) is bsm.Mark and type(port) is int and 0 <= port < 4,
             'original source Mark and physical APD port required')
    return gate.target(mark, port)


def _mark_inventory(gate):
    """Enumerate exactly the source-reachable original Mark inventory."""
    seen, pending = {bsm.INITIAL}, [bsm.INITIAL]
    while pending:
        mark = pending.pop()
        if mark.receipt is not None:
            continue
        for port in range(4):
            target = _target(gate, mark, port)
            if target not in seen:
                seen.add(target)
                pending.append(target)
    return tuple(sorted(seen, key=lambda m: (m.counts, -1 if m.receipt is None else m.receipt)))


def _generator_action(source, gate, state, detector_seconds, receipt_seconds,
                      ready_face, member, *, bits):
    """Apply one source-time generator and split new first receipts."""
    result, flux, source_error = {}, [dict() for _ in bsm.PATTERNS], Q(0)
    for mark, matrix in _marked_blocks(state).items():
        if mark.receipt is not None:
            continue
        report = source.retarded_generator(detector_seconds, receipt_seconds, ready_face,
                                          member, matrix, bits=bits)
        pending = channel._read_input(report['no_arrival_generator_image_per_second'], joint.DIMENSION)
        _add_mark(result, mark, pending)
        source_error += Q(report['source_scalar_generator_error_per_second_per_input_norm']) * bsm._entry_norm(matrix, bits=bits)
        jumps = [channel._read_input(value, joint.DIMENSION)
                 for value in report['four_physical_port_jump_images_per_second']]
        for port, jump in enumerate(jumps):
            target = _target(gate, mark, port)
            _add_mark(result, target, jump)
            if mark.receipt is None and target.receipt is not None:
                field._add(flux[target.receipt], jump)
    return result, tuple(flux), source_error


def _scaled_add_marked(target, source, factor):
    field._add(target, source, factor)


def _unobserved_image(primitives, matrix):
    """Before the gate, summing all port/loss words gives the local natural baths."""
    result, scalar = {}, Q(0)
    for side, primitive in primitives:
        k = excitation.gaussian._matrix(primitive['complete_K_per_second'])
        field._add(result, joint._operator_left(matrix, side, k))
        field._add(result, joint._operator_right(matrix, side, dipole.matrix_adjoint(k)))
        for jump in primitive['original_resolved_natural_jumps']:
            operator = excitation.gaussian._matrix(jump['normalized_natural_jump_operator'])
            image = joint._operator_right(joint._operator_left(matrix, side, operator), side, dipole.matrix_adjoint(operator))
            field._add(result, image, Q(jump['physical_amplitude_squared_per_second']))
        scalar += 2*Q(primitive['H_scalar_operator_error_upper_per_second'])
    return result, scalar*bsm._entry_norm(matrix)


def _unobserved_gate_input_piece(source, matrix, start, width, origin, flights,
                                 receipt, face, member, *, order, bits):
    midpoint = start+width/2
    primitives = [(side, source.primitive_fibre(side, receipt, face, midpoint-origin-flight, member, bits=bits))
                  for side, flight in enumerate(flights) if midpoint >= origin+flight]
    current, centre, action_error = matrix, {}, Q(0)
    for degree in range(order+1):
        field._add(centre, current, width**degree/factorial(degree))
        following, error = _unobserved_image(primitives, current)
        action_error += error*width**(degree+1)/factorial(degree+1)
        if degree == order:
            remainder = width**(degree+1)*bsm._entry_norm(following)/factorial(degree+1)
            break
        current = following
    return centre, action_error+remainder, {
        'detector_interval_seconds': list(map(str, (start, start+width))),
        'active_retarded_sides': [side for side, _ in primitives],
        'midpoint_retarded_local_seconds': [str(midpoint-origin-flights[side]) for side, _ in primitives],
        'source_action_error_integral': str(action_error), 'constant_midpoint_Taylor_remainder_upper': str(remainder),
        'all_natural_and_unobserved_port_words_summed': True,
        'background_identity_cancels_before_gate': True, 'pre_gate_photons_counted_as_gate_clicks': False,
        'source_time_variation_priced': False, 'independent_uniform_residual_required': True}


def _gate_input_partition(start, stop, births, count):
    _require(start <= stop and type(count) is int and count > 0, 'ordered retarded inlet interval and positive piece budget required')
    cuts = sorted({start, stop, *(t for t in births if start < t < stop)})
    return tuple(piece for a, b in zip(cuts, cuts[1:]) for piece in _partition(a, b, count))


def _integrate_piece(source, gate, state, flux, detector_start, width,
                     receipt_seconds, ready_face, member, *, order, bits):
    """Constant-midpoint source-time GKSL Taylor piece with first-receipt flux."""
    detector_start, width = full.nonnegative(detector_start), full.nonnegative(width)
    _require(width > 0 and type(order) is int and 0 <= order <= 12,
             'positive finite source gate piece and registered Taylor order required')
    detector = detector_start + width/2
    current, centre, source_flux = state, {}, [dict() for _ in bsm.PATTERNS]
    derivative_error, action_error = Q(0), Q(0)
    for degree in range(order + 1):
        coefficient = width**degree / factorial(degree)
        _scaled_add_marked(centre, current, coefficient)
        next_state, rates, source_error = _generator_action(source, gate, current, detector,
                                                             receipt_seconds, ready_face, member, bits=bits)
        for index, rate in enumerate(rates):
            _scaled_add_marked(source_flux[index], rate, width**(degree+1) / factorial(degree+1))
        action_error += source_error * width**(degree+1) / factorial(degree+1)
        if degree == order:
            break
        current = next_state
    remainder, _, tail_error = _generator_action(source, gate, current, detector,
                                                 receipt_seconds, ready_face, member, bits=bits)
    derivative_error = width**(order+1) * (_state_norm(remainder, bits) + tail_error) / factorial(order+1)
    next_flux = tuple({key: value for key, value in matrix.items() if value} for matrix in source_flux)
    gate.blocks(centre)
    return centre, next_flux, derivative_error + action_error, {
        'detector_midpoint_seconds': str(detector), 'duration_seconds': str(width),
        'taylor_order': order, 'source_action_error_integral': str(action_error),
        'Taylor_remainder_upper': str(derivative_error),
        'all_original_mark_coordinates_retained': True,
        'midpoint_generator_is_not_a_gate_end_state': True}


def _sum_flux(flux, destination, factor=Q(1)):
    for matrix in flux:
        for key, value in matrix.items():
            field._add(destination, key, value, factor)


def _trace(matrix):
    return joint._trace(matrix)


def _input_from_terms(terms):
    result = {}
    for left, right in terms:
        field._add(result, excitation.driven.original._tensor(left, right))
    _require(result and all(result.get((j, i), dipole.ComplexRadical()) == value.conjugate()
                            for (i, j), value in result.items()),
             'source-projected coimage must provide a Hermitian joint input')
    return result


def _mass_row(matrix, error, herald, bits=192):
    centre = _trace(matrix)
    _require(not centre.imag, 'Hermitian source receipt mass must be real')
    rational, rounding = full.radical_midpoint(centre.real, bits)
    radius = full.nonnegative(error)+rounding
    return {'herald': herald, 'poststate': channel._input_record(matrix),
            'mass_center': centre.serialize(), 'rational_mass_center': str(rational),
            'trace_scalar_rounding': str(rounding), 'mass_interval': [str(rational-radius), str(rational+radius)],
            'trace_error_upper': str(radius), 'positive_mass_not_assumed': True}


class RetardedPreparedGateSource:
    def __init__(self, source, member, *, receipt_seconds, Ready_face_index=0,
                 pre_gate_seconds=Q(1, 10**9)):
        _CHECK()
        _require(type(source) is excitation.RetardedPreparedExcitationFieldSource and
                 type(member) is excitation.ExcitationClockMember,
                 'same source-issued excitation carrier and fixed member required')
        raw = source.record(); point = source._member(member)
        projection = source.joint_common_line_input_projection(member)
        tensors = source.source_tensors(member)
        _require(projection['source_carrier_digest'] == raw['source_digest'] and
                 tensors['source_record'] == raw and
                 type(Ready_face_index) is int and Ready_face_index >= 0,
                 'same positive coimage and complete time/PC mother required')
        _require(type(pre_gate_seconds) is Q and pre_gate_seconds > 0,
                 'positive local pre-gate interval required')
        common = optical.CommonOpticalReadout.from_record(raw['working_common_optical_source'])
        gate, gate_report = common.bsm_gate(compilation_bits=160)
        gate_raw = bsm.BSMSource.record(gate)
        marks = _mark_inventory(gate)
        _require(len(marks) == 45, 'the original finite gate must retain all 45 source Mark targets')
        origin = Q(source.time_phase_fibre(receipt_seconds, Ready_face_index, 0, member)['source_excitation_origin_seconds'])
        flights = tuple(map(Q, raw['flight_seconds']))
        gate_offsets = tuple(map(Q, raw['source_gate_offsets_from_pump_end_seconds']))
        gate_start, gate_end = origin+gate_offsets[0], origin+gate_offsets[1]
        _require(gate_start >= origin+max(flights), 'both retarded gate cuts must follow the same source excitation origin')
        local_start = gate_start + pre_gate_seconds
        _require(gate_start <= local_start < gate_end,
                 'one-nanosecond pre-gate propagation must remain inside the original gate')
        projected_terms = tuple((dict(a), dict(b)) for a, b in projection['projected_source_tensor_terms'])
        initial = _input_from_terms(projected_terms)
        self._source, self._member, self._gate = source, member, gate
        self._terms = excitation._freeze_terms(projected_terms)
        self._value = {'schema': SCHEMA, 'source_excitation_record': raw,
            'fixed_same_history_excitation_member': point,
            'source_derived_joint_input_projection': projection['source_derived_projection_price'],
            'whole_quantum_coimage_error_once': tensors['whole_upstream_trace_norm_error'],
            'same_positive_joint_mother_mass_upper': tensors['same_positive_CEM_mass_upper'],
            'retained_original_joint_time_field_queue_mother': tensors['whole_original_time_field_queue_mother'],
            'source_preparation_end_time_family_seconds': list(map(str, tensors['source_preparation_end_time_family_seconds'])),
            'raw_BSM_gate': gate_raw, 'raw_BSM_gate_report': gate_report,
            'source_mark_inventory': [{'counts': list(mark.counts), 'receipt': mark.receipt} for mark in marks],
            'source_mark_inventory_count': len(marks),
            'source_gate_seconds': list(map(str, (gate_start, gate_end))),
            'source_excitation_origin_seconds': str(origin), 'source_flight_seconds': list(map(str, flights)),
            'source_retarded_gate_input_cuts_seconds': [str(gate_start-origin-flight) for flight in flights],
            'unobserved_gate_input_interval_seconds': list(map(str, (origin+min(flights), gate_start))),
            'pre_gate_interval_seconds': list(map(str, (gate_start, local_start))),
            'pre_gate_scope': 'leading one-nanosecond slice inside the original detector gate; not excitation-origin propagation',
            'local_gate_interval_seconds': list(map(str, (local_start, gate_end))),
            'pre_gate_seconds': str(pre_gate_seconds), 'receipt_seconds': str(full.exact(receipt_seconds)),
            'Ready_face_index': Ready_face_index, 'initial_projected_matter': channel._input_record(initial),
            'all_original_mark_targets_retained': True,
            'first_receipt_quantum_coimage_frozen_at_its_own_clock': True,
            'all_photon_numbers_resummed_by_marked_GKSL': True,
            'background_added_once_by_source_retarded_generator': True,
            'source_time_and_clock_mother_retained': True,
            'source_scope': 'same source positive coimage through pre-gate and finite original detector gate',
            'actual_hardware_member_asserted': False, 'source_bindings': _bindings(),
            'controller_advance': False}
        self._seal = _digest(self._value)
        _ISSUED[id(self)] = self._seal, source, member, gate, self._terms

    def record(self):
        _CHECK()
        _require(type(self) is RetardedPreparedGateSource and set(vars(self)) ==
                 {'_source', '_member', '_gate', '_terms', '_value', '_seal'} and
                 _ISSUED.get(id(self)) == (self._seal, self._source, self._member, self._gate, self._terms) and
                 _digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
                 self._source.record() == self._value['source_excitation_record'] and
                 self._source._member(self._member) == self._value['fixed_same_history_excitation_member'] and
                 bsm.BSMSource.record(self._gate) == self._value['raw_BSM_gate'],
                 'same source coimage, Mark gate, clock member or retained mother changed')
        return _copy(self._value)

    def _initial(self):
        return channel._read_input(self._value['initial_projected_matter'], joint.DIMENSION)

    def finite_first_receipt(self, *, order=4, bits=128, inlet_pieces=1, pre_gate_pieces=1, gate_pieces=1):
        raw = self.record(); _CHECK(); excitation.gaussian._precision(bits)
        _require(type(order) is int and 0 <= order <= 12 and type(pre_gate_pieces) is int and pre_gate_pieces > 0 and
                 type(gate_pieces) is int and gate_pieces > 0 and type(inlet_pieces) is int and inlet_pieces > 0,
                 'registered finite inlet/gate trial controls required')
        receipt, face = Q(raw['receipt_seconds']), raw['Ready_face_index']
        pre_start, pre_end = map(Q, raw['pre_gate_interval_seconds'])
        gate_start, gate_end = map(Q, raw['local_gate_interval_seconds'])
        matter = self._initial()
        inherited = Q(raw['whole_quantum_coimage_error_once'])
        projection = Q(raw['source_derived_joint_input_projection']['joint_mother_projection_trace_norm_upper'])
        total_error = inherited + projection; pieces, pre_flux = [], [dict() for _ in bsm.PATTERNS]
        inlet_start, inlet_stop = map(Q, raw['unobserved_gate_input_interval_seconds'])
        origin = Q(raw['source_excitation_origin_seconds']); flights = tuple(map(Q, raw['source_flight_seconds']))
        for left, right in _gate_input_partition(inlet_start, inlet_stop, tuple(origin+f for f in flights), inlet_pieces):
            matter, error, paid = _unobserved_gate_input_piece(self._source, matter, left, right-left, origin, flights,
                receipt, face, self._member, order=order, bits=bits)
            pieces.append({'stage': 'unobserved_inlet', 'payment': str(error), **paid})
            total_error += error
        state = {(bsm.INITIAL, i, j): value for (i, j), value in matter.items()}
        gate_input = channel._input_record(matter)
        for left, right in _partition(pre_start, pre_end, pre_gate_pieces):
            state, flux, error, paid = _integrate_piece(self._source, self._gate, state, pre_flux,
                left, right-left, receipt, face, self._member, order=order, bits=bits)
            for index, matrix in enumerate(flux):
                field._add(pre_flux[index], matrix)
            pieces.append({'stage': 'pre_gate', 'interval_seconds': [str(left), str(right)], 'payment': str(error), **paid})
            total_error += error
        for left, right in _partition(gate_start, gate_end, gate_pieces):
            state, flux, error, paid = _integrate_piece(self._source, self._gate, state, pre_flux,
                left, right-left, receipt, face, self._member, order=order, bits=bits)
            for index, matrix in enumerate(flux):
                field._add(pre_flux[index], matrix)
            pieces.append({'stage': 'gate', 'interval_seconds': [str(left), str(right)], 'payment': str(error), **paid})
            total_error += error
        rows = [_mass_row(matrix, total_error, bsm.PATTERNS[index][0], bits) for index, matrix in enumerate(pre_flux)]
        pending = {key: value for key, value in state.items() if key[0].receipt is None}
        absorbed = {key: value for key, value in state.items() if key[0].receipt is not None}
        return {'schema': SCHEMA+'/finite-first-receipt', 'source_record': raw,
            'source_gate_record': bsm.BSMSource.record(self._gate),
            'source_mark_inventory_count': len(_mark_inventory(self._gate)),
            'initial_projected_matter': raw['initial_projected_matter'],
            'source_retarded_gate_input_trial': gate_input, 'inlet_pieces_per_activation_cell': inlet_pieces,
            'pre_gate_and_gate_pieces': pieces, 'final_marked_state': _record_marked_state(state),
            'pending_marked_state': _record_marked_state(pending),
            'absorbed_marked_state': _record_marked_state(absorbed),
            'first_receipt_flux_by_pattern': [channel._input_record(matrix) for matrix in pre_flux],
            'temporal_response_anchor_rows': rows,
            'whole_trace_norm_error': str(total_error),
            'scalar_bits': bits, 'taylor_order': order,
            'pre_gate_full_G0_plus_four_J_consumed': True,
            'original_gate_target_and_first_receipt_measure_consumed': True,
            'all_original_45_mark_targets_retained': True,
            'first_receipt_quantum_coimage_frozen_at_its_own_clock': True,
            'all_photon_numbers_resummed': True,
            'same_source_time_PC_queue_mother_retained': True,
            'source_pump_endpoint_used_directly_at_gate_start': False,
            'both_true_retarded_gate_input_cuts_propagated': True,
            'finite_time_trial_requires_independent_residual': True,
            'response_anchor_is_source_output_not_empirical_input': True,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False,
            'source_bindings': _bindings()}

    def verify_finite_first_receipt(self, report):
        _require(type(report) is dict and report.get('schema') == SCHEMA+'/finite-first-receipt' and
                 report.get('source_record') == self.record(), 'same source finite first-receipt certificate required')
        pieces = report['pre_gate_and_gate_pieces']
        expected = self.finite_first_receipt(order=report['taylor_order'], bits=report['scalar_bits'],
                                             inlet_pieces=report['inlet_pieces_per_activation_cell'],
                                             pre_gate_pieces=sum(p['stage'] == 'pre_gate' for p in pieces),
                                             gate_pieces=sum(p['stage'] == 'gate' for p in pieces))
        _require(expected == report, 'source finite Mark action, first receipt flux or paid error changed')
        return True

    def response_anchor(self, report):
        self.verify_finite_first_receipt(report)
        return {'schema': response_anchor.SCHEMA+'/direct-source-gate',
            'finite_first_receipt_source': report,
            'source_response_rows': report['temporal_response_anchor_rows'],
            'response_rows_are_source_intervals': True,
            'empirical_response_interval_required_for_inverse': True,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False}


def _partition(start, stop, count):
    start, stop = full.nonnegative(start), full.nonnegative(stop)
    _require(type(count) is int and count > 0 and start < stop, 'positive source interval partition required')
    return tuple((start + (stop-start)*i/count, start + (stop-start)*(i+1)/count) for i in range(count))


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None)), repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None))


def _signature():
    functions = (_require, _copy, _digest, _bindings, _add_mark, _marked_blocks, _record_marked_state, _state_norm,
        _target, _mark_inventory, _generator_action, _scaled_add_marked, _integrate_piece, _sum_flux, _trace,
        _unobserved_image, _unobserved_gate_input_piece, _gate_input_partition,
        _input_from_terms, _mass_row, _partition, _function, _signature, _check,
        excitation._freeze_terms, excitation.RetardedPreparedExcitationFieldSource.record,
        excitation.RetardedPreparedExcitationFieldSource._member,
        excitation.RetardedPreparedExcitationFieldSource.source_tensors,
        excitation.RetardedPreparedExcitationFieldSource.joint_common_line_input_projection,
        excitation.RetardedPreparedExcitationFieldSource.time_phase_fibre,
        excitation.RetardedPreparedExcitationFieldSource.retarded_generator,
        excitation.RetardedPreparedExcitationFieldSource.primitive_fibre,
        excitation.channel._canonical, excitation.channel._input_record,
        excitation.channel._read_input, excitation.field._add, excitation.driven.original._tensor,
        bsm.BSMSource.record, bsm.BSMSource.target, bsm.BSMSource.blocks,
        bsm._entry_norm, optical.CommonOpticalReadout.from_record,
        optical.CommonOpticalReadout.bsm_gate, joint._matrix, joint._trace,
        full.exact, full.nonnegative)
    methods = tuple(_function(value) for value in vars(RetardedPreparedGateSource).values() if callable(value))
    return tuple(map(_function, functions)), methods, SCHEMA, joint.DIMENSION, len(bsm.PATTERNS)


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             excitation._CHECK is _SOURCE_CHECK, 'same-preparation finite gate source execution changed')
    _SOURCE_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
