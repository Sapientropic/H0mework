"""Whole-flow Gaussian tail comparison from the original auxiliary GKSL.

Removing an original Hamiltonian drive after its source tail cut defines a
mathematical CP flow with unchanged baths, counters and receipt frames.
The numerical curve is checked against that complete flow; the original
physical drive is restored by a source-generated whole Duhamel price.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import lcm
import hashlib

import retarded_gaussian_tail_certificate as original

tail, clustered, fixed = original.tails, original.clustered, original.fixed
checked, integer, trajectory, gaussian, field, full = (original.checked, original.integer,
    original.trajectory, original.gaussian, original.field, original.full)
dipole, joint, bsm = trajectory.dipole, trajectory.joint, trajectory.bsm
SCHEMA = 'stage10-original-retarded-whole-Gaussian-tail-Duhamel-certificate/v1'
_ORIGINAL_CHECK = original._CHECK
_ISSUED = {}
PRICINGS = ('auxiliary_cptp', 'original_coefficients')


def _require(value, message):
    if not value:
        raise ValueError(message)


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), *(Path(m.__file__) for m in (original, tail, clustered, fixed, integer, checked,
         trajectory, trajectory.retarded, trajectory.density, gaussian, joint, bsm)))}


def _pricing(value):
    _require(type(value) is str and value in PRICINGS, 'named whole-flow or original-coefficient tail pricing required')
    return value


def _source_cp_contract(source):
    raw = trajectory.RetardedGaussianTrajectorySource.record(source); law = source._law
    transfer, gram, loss = joint.passive_transfer(law._transfer)
    _require(transfer == law._transfer and gram == law._gram and loss == law._loss,
             'the auxiliary flow must retain the original passive detector and complement')
    _require(all(gram[i][j]+loss[i][j] == dipole.ComplexRadical(int(i == j))
                 for i in range(6) for j in range(6)), 'whole observed/unobserved Gram identity required')
    generated_marks = trajectory._inventory(law._gate)
    _require(generated_marks == source._marks and all(mark.receipt is not None or
        all(bsm.BSMSource.target(law._gate, mark, port) in generated_marks for port in range(4))
        for mark in generated_marks), 'the complete original stopped Mark carrier must be closed')
    beta = tuple(map(full.nonnegative, raw['retarded_source']['BG_source']['BG_rates_per_second']))
    legs = raw['retarded_source']['complete_driven_field_source']['Gaussian_source_legs']; contracts = []
    for side, (leg, parts) in enumerate(zip(legs, source._parts)):
        pulse = law._field._pulses[side]
        _require(gaussian.GaussianAtomicPulseSource.record(pulse) == leg, 'same original pulse and natural bath required')
        recovered = {}
        for _, rate, modes in law._groups:
            _require(rate >= 0, 'original nonnegative natural widths required')
            for _, (owner, jump) in modes:
                if owner == side:
                    field._add(recovered, dipole.matrix_product(dipole.matrix_adjoint(jump), jump), rate)
        natural = gaussian._matrix(leg['complete_natural_R_per_second'])
        _require(recovered == natural, 'all resolved source jumps must recover the original complete natural R')
        k, v = parts[:2]
        identity = dict(k); field._add(identity, dipole.matrix_adjoint(k)); field._add(identity, natural)
        _require(not identity and not gaussian._sum(v, dipole.matrix_adjoint(v)),
                 'the original quiet drift and optional Hamiltonian drive must retain their exact CP identities')
        contracts.append({'source_side': side, 'all_original_natural_jump_groups_checked': True,
            'quiet_K_plus_K_adjoint_plus_R_is_zero': True, 'drive_V_plus_V_adjoint_is_zero': True,
            'source_pulse_record_digest': pulse._seal})
    return {'schema': SCHEMA+'/whole-auxiliary-GKSL-contract',
        'original_stopped_trajectory_source': raw,
        'complete_source_mark_inventory': len(generated_marks), 'two_original_local_CP_identities': contracts,
        'original_background_rates_per_second': list(map(str, beta)),
        'detected_and_loss_Gram_are_original_passive_complements': True,
        'relative_line_phases_conjugate_the_original_Grams_by_unitaries': True,
        'inactive_arms_use_the_same_source_Gram_principal_compression': True,
        'source_line_phases_are_exact_mathematical_phases': True,
        'rounded_scalar_centres_are_not_assumed_unitary': True,
        'every_pending_to_original_receipt_transfer_is_retained': True,
        'receipt_blocks_keep_the_original_unitary_counterflow': True,
        'auxiliary_semantics': 'only source-selected pending Hamiltonian drives are omitted; every original jump and counter remains',
        'whole_direct_sum_flow_is_CPTP': True,
        'contraction_scope': 'whole Hermitian direct-sum trace norm, including signed matrices',
        'candidate_positive_assumed': False, 'physical_source_drive_turned_off': False,
        'source_bindings': _bindings(), 'controller_advance': False}


def _source_schedule(source, bits, policy, interval, durations):
    raw = trajectory.RetardedGaussianTrajectorySource.record(source)
    native = raw['retarded_source']; driven = native['complete_driven_field_source']
    g0, g1 = map(Q, native['gate_seconds'])
    start, stop = (g0, g1) if interval is None else tuple(map(full.nonnegative, interval))
    _require(g0 <= start <= stop <= g1, 'the auxiliary schedule must retain the original source gate')
    births = tuple(Q(a)+Q(b) for a, b in zip(driven['emission_origins_seconds'], driven['flight_seconds']))
    cuts = tuple(birth+tail._tail_cut(leg, bits) for birth, leg in zip(births, driven['Gaussian_source_legs']))
    if durations is None:
        edges = sorted({start, stop} | {value for value in (*births, *cuts) if start < value < stop})
        durations = tuple(second-first for first, second in zip(edges, edges[1:]))
    _require(type(durations) in (tuple, list), 'complete numerical source-clock piece durations required')
    time = start; result = []
    for duration in durations:
        width = full.exact(duration)
        _require(width > 0 and time+width <= stop, 'ordered positive source auxiliary pieces required')
        _require(not any(time < birth < time+width for birth in births), 'partition the original source activation boundary')
        local, active = trajectory.RetardedGaussianTrajectorySource._clock(source, time)
        discarded = tuple(side for side, (coordinate, on, leg) in enumerate(zip(local, active, driven['Gaussian_source_legs']))
            if on and policy == 'source_tail' and coordinate >= tail._tail_cut(leg, bits))
        result.append({'source_detector_interval_seconds': list(map(str, (time, time+width))),
            'source_selected_math_drive_omissions': list(discarded),
            'original_source_local_start_seconds': list(map(str, local)),
            'rule': 'same piece-start source test as the complete residual; drive remains through a crossing piece'})
        time += width
    _require(time == stop, 'the auxiliary schedule must cover the entire declared original interval')
    return (start, stop), result


class RetardedAuxiliaryTailGKSL:
    def __init__(self, owner, *, coefficient_bits=192, tail_policy='source_tail',
                 source_interval_seconds=None, source_piece_durations=None):
        _CHECK(); gaussian._precision(coefficient_bits); tail.policy(tail_policy)
        _require(type(owner) is checked.RetardedReceiptTrajectoryCertificate,
                 'closed original retarded source required; an auxiliary target or turnoff command is not input')
        owner_raw = checked.RetardedReceiptTrajectoryCertificate.record(owner)
        source = owner._source
        value = _source_cp_contract(source)
        interval, schedule = _source_schedule(source, coefficient_bits, tail_policy,
            source_interval_seconds, source_piece_durations)
        value.update(coefficient_bits=coefficient_bits, residual_policy=tail.policy(tail_policy))
        value.update(source_piecewise_omission_schedule=schedule,
            source_detector_interval_seconds=list(map(str, interval)),
            original_complete_trajectory_certificate_owner=owner_raw,
            time_retaining_instrument_lift={
                'source_first_receipt_time_write': 'same original detector clock and first BSM target, before time marginalisation',
                'jump_groups_ports_background_and_all_time_writes_are_unchanged': True,
                'same_original_atom_field_dilation': source._value['retarded_source']['complete_driven_field_source'],
                'same_original_inlet_time_field_queue_mother': None if owner._inlet is None else
                    owner_raw['source_issued_inlet']['retained_pump_field_and_queue_mother'],
                'source_issued_mother_retained_by_the_same_inlet_pointer': owner._inlet is not None,
                'lifted_perturbation': 'original omitted Hdrive acts on atoms tensor identity on retained time, field and queue',
                'whole_lifted_flow_is_CP_and_trace_preserving': True,
                'comparison_is_before_first_receipt_time_projection': True,
                'comparison_norm_scope': 'complete quantum x first-receipt-time instrument, with the same retained field/queue mother',
                'a_CDF_or_final_Mark_price_is_not_substituted_for_time_TV': True})
        self._owner, self._inlet = owner, owner._inlet
        self._source, self._bits, self._policy = source, coefficient_bits, tail_policy
        self._value, self._seal = value, checked._digest(value)
        _ISSUED[id(self)] = owner, source, owner._inlet, coefficient_bits, tail_policy, self._seal

    def record(self):
        _CHECK(); field._closed(self)
        _require(type(self) is RetardedAuxiliaryTailGKSL and set(vars(self)) ==
            {'_owner', '_inlet', '_source', '_bits', '_policy', '_value', '_seal'} and
            _ISSUED.get(id(self)) == (self._owner, self._source, self._inlet, self._bits, self._policy, self._seal) and
            checked._digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
            self._owner._source is self._source and self._owner._inlet is self._inlet and
            checked.RetardedReceiptTrajectoryCertificate.record(self._owner) ==
                self._value['original_complete_trajectory_certificate_owner'] and
            trajectory.RetardedGaussianTrajectorySource.record(self._source) == self._value['original_stopped_trajectory_source'],
            'the original auxiliary source, bath, complete Mark carrier or policy changed')
        return checked._copy(self._value)

    def discarded_sides(self, time):
        RetardedAuxiliaryTailGKSL.record(self)
        time = full.nonnegative(time)
        start, stop = map(Q, self._value['source_detector_interval_seconds'])
        _require(start <= time <= stop, 'the auxiliary action must use the same complete source clock schedule')
        schedule = self._value['source_piecewise_omission_schedule']
        if not schedule:
            return ()
        selected = next((piece for piece in schedule if Q(piece['source_detector_interval_seconds'][0]) <= time <
            Q(piece['source_detector_interval_seconds'][1])), schedule[-1] if time == stop else None)
        _require(selected is not None, 'same source piece clock required')
        return tuple(selected['source_selected_math_drive_omissions'])

    def action_and_price(self, time, state):
        RetardedAuxiliaryTailGKSL.record(self)
        local, active = trajectory.RetardedGaussianTrajectorySource._clock(self._source, time)
        discarded = RetardedAuxiliaryTailGKSL.discarded_sides(self, time)
        source_raw = self._source._value['retarded_source']['complete_driven_field_source']
        births = tuple(Q(a)+Q(b) for a, b in zip(source_raw['emission_origins_seconds'], source_raw['flight_seconds']))
        omega = tuple(Q(leg['carrier_angular_frequency_per_second']) for leg in source_raw['Gaussian_source_legs'])
        answer = {}; price = Q(0)
        for component in trajectory.COMPONENTS:
            if component == 'quiet':
                scalar, error = (Q(1), Q(0)), Q(0)
            elif component[0] == 'drive':
                side = component[1]
                if not active[side] or side in discarded:
                    continue
                leg = source_raw['Gaussian_source_legs'][side]
                offset = local[side]-Q(leg['centre_seconds'])
                scalar, error = gaussian._exponential(-offset*offset/(4*Q(leg['sigma_squared_seconds'])), Q(0), self._bits)
            else:
                side, other = component[1:]
                angle = -omega[side]*(Q(time)-births[side])+omega[other]*(Q(time)-births[other])
                scalar, error = gaussian._exponential(Q(0), angle, self._bits)
            image, component_error = trajectory.RetardedGaussianTrajectorySource.component_action_and_price(
                self._source, component, state, slice_start=time)
            field._add(answer, image, dipole.ComplexRadical(*scalar))
            blocks = trajectory.RetardedGaussianTrajectorySource._blocks(self._source, image)
            price += error*trajectory._norm(blocks, self._bits)+(abs(scalar[0])+abs(scalar[1])+error)*component_error
        return answer, field._price_upper(price, self._bits)


def _whole_tail_receipt(auxiliary, side, local, initial_norm):
    RetardedAuxiliaryTailGKSL.record(auxiliary)
    _require(type(side) is int and side in (0, 1), 'original local source side required')
    pulse = auxiliary._source._law._field._pulses[side]
    leg = gaussian.GaussianAtomicPulseSource.record(pulse)
    _require(auxiliary._policy == 'source_tail' and Q(local) >= tail._tail_cut(leg, auxiliary._bits),
             'a whole-tail comparison requires the original legal source tail cut')
    receipt = gaussian.GaussianAtomicPulseSource.field_off_tail_price(pulse, local, bits=auxiliary._bits)
    norm = full.nonnegative(initial_norm)
    price = norm*Q(receipt['density_CP_Duhamel_price_per_input_norm_upper'])
    return price, {'source_side': side, 'source_first_discarded_local_seconds': str(local),
        'original_physical_tail_receipt': receipt, 'whole_initial_Hermitian_norm_upper': str(norm),
        'physical_drive_norm_and_exact_phase_covered': True,
        'norm_is_of_true_auxiliary_flow_not_candidate_coefficients': True,
        'comparison_scope': 'whole same-jump quantum x first-receipt-time instrument before time projection',
        'retained_time_field_queue_ancillas_use_Hdrive_tensor_identity': True,
        'whole_future_tail_paid_once_for_this_leg': True,
        'whole_physical_Duhamel_difference_price': str(field._price_upper(price, auxiliary._bits)),
        'candidate_positive_assumed': False, 'physical_source_drive_turned_off': False}


def _piece_aux(source, columns, piece, current, start, mode_bits, exp_bits, envelope_order, cluster_order, auxiliary):
    width, groups = checked._modes(piece, mode_bits, source)
    states = [matrix for polynomial in groups.values() for matrix in polynomial.values()]
    active, descriptors, discarded = tail.descriptors(source, columns, start, start+width, states,
        envelope_order, tail_policy=auxiliary._policy)
    _require(tuple(sorted(component[1] for component in discarded)) == auxiliary.discarded_sides(start),
             'the residual and auxiliary flow must use the same source tail regime')
    grid_bits = max(mode_bits+1, columns.bits); denominator = 1; factors = set()
    for exponent, polynomial in groups.items():
        factors.add((width*exponent[0], width*exponent[1]))
        for n in polynomial:
            factors.add((Q(n), Q(0)))
    for _, _, scalars, _, _ in descriptors:
        for a, b in scalars:
            factors.add((-width*a, -width*b))
    for factor in factors:
        for value in factor:
            denominator = lcm(denominator, value.denominator)
    weights = {factor: tuple(value.numerator*(denominator//value.denominator) for value in factor) for factor in factors}
    complete_denominator = denominator*(1 << grid_bits); residual = {}; rounding = scalar_tails = phases = Q(0)
    for exponent, polynomial in groups.items():
        lr, li = exponent
        for n, matrix in polynomial.items():
            coefficient = fixed._coefficient_grid(matrix, grid_bits)
            fixed._add(residual.setdefault(exponent, {}).setdefault(n, {}), coefficient, weights[width*lr, width*li])
            if n:
                fixed._add(residual.setdefault(exponent, {}).setdefault(n-1, {}), coefficient, weights[Q(n), Q(0)])
            for component, frequency, scalars, radius, _ in descriptors:
                if component in discarded:
                    continue
                image, error, _ = integer.IntegerColumns.action(columns, component, matrix, active)
                image_int = fixed._coefficient_grid(image, grid_bits)
                target = lr, li+frequency
                for j, (a, b) in enumerate(scalars):
                    fixed._add(residual.setdefault(target, {}).setdefault(n+j, {}), image_int, weights[-width*a, -width*b])
                    rounding += 2*width*(abs(a)+abs(b))*error/Q(n+j+1)
                scalar_tails += 2*width*radius*(fixed._norm(image_int, 1 << grid_bits)+error)/Q(n+1)
                phases += 2*width*integer.IntegerColumns.phase_error(columns, component, matrix, active)/Q(n+1)
    defect, clusters = clustered._clustered_defect(residual, complete_denominator, width, cluster_order)
    separate = 2*sum((fixed._norm(matrix, complete_denominator)/Q(n+1)
        for polynomial in residual.values() for n, matrix in polynomial.items()), Q(0))
    begin, e0 = checked._evaluate(groups, width, Q(0), exp_bits)
    end, e1 = checked._evaluate(groups, width, Q(1), exp_bits)
    join = checked._difference(begin, current)+e0; uniform = join+defect+rounding+scalar_tails+phases
    detail = {'source_detector_interval_seconds': list(map(str, (start, start+width))),
        'source_exact_frequency_words_after_merge': len(residual), 'source_frequency_clusters': len(clusters),
        'frequency_cluster_prices': clusters, 'separate_frequency_integrated_residual': str(field._price_upper(separate, columns.bits)),
        'complete_marked_coordinate_inventory': len(set().union(*(set(matrix) for matrix in states))) if states else 0,
        'Hermitian_projection_of_entire_complex_curve': True,
        'integrated_original_source_residual': str(field._price_upper(defect, columns.bits)),
        'source_radical_column_rounding_price': str(field._price_upper(rounding, columns.bits)),
        'source_Gaussian_and_relative_phase_tail_price': str(field._price_upper(scalar_tails, columns.bits)),
        'source_drive_phase_price': str(field._price_upper(phases, columns.bits)),
        'complete_join_price': str(field._price_upper(join, columns.bits)),
        'auxiliary_piece_uniform_rotating_error_from_input': str(field._price_upper(uniform, columns.bits)),
        'endpoint_exponential_scalar_price': str(field._price_upper(e1, columns.bits)),
        'source_selected_mathematical_drive_omissions': list(auxiliary.discarded_sides(start)),
        'original_tail_regime_receipts': [value for _, value in sorted(discarded.items())],
        'zero_component_from_original_columns': [list(c) if type(c) is tuple else c
            for c, _, _, _, zero in descriptors if zero], 'Hamiltonian_norm_exponential_used': False,
        'candidate_positive_assumed': False}
    return width, end, uniform, e1, detail, discarded


def certify(source, trial, *, upstream_error=0, coefficient_bits=192, exponential_bits=192,
            envelope_order=10, cluster_order=12, tail_policy='source_tail', tail_pricing='auxiliary_cptp'):
    _CHECK(); _pricing(tail_pricing); tail.policy(tail_policy); clustered._cluster_order(cluster_order)
    _require(type(source) is checked.RetardedReceiptTrajectoryCertificate,
             'closed original continuous source required; no auxiliary target or caller checker')
    raw = checked.RetardedReceiptTrajectoryCertificate.record(source)
    _require(type(trial) is dict and set(trial) == {'schema', 'source_record', 'complete_initial_marked_state',
        'source_issued_input_used', 'source_detector_interval_seconds', 'mode_bits', 'pieces', 'writer_correctness_assumed'} and
        trial['schema'] == checked.SCHEMA+'/untrusted-curve' and trial['source_record'] == raw and
        trial['writer_correctness_assumed'] is False, 'the complete original untrusted source curve is required')
    mode_bits = trial['mode_bits']
    for bits in (mode_bits, coefficient_bits, exponential_bits):
        gaussian._precision(bits)
    if source._inlet is None:
        initial, inherited, issued = checked.RetardedReceiptTrajectoryCertificate._input(source,
            trial['complete_initial_marked_state'], upstream_error)
    else:
        initial, inherited, issued = checked.RetardedReceiptTrajectoryCertificate._input(source, None, upstream_error)
        _require(checked._record_state(initial) == trial['complete_initial_marked_state'], 'original source-issued input changed')
    _require(trial['source_issued_input_used'] is issued and type(trial['pieces']) is list, 'original input issuance required')
    start, stop = map(full.nonnegative, trial['source_detector_interval_seconds'])
    trajectory.RetardedGaussianTrajectorySource._clock(source._source, start)
    trajectory.RetardedGaussianTrajectorySource._clock(source._source, stop)
    _require(start <= stop and (not issued or start == Q(raw['stopped_trajectory_source']['retarded_source']['gate_seconds'][0])),
             'original source interval and input cut required')
    _, current, entry, initial_norm = checked._initial(source._source, initial, start, coefficient_bits)
    if issued:
        initial_norm = min(initial_norm, Q(raw['source_issued_inlet']['source_centre_trace_norm_upper']))
        lift_initial_norm = Q(raw['source_issued_inlet']['source_centre_trace_norm_upper'])
        lift_norm_scope = 'source positive complete mother mass upper plus its original input error; no arbitrary marginal-norm lift'
    else:
        lift_initial_norm = initial_norm
        lift_norm_scope = 'declared Hermitian input and original subsequent vacuum/instrument ancillas; actual membership not asserted'
    columns = integer.IntegerColumns(source._source, coefficient_bits)
    auxiliary = RetardedAuxiliaryTailGKSL(source, coefficient_bits=coefficient_bits, tail_policy=tail_policy,
        source_interval_seconds=(start, stop), source_piece_durations=tuple(piece['duration_seconds'] for piece in trial['pieces']))
    time = start; accumulated = entry; physical_tail = Q(0); paid_sides = set(); payments = []; records = []
    for piece in trial['pieces']:
        before = accumulated
        if tail_pricing == 'original_coefficients':
            width, current, uniform, endpoint, detail = original._piece(source._source, columns,
                piece, current, time, mode_bits, exponential_bits, envelope_order, cluster_order, tail_policy)
            new_difference = Q(0)
        else:
            width, current, uniform, endpoint, detail, discarded = _piece_aux(source._source, columns,
                piece, current, time, mode_bits, exponential_bits, envelope_order, cluster_order, auxiliary)
            new_difference = Q(0)
            for component, regime in sorted(discarded.items()):
                side = component[1]
                if side not in paid_sides:
                    price, receipt = _whole_tail_receipt(auxiliary, side, regime['source_local_cut_seconds'], lift_initial_norm)
                    new_difference += price; payments.append(receipt); paid_sides.add(side)
            physical_tail += new_difference
        detail.update(previous_rotating_endpoint_error=str(field._price_upper(before, coefficient_bits)),
            new_whole_physical_tail_difference_price=str(field._price_upper(new_difference, coefficient_bits)),
            cumulative_whole_physical_tail_difference_price=str(field._price_upper(physical_tail, coefficient_bits)),
            piece_uniform_rotating_error_from_input=str(field._price_upper(uniform+new_difference, coefficient_bits)))
        accumulated += uniform+endpoint+new_difference; time += width; records.append(detail)
    _require(time == stop, 'all original source time must be covered')
    physical, frame_error = trajectory.RetardedGaussianTrajectorySource.frame(source._source, stop, checked._exact(current))
    gamma_price, gamma_record = checked._gamma_price(source._source, initial_norm, start, stop, coefficient_bits)
    return {'schema': SCHEMA+'/checked-complete-curve', 'source_record': raw, 'untrusted_trial': checked._copy(trial),
        'integer_action_source': integer.RetardedComponentIntegerAction.record(columns.owner), 'source_bindings': _bindings(),
        'source_auxiliary_GKSL_contract': auxiliary.record(),
        'complete_physical_marked_endpoint': checked._record_state(physical),
        'whole_upstream_trace_norm_error_once': str(inherited),
        'source_initial_trace_norm_upper': str(field._price_upper(initial_norm, coefficient_bits)),
        'source_time_retaining_lift_initial_norm_upper': str(field._price_upper(lift_initial_norm, coefficient_bits)),
        'source_time_retaining_lift_initial_norm_scope': lift_norm_scope,
        'source_rotating_curve_error': str(field._price_upper(accumulated, coefficient_bits)),
        'physical_frame_readout_error': str(field._price_upper(frame_error, coefficient_bits)),
        'mathematical_Gamma_full_marked_price': str(field._price_upper(gamma_price, coefficient_bits)),
        'Gamma_price_components': gamma_record,
        'global_trace_norm_error': str(field._price_upper(inherited+accumulated+frame_error+gamma_price, coefficient_bits)),
        'whole_physical_Gaussian_Duhamel_difference_price': str(field._price_upper(physical_tail, coefficient_bits)),
        'whole_physical_Gaussian_difference_is_time_retaining_instrument_price': True,
        'auxiliary_source_rotating_curve_error': str(field._price_upper(accumulated-physical_tail, coefficient_bits)),
        'source_whole_tail_difference_receipts': payments,
        'source_detector_interval_seconds': list(map(str, (start, stop))), 'piece_records': records,
        'source_issued_input_used': issued, 'actual_hardware_member_asserted': False,
        'endpoint_price_substituted_for_uniform_error': False, 'Hermitian_CPTP_contraction_used': True,
        'coefficient_bits': coefficient_bits, 'exponential_bits': exponential_bits,
        'envelope_order': envelope_order, 'cluster_order': cluster_order,
        'residual_policy': tail.policy(tail_policy), 'tail_pricing': tail_pricing,
        'candidate_positive_assumed': False, 'physical_source_drive_turned_off': False, 'controller_advance': False}


def verify(source, report):
    _CHECK()
    _require(type(report) is dict and report.get('schema') == SCHEMA+'/checked-complete-curve',
             'named whole Gaussian tail Duhamel certificate required')
    rebuilt = certify(source, report['untrusted_trial'], upstream_error=(
        report['whole_upstream_trace_norm_error_once'] if source._inlet is None else 0),
        coefficient_bits=report['coefficient_bits'], exponential_bits=report['exponential_bits'],
        envelope_order=report['envelope_order'], cluster_order=report['cluster_order'],
        tail_policy=report['residual_policy']['name'], tail_pricing=report['tail_pricing'])
    _require(rebuilt == report, 'complete auxiliary source, whole tail comparison, uniform price or endpoint changed')
    return rebuilt


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    helpers = (_require, _bindings, _pricing, _source_cp_contract, _source_schedule, _whole_tail_receipt, _piece_aux,
        certify, verify, _function, _signature, _check, lcm,
        RetardedAuxiliaryTailGKSL.__init__, RetardedAuxiliaryTailGKSL.record,
        RetardedAuxiliaryTailGKSL.discarded_sides, RetardedAuxiliaryTailGKSL.action_and_price,
        joint.passive_transfer, trajectory._inventory, trajectory.RetardedGaussianTrajectorySource.record,
        trajectory.RetardedGaussianTrajectorySource._clock, trajectory.RetardedGaussianTrajectorySource.component_action_and_price,
        tail.descriptors, tail._tail_cut, tail.policy, original._piece,
        gaussian.GaussianAtomicPulseSource.field_off_tail_price, gaussian.GaussianAtomicPulseSource.record,
        integer.IntegerColumns.action, clustered._clustered_defect, checked._modes, checked._evaluate,
        checked._initial, checked._gamma_price, checked._record_state, checked._exact)
    return tuple(map(_function, helpers)), SCHEMA, PRICINGS


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             original._CHECK is _ORIGINAL_CHECK, 'whole Gaussian tail Duhamel source checker execution changed')
    _ORIGINAL_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
