"""Validation cells price the same auxiliary residual with whole physical tails.

The source-owned time-retaining auxiliary GKSL and physical Duhamel price
remain unchanged.  Only the complete auxiliary residual integral is
reparameterised by the already checked exact validation-cell algorithm.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import lcm
import hashlib

import retarded_gaussian_tail_duhamel_certificate as duhamel
import retarded_residual_cell_certificate as validation

original, tail, clustered, fixed = duhamel.original, duhamel.tail, duhamel.clustered, duhamel.fixed
checked, integer, trajectory, gaussian, field, full = (duhamel.checked, duhamel.integer,
    duhamel.trajectory, duhamel.gaussian, duhamel.field, duhamel.full)
RetardedAuxiliaryTailGKSL = duhamel.RetardedAuxiliaryTailGKSL
_whole_tail_receipt, _pricing = duhamel._whole_tail_receipt, duhamel._pricing
_REQUIRE_CHECK, _VALIDATION_CHECK = duhamel._CHECK, validation._CHECK
SCHEMA = 'stage10-original-retarded-whole-tail-Duhamel-residual-cell-certificate/v1'


def _require(value, message):
    if not value:
        raise ValueError(message)


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), *(Path(m.__file__) for m in (duhamel, validation, original, tail, clustered, fixed,
         integer, checked, trajectory, gaussian)))}


def _piece_aux(source, columns, piece, current, start, mode_bits, exp_bits, envelope_order, cluster_order, auxiliary, cells):
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
    defect, original_defect, cell_sum, clusters, cell_records = validation._validated_defect(
        residual, complete_denominator, width, cluster_order, cells, exp_bits)
    separate = 2*sum((fixed._norm(matrix, complete_denominator)/Q(n+1)
        for polynomial in residual.values() for n, matrix in polynomial.items()), Q(0))
    begin, e0 = checked._evaluate(groups, width, Q(0), exp_bits)
    end, e1 = checked._evaluate(groups, width, Q(1), exp_bits)
    join = checked._difference(begin, current)+e0; uniform = join+defect+rounding+scalar_tails+phases
    detail = {'source_detector_interval_seconds': list(map(str, (start, start+width))),
        'source_exact_frequency_words_after_merge': len(residual), 'source_frequency_clusters': len(clusters),
        'frequency_cluster_prices': clusters,
        'original_frequency_clustered_integrated_residual': str(field._price_upper(original_defect, columns.bits)),
        'validation_cells_integrated_residual': str(field._price_upper(cell_sum, columns.bits)),
        'residual_validation_cells': cell_records,
        'residual_price_choice': 'validation cells' if cell_sum < original_defect else 'original bound', 'separate_frequency_integrated_residual': str(field._price_upper(separate, columns.bits)),
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
            envelope_order=10, cluster_order=12, tail_policy='source_tail', tail_pricing='auxiliary_cptp', cells=4):
    _CHECK(); cells = validation._cells(cells); _pricing(tail_pricing); tail.policy(tail_policy); clustered._cluster_order(cluster_order)
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
                piece, current, time, mode_bits, exponential_bits, envelope_order, cluster_order, auxiliary, cells)
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
        'candidate_positive_assumed': False, 'physical_source_drive_turned_off': False, 'controller_advance': False,
        'residual_validation_cells': validation._cell_record(cells), 'validation_cells_change_source_steps': False}


def verify(source, report):
    _CHECK()
    _require(type(report) is dict and report.get('schema') == SCHEMA+'/checked-complete-curve',
             'named same-residual cells and whole Gaussian tail Duhamel certificate required')
    rebuilt = certify(source, report['untrusted_trial'], upstream_error=(
        report['whole_upstream_trace_norm_error_once'] if source._inlet is None else 0),
        coefficient_bits=report['coefficient_bits'], exponential_bits=report['exponential_bits'],
        envelope_order=report['envelope_order'], cluster_order=report['cluster_order'],
        tail_policy=report['residual_policy']['name'], tail_pricing=report['tail_pricing'],
        cells=validation._read_cells(report['residual_validation_cells']))
    _require(rebuilt == report, 'complete auxiliary source, whole tail comparison, uniform price or endpoint changed')
    return rebuilt


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    helpers = (_require, _bindings, _piece_aux, certify, verify, _function, _signature, _check, lcm,
        validation._validated_defect, validation._cells, validation._cell_record, validation._read_cells,
        RetardedAuxiliaryTailGKSL.__init__, RetardedAuxiliaryTailGKSL.record,
        RetardedAuxiliaryTailGKSL.discarded_sides, _whole_tail_receipt, _pricing, original._piece,
        tail.descriptors, fixed._coefficient_grid, fixed._add, fixed._norm, checked._modes,
        checked._evaluate, checked._initial, checked._gamma_price, checked._record_state, checked._exact,
        integer.IntegerColumns.action, integer.IntegerColumns.phase_error)
    return tuple(map(_function, helpers)), SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             duhamel._CHECK is _REQUIRE_CHECK and validation._CHECK is _VALIDATION_CHECK,
             'whole auxiliary tail residual-cell checker execution changed')
    _REQUIRE_CHECK(); _VALIDATION_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
