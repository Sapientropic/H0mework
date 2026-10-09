"""The full original retarded drive is paid by its decreasing Gaussian tail.

Early slices retain the original jet.  Later source-owned local cuts use
zero drive candidates while complete original drive images and their actual
Gaussian envelope integral enter the residual price.  The remaining whole
Mark residual uses the original exact frequency-cluster checker.
"""
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import hashlib

import retarded_gaussian_tail_descriptors as tails

clustered = tails.clustered
fixed = clustered.fixed

checked, integer, trajectory = fixed.checked, fixed.integer, fixed.trajectory
field, gaussian, full = fixed.field, fixed.gaussian, fixed.full
SCHEMA = 'stage10-source-retarded-Gaussian-tail-residual-certificate/v1'
_CLUSTER_CHECK, _TAIL_CHECK = clustered._CHECK, tails._CHECK


def _require(value, message):
    if not value:
        raise ValueError(message)


def _bindings():
    paths = (Path(__file__), *(Path(m.__file__) for m in
             (clustered, tails, fixed, integer, checked, trajectory, gaussian)),
             Path(__file__).with_name('retarded_counterflow_numpy_writer.py'))
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def generate_trial(source, initial=None, stop=None, *, start=None, slices=1,
                   order=16, mode_bits=96, envelope_order=10, maximum_count_sum=2,
                   tail_policy='source_tail'):
    """Untrusted original-format curves, retaining exact receipt counterflow."""
    import numpy as np
    import retarded_counterflow_numpy_writer as counterflow
    _CHECK(); tails.policy(tail_policy)
    original = counterflow.original
    _require(type(source) is checked.RetardedReceiptTrajectoryCertificate,
             'closed original continuous source required; a target curve is not input')
    raw = checked.RetardedReceiptTrajectoryCertificate.record(source)
    _require(maximum_count_sum is None or (type(maximum_count_sum) is int and maximum_count_sum >= 0),
             'nonnegative candidate count budget or complete override required')
    _require(type(slices) is int and slices > 0 and type(order) is int and 0 <= order <= 63,
             'finite pending polynomial and receipt integral budget required')
    gaussian._precision(mode_bits)
    original_input, _, issued = checked.RetardedReceiptTrajectoryCertificate._input(source, initial, 0)
    g0, g1 = map(Q, raw['stopped_trajectory_source']['retarded_source']['gate_seconds'])
    start = g0 if start is None else full.nonnegative(start)
    stop = g1 if stop is None else full.nonnegative(stop)
    _require(g0 <= start <= stop <= g1 and (not issued or start == g0), 'original source input cut required')
    _, pairs, _, _ = checked._initial(source._source, original_input, start, mode_bits)
    paths = original._Paths(source._source, pairs, maximum_count_sum, mode_bits); current = paths.input(pairs)
    driven = raw['stopped_trajectory_source']['retarded_source']['complete_driven_field_source']
    births = tuple(Q(a)+Q(b) for a, b in zip(driven['flight_seconds'], driven['emission_origins_seconds']))
    cuts = tuple(birth+tails._tail_cut(leg, source._source._value['scalar_bits'])
                 for birth, leg in zip(births, driven['Gaussian_source_legs']))
    edges = sorted({start+n*(stop-start)/slices for n in range(slices+1)} |
                   {x for x in (*births, *cuts) if start < x < stop})
    scratch = np.zeros(paths.length, dtype=np.complex128); derivative = np.zeros_like(scratch); pieces = []
    for origin, end in zip(edges, edges[1:]):
        width = end-origin
        active, descriptors = tails.candidate_scalars(source._source, origin, end, order,
            envelope_order, tail_policy=tail_policy)
        pending, receipt = counterflow._split(paths, current); pending_modes = [pending]; forcing = []
        for degree in range(order+1):
            derivative.fill(0)
            for component, scalars in descriptors:
                scratch.fill(0)
                for j in range(degree+1):
                    paths.add(scratch, pending_modes[degree-j], scalars[j])
                paths.action(component, paths.state(scratch), active, derivative)
            matrix = derivative.reshape(len(paths.global_ids), paths.dimension, paths.dimension)
            matrix += matrix.conjugate().swapaxes(1, 2); matrix *= .5
            next_pending, arrival = counterflow._split(paths, paths.state(derivative)); forcing.append(arrival)
            if degree < order:
                pending_modes.append(counterflow._sum([counterflow._scaled(next_pending, float(width/Q(degree+1)))], mode_bits))
        groups = counterflow._receipt_modes(paths, receipt, forcing, width, active, mode_bits)
        groups.setdefault(Q(0), []); length = max(len(groups[Q(0)]), len(pending_modes))
        groups[Q(0)] = [counterflow._sum(([groups[Q(0)][n]] if n < len(groups[Q(0)]) else [])+
            ([pending_modes[n]] if n < len(pending_modes) else []), mode_bits) for n in range(length)]
        modes = [{'lambda_per_second': ['0', str(frequency)],
            'coefficients': [paths.rows(state, mode_bits) for state in coefficients]}
            for frequency, coefficients in sorted(groups.items())]
        pieces.append({'duration_seconds': str(width), 'modes': modes})
        current = counterflow._sum([counterflow._scaled(state,
            complex(*map(float, gaussian._exponential(Q(0), frequency*width, mode_bits)[0])))
            for frequency, coefficients in groups.items() for state in coefficients], mode_bits)
    return {'schema': checked.SCHEMA+'/untrusted-curve', 'source_record': raw,
        'complete_initial_marked_state': checked._record_state(original_input), 'source_issued_input_used': issued,
        'source_detector_interval_seconds': list(map(str, (start, stop))), 'mode_bits': mode_bits,
        'pieces': pieces, 'writer_correctness_assumed': False}


def _piece(source, columns, piece, current, start, mode_bits, exp_bits, envelope_order, cluster_order, tail_policy):
    width, groups = checked._modes(piece, mode_bits, source)
    states = [matrix for polynomial in groups.values() for matrix in polynomial.values()]
    active, descriptors, tail_inventory = tails.descriptors(source, columns, start, start+width, states,
        envelope_order, tail_policy=tail_policy)
    tail_payments = {component: Q(0) for component in tail_inventory}
    tail_coefficient_prices = {component: [] for component in tail_inventory}
    grid_bits = max(mode_bits+1, columns.bits)
    scalar_denominator = 1
    factors = set()
    for exponent, polynomial in groups.items():
        factors.add((width*exponent[0], width*exponent[1]))
        for n in polynomial:
            factors.add((Q(n), Q(0)))
    for _, _, coefficients, _, _ in descriptors:
        for a, b in coefficients:
            factors.add((-width*a, -width*b))
    for factor in factors:
        for value in factor:
            scalar_denominator = lcm(scalar_denominator, value.denominator)
    weights = {factor: tuple(value.numerator*(scalar_denominator//value.denominator)
                             for value in factor) for factor in factors}
    denominator = scalar_denominator*(1 << grid_bits)
    residual = {}
    rounding = scalar_tails = phases = Q(0)
    for exponent, polynomial in groups.items():
        lr, li = exponent
        for n, matrix in polynomial.items():
            coefficient = fixed._coefficient_grid(matrix, grid_bits)
            fixed._add(residual.setdefault(exponent, {}).setdefault(n, {}), coefficient,
                       weights[width*lr, width*li])
            if n:
                fixed._add(residual.setdefault(exponent, {}).setdefault(n-1, {}), coefficient, weights[Q(n), Q(0)])
            for component, frequency, scalars, tail, _ in descriptors:
                image, error, _ = integer.IntegerColumns.action(columns, component, matrix, active)
                image_int = fixed._coefficient_grid(image, grid_bits)
                if component in tail_inventory:
                    integral = Q(tail_inventory[component]['original_tail_integral_seconds_upper'])
                    image_norm = fixed._norm(image_int, 1 << grid_bits)
                    phase = integer.IntegerColumns.phase_error(columns, component, matrix, active)
                    price = tails.weighted_tail_price(integral, image_norm, error, phase, n)
                    tail_payments[component] += price
                    tail_coefficient_prices[component].append({'exact_mode_exponent_per_second': list(map(str, exponent)),
                        'polynomial_degree': n, 'complete_original_drive_image_norm_upper': str(image_norm),
                        'original_drive_column_error': str(error), 'original_drive_phase_error': str(phase),
                        'weighted_integral_source_drive_price': str(field._price_upper(price, columns.bits)),
                        'original_image_not_zero': bool(image), 'drive_registered_as_source_zero': False})
                    continue
                target = lr, li+frequency
                for j, (a, b) in enumerate(scalars):
                    fixed._add(residual.setdefault(target, {}).setdefault(n+j, {}), image_int,
                               weights[-width*a, -width*b])
                    rounding += 2*width*(abs(a)+abs(b))*error/Q(n+j+1)
                scalar_tails += 2*width*tail*(fixed._norm(image_int, 1 << grid_bits)+error)/Q(n+1)
                phases += 2*width*integer.IntegerColumns.phase_error(columns, component, matrix, active)/Q(n+1)
    separate = 2*sum((fixed._norm(matrix, denominator)/Q(n+1)
        for polynomial in residual.values() for n, matrix in polynomial.items()), Q(0))
    defect, clusters = clustered._clustered_defect(residual, denominator, width, cluster_order)
    begin, e0 = checked._evaluate(groups, width, Q(0), exp_bits)
    end, e1 = checked._evaluate(groups, width, Q(1), exp_bits)
    join = checked._difference(begin, current)+e0
    tail_payment = sum(tail_payments.values(), Q(0))
    uniform = join+defect+rounding+scalar_tails+phases+tail_payment
    record = {'source_detector_interval_seconds': list(map(str, (start, start+width))),
        'source_exact_frequency_words_after_merge': len(residual), 'source_frequency_clusters': len(clusters),
        'frequency_cluster_prices': clusters,
        'separate_frequency_integrated_residual': str(field._price_upper(separate, columns.bits)),
        'complete_marked_coordinate_inventory': len(set().union(*(set(m) for m in states))) if states else 0,
        'Hermitian_projection_of_entire_complex_curve': True,
        'integrated_original_source_residual': str(field._price_upper(defect, columns.bits)),
        'source_radical_column_rounding_price': str(field._price_upper(rounding, columns.bits)),
        'source_Gaussian_and_relative_phase_tail_price': str(field._price_upper(scalar_tails, columns.bits)),
        'source_drive_phase_price': str(field._price_upper(phases, columns.bits)),
        'original_decreasing_Gaussian_drive_integral_price': str(field._price_upper(tail_payment, columns.bits)),
        'original_decreasing_Gaussian_tail_inventory': [{**item,
            'complete_original_drive_coefficient_prices': tail_coefficient_prices[component],
            'complete_weighted_integral_drive_payment': str(field._price_upper(tail_payments[component], columns.bits))}
            for component, item in sorted(tail_inventory.items())],
        'residual_policy': tails.policy(tail_policy),
        'complete_join_price': str(field._price_upper(join, columns.bits)),
        'piece_uniform_rotating_error_from_input': str(field._price_upper(uniform, columns.bits)),
        'endpoint_exponential_scalar_price': str(field._price_upper(e1, columns.bits)),
        'zero_component_from_original_columns': [list(c) if type(c) is tuple else c
            for c, _, _, _, zero in descriptors if zero], 'Hamiltonian_norm_exponential_used': False}
    return width, end, uniform, e1, record


def certify(source, trial, *, upstream_error=0, coefficient_bits=192,
            exponential_bits=192, envelope_order=10, cluster_order=12, tail_policy='source_tail'):
    _CHECK()
    clustered._cluster_order(cluster_order)
    tails.policy(tail_policy)
    _require(type(source) is checked.RetardedReceiptTrajectoryCertificate,
             'closed original continuous source required; no target matrix or caller checker')
    raw = checked.RetardedReceiptTrajectoryCertificate.record(source)
    _require(type(trial) is dict and set(trial) == {'schema', 'source_record', 'complete_initial_marked_state',
        'source_issued_input_used', 'source_detector_interval_seconds', 'mode_bits', 'pieces',
        'writer_correctness_assumed'} and trial['schema'] == checked.SCHEMA+'/untrusted-curve' and
        trial['source_record'] == raw and trial['writer_correctness_assumed'] is False,
        'untrusted curve must retain its complete original source')
    mode_bits = trial['mode_bits']
    for bits in (mode_bits, coefficient_bits, exponential_bits):
        gaussian._precision(bits)
    if source._inlet is None:
        initial, inherited, issued = checked.RetardedReceiptTrajectoryCertificate._input(
            source, trial['complete_initial_marked_state'], upstream_error)
    else:
        initial, inherited, issued = checked.RetardedReceiptTrajectoryCertificate._input(source, None, upstream_error)
        _require(checked._record_state(initial) == trial['complete_initial_marked_state'], 'issued complete input changed')
    _require(trial['source_issued_input_used'] is issued and type(trial['pieces']) is list, 'input issuance is source-owned')
    start, stop = map(full.nonnegative, trial['source_detector_interval_seconds'])
    trajectory.RetardedGaussianTrajectorySource._clock(source._source, start)
    trajectory.RetardedGaussianTrajectorySource._clock(source._source, stop)
    _require(start <= stop and (not issued or start == Q(raw['stopped_trajectory_source']['retarded_source']['gate_seconds'][0])),
             'original source interval and source-issued input cut required')
    _, current, entry, initial_norm = checked._initial(source._source, initial, start, coefficient_bits)
    if issued:
        initial_norm = min(initial_norm, Q(raw['source_issued_inlet']['source_centre_trace_norm_upper']))
    columns = integer.IntegerColumns(source._source, coefficient_bits)
    time = start
    accumulated = entry
    records = []
    for piece in trial['pieces']:
        before = accumulated
        width, current, uniform, endpoint, detail = _piece(source._source, columns,
            piece, current, time, mode_bits, exponential_bits, envelope_order, cluster_order, tail_policy)
        time += width
        accumulated += uniform+endpoint
        detail['previous_rotating_endpoint_error'] = str(field._price_upper(before, coefficient_bits))
        records.append(detail)
    _require(time == stop, 'all original source time must be covered')
    physical, frame = trajectory.RetardedGaussianTrajectorySource.frame(source._source, stop, checked._exact(current))
    model, model_record = checked._gamma_price(source._source, initial_norm, start, stop, coefficient_bits)
    return {'schema': SCHEMA+'/checked-complete-curve', 'source_record': raw, 'untrusted_trial': checked._copy(trial),
        'integer_action_source': integer.RetardedComponentIntegerAction.record(columns.owner), 'source_bindings': _bindings(),
        'complete_physical_marked_endpoint': checked._record_state(physical),
        'whole_upstream_trace_norm_error_once': str(inherited),
        'source_initial_trace_norm_upper': str(field._price_upper(initial_norm, coefficient_bits)),
        'source_rotating_curve_error': str(field._price_upper(accumulated, coefficient_bits)),
        'physical_frame_readout_error': str(field._price_upper(frame, coefficient_bits)),
        'mathematical_Gamma_full_marked_price': str(field._price_upper(model, coefficient_bits)),
        'Gamma_price_components': model_record,
        'global_trace_norm_error': str(field._price_upper(inherited+accumulated+frame+model, coefficient_bits)),
        'source_detector_interval_seconds': list(map(str, (start, stop))), 'piece_records': records,
        'source_issued_input_used': issued, 'actual_hardware_member_asserted': False,
        'endpoint_price_substituted_for_uniform_error': False, 'Hermitian_CPTP_contraction_used': True,
        'coefficient_bits': coefficient_bits, 'exponential_bits': exponential_bits,
        'envelope_order': envelope_order, 'cluster_order': cluster_order,
        'residual_policy': tails.policy(tail_policy), 'physical_source_drive_turned_off': False}


def verify(source, report):
    _CHECK()
    _require(type(report) is dict and report.get('schema') == SCHEMA+'/checked-complete-curve',
             'named Gaussian-tail complete source certificate required')
    expected = certify(source, report['untrusted_trial'], upstream_error=(
        report['whole_upstream_trace_norm_error_once'] if source._inlet is None else 0),
        coefficient_bits=report['coefficient_bits'], exponential_bits=report['exponential_bits'],
        envelope_order=report['envelope_order'], cluster_order=report['cluster_order'],
        tail_policy=report['residual_policy']['name'])
    _require(expected == report, 'original Gaussian tail policy, complete source residual, price or endpoint changed')
    return expected


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    helpers = (_require, _bindings, generate_trial, _piece, certify, verify, _function, _signature, _check, lcm,
        tails.descriptors, tails.policy, tails.weighted_tail_price, clustered._clustered_defect,
        fixed._coefficient_grid, fixed._add, fixed._norm, checked._modes, checked._evaluate,
        checked._difference, checked._initial, checked._gamma_price, checked._exact, checked._record_state,
        checked._copy, field._price_upper, checked.RetardedReceiptTrajectoryCertificate.record,
        checked.RetardedReceiptTrajectoryCertificate._input, integer.IntegerColumns.action,
        integer.IntegerColumns.phase_error, integer.RetardedComponentIntegerAction.record,
        trajectory.RetardedGaussianTrajectorySource.frame, trajectory.RetardedGaussianTrajectorySource._clock)
    return tuple(map(_function, helpers)), SCHEMA, full.DIMENSION


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             clustered._CHECK is _CLUSTER_CHECK and tails._CHECK is _TAIL_CHECK,
             'original Gaussian tail residual checker execution closure changed')
    _CLUSTER_CHECK(); _TAIL_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
