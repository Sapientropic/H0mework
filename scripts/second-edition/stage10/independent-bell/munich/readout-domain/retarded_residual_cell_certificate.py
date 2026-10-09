"""Validation cells price the same complete source residual function.

Exact binomial translation retains every original matrix coefficient. Only
the residual integral is subdivided: the physical curve, joins, source and
Mark actions remain the original ones. Scalar shift enclosures are paid
against each complete polynomial and its remaining exponential growth.
"""
from fractions import Fraction as Q
from math import comb, lcm
from pathlib import Path
import hashlib

import retarded_frequency_clustered_certificate as clustered

fixed, checked, integer, trajectory = clustered.fixed, clustered.checked, clustered.integer, clustered.trajectory
field, gaussian, full = clustered.field, clustered.gaussian, clustered.full
SCHEMA = 'stage10-source-retarded-residual-validation-cell-certificate/v1'
_CLUSTERED_CHECK = clustered._CHECK


def _require(value, message):
    if not value:
        raise ValueError(message)


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), *(Path(m.__file__) for m in (clustered, fixed, integer, checked, trajectory, gaussian)))}


def _cells(value):
    if type(value) is int:
        _require(1 <= value <= 64, 'positive finite validation-cell budget required')
        value = tuple((Q(n, value), Q(n+1, value)) for n in range(value))
    _require(type(value) in (tuple, list) and value, 'nonempty exact validation-cell partition required')
    result = []
    previous = Q(0)
    for cell in value:
        _require(type(cell) in (tuple, list) and len(cell) == 2 and all(type(x) is Q for x in cell),
                 'validation-cell endpoints must be exact Fractions, not floats')
        left, right = cell
        _require(left == previous and Q(0) <= left < right <= Q(1),
                 'validation cells must exactly cover [0,1] without gaps or overlaps')
        result.append((left, right))
        previous = right
    _require(previous == Q(1), 'validation cells must exactly cover [0,1] without gaps or overlaps')
    return tuple(result)


def _cell_record(cells):
    return [list(map(str, cell)) for cell in cells]


def _read_cells(record):
    _require(type(record) is list and record, 'complete canonical validation-cell record required')
    cells = []
    for row in record:
        _require(type(row) is list and len(row) == 2 and all(type(x) is str for x in row),
                 'canonical exact validation-cell strings required')
        cell = tuple(Q(x) for x in row)
        _require(list(map(str, cell)) == row, 'canonical exact validation-cell strings required')
        cells.append(cell)
    return _cells(cells)


def _translated(polynomial, denominator, left, span):
    weights = {(n, k): Q(comb(n, k))*left**(n-k)*span**k
               for n in polynomial for k in range(n+1)}
    scalar_denominator = 1
    for weight in weights.values():
        scalar_denominator = lcm(scalar_denominator, weight.denominator)
    result = {}
    for n, matrix in polynomial.items():
        for k in range(n+1):
            weight = weights[n, k]
            integer_weight = weight.numerator*(scalar_denominator//weight.denominator)
            fixed._add(result.setdefault(k, {}), matrix, (integer_weight, 0))
    return result, denominator*scalar_denominator


def _cell_bound(residual, denominator, width, cell, cluster_order, shift_bits):
    left, right = cell
    span = right-left
    proposals = []
    scalar_prices = []
    shift_error = Q(0)
    common_denominator = 1
    for exponent, polynomial in sorted(residual.items()):
        polynomial = {n: matrix for n, matrix in polynomial.items() if matrix}
        if not polynomial:
            continue
        translated, translated_denominator = _translated(polynomial, denominator, left, span)
        lr, li = exponent
        centre, error = gaussian._exponential(width*lr*left, width*li*left, shift_bits)
        # The remaining cell exponential has growth <= 2; nonpositive real
        # exponents have growth <= 1. The scalar enclosure prices the shift.
        growth = Q(1) if lr <= 0 else Q(2)
        polynomial_integral = sum((fixed._norm(matrix, translated_denominator)/Q(k+1)
                                   for k, matrix in translated.items()), Q(0))
        shift_error += growth*error*polynomial_integral
        phase_denominator = lcm(*(x.denominator for x in centre))
        factor = tuple(x.numerator*(phase_denominator//x.denominator) for x in centre)
        phased = {}
        for k, matrix in translated.items():
            fixed._add(phased.setdefault(k, {}), matrix, factor)
        phased_denominator = translated_denominator*phase_denominator
        common_denominator = lcm(common_denominator, phased_denominator)
        proposals.append((exponent, phased, phased_denominator))
        scalar_prices.append({'original_exponent_per_second': list(map(str, exponent)),
            'dimensionless_shift_exponent': list(map(str, (width*lr*left, width*li*left))),
            'shift_exponential_centre': list(map(str, centre)),
            'shift_exponential_error': str(error), 'remaining_cell_growth_upper': str(growth),
            'translated_polynomial_norm_integral_in_v': str(polynomial_integral)})
    shifted = {}
    for exponent, polynomial, divisor in proposals:
        factor = common_denominator//divisor
        target = shifted.setdefault(exponent, {})
        for n, matrix in polynomial.items():
            fixed._add(target.setdefault(n, {}), matrix, (factor, 0))
    clustered_price, clusters = clustered._clustered_defect(
        shifted, common_denominator, width*span, cluster_order)
    result = span*(clustered_price+shift_error)
    return result, {'normalized_validation_cell': list(map(str, cell)),
        'normalized_cell_span': str(span), 'residual_evaluation_width_seconds': str(width*span),
        'original_per_second_exponents_retained': True, 'binomial_rearrangement_exact': True,
        'clustered_residual_integral_in_v': str(clustered_price),
        'shift_scalar_integral_price_in_original_u': str(span*shift_error),
        'residual_cell_integral_in_original_u': str(result),
        'shift_scalar_enclosures': scalar_prices, 'frequency_cluster_prices': clusters,
        'validation_cell_is_physical_step': False, 'validation_cell_join_price_added': False}


def _validated_defect(residual, denominator, width, cluster_order, cells, shift_bits):
    cells = _cells(cells)
    gaussian._precision(shift_bits)
    # This checks the complete original integer residual before any auxiliary
    # translation. The original bound remains an independently sound fallback.
    original, original_clusters = clustered._clustered_defect(residual, denominator, width, cluster_order)
    total = Q(0)
    records = []
    for cell in cells:
        price, record = _cell_bound(residual, denominator, width, cell, cluster_order, shift_bits)
        total += price
        records.append(record)
    return min(original, total), original, total, original_clusters, records

def _piece(source, columns, piece, current, start, mode_bits, exp_bits, envelope_order, cluster_order, cells):
    width, groups = checked._modes(piece, mode_bits, source)
    states = [matrix for polynomial in groups.values() for matrix in polynomial.values()]
    active, descriptors = checked._descriptors(source, columns, start, start+width, states, envelope_order)
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
    rounding = tails = phases = Q(0)
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
                target = lr, li+frequency
                for j, (a, b) in enumerate(scalars):
                    fixed._add(residual.setdefault(target, {}).setdefault(n+j, {}), image_int,
                               weights[-width*a, -width*b])
                    rounding += 2*width*(abs(a)+abs(b))*error/Q(n+j+1)
                tails += 2*width*tail*(fixed._norm(image_int, 1 << grid_bits)+error)/Q(n+1)
                phases += 2*width*integer.IntegerColumns.phase_error(columns, component, matrix, active)/Q(n+1)
    separate = 2*sum((fixed._norm(matrix, denominator)/Q(n+1)
        for polynomial in residual.values() for n, matrix in polynomial.items()), Q(0))
    defect, original, cell_sum, clusters, cell_records = _validated_defect(
        residual, denominator, width, cluster_order, cells, exp_bits)
    begin, e0 = checked._evaluate(groups, width, Q(0), exp_bits)
    end, e1 = checked._evaluate(groups, width, Q(1), exp_bits)
    join = checked._difference(begin, current)+e0
    uniform = join+defect+rounding+tails+phases
    record = {'source_detector_interval_seconds': list(map(str, (start, start+width))),
        'source_exact_frequency_words_after_merge': len(residual), 'source_frequency_clusters': len(clusters),
        'frequency_cluster_prices': clusters,
        'original_frequency_clustered_integrated_residual': str(field._price_upper(original, columns.bits)),
        'validation_cells_integrated_residual': str(field._price_upper(cell_sum, columns.bits)),
        'residual_validation_cells': cell_records,
        'residual_price_choice': 'validation cells' if cell_sum < original else 'original bound',
        'separate_frequency_integrated_residual': str(field._price_upper(separate, columns.bits)),
        'complete_marked_coordinate_inventory': len(set().union(*(set(m) for m in states))) if states else 0,
        'Hermitian_projection_of_entire_complex_curve': True,
        'integrated_original_source_residual': str(field._price_upper(defect, columns.bits)),
        'source_radical_column_rounding_price': str(field._price_upper(rounding, columns.bits)),
        'source_Gaussian_and_relative_phase_tail_price': str(field._price_upper(tails, columns.bits)),
        'source_drive_phase_price': str(field._price_upper(phases, columns.bits)),
        'complete_join_price': str(field._price_upper(join, columns.bits)),
        'piece_uniform_rotating_error_from_input': str(field._price_upper(uniform, columns.bits)),
        'endpoint_exponential_scalar_price': str(field._price_upper(e1, columns.bits)),
        'zero_component_from_original_columns': [list(c) if type(c) is tuple else c
            for c, _, _, _, zero in descriptors if zero], 'Hamiltonian_norm_exponential_used': False}
    return width, end, uniform, e1, record


def certify(source, trial, *, upstream_error=0, coefficient_bits=192,
            exponential_bits=192, envelope_order=10, cluster_order=12, cells=4):
    _CHECK()
    clustered._cluster_order(cluster_order)
    cells = _cells(cells)
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
            piece, current, time, mode_bits, exponential_bits, envelope_order, cluster_order, cells)
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
        'residual_validation_cells': _cell_record(cells),
        'validation_cells_change_source_steps': False}


def verify(source, report):
    _CHECK()
    _require(type(report) is dict and report.get('schema') == SCHEMA+'/checked-complete-curve',
             'named residual-cell complete source certificate required')
    expected = certify(source, report['untrusted_trial'], upstream_error=(
        report['whole_upstream_trace_norm_error_once'] if source._inlet is None else 0),
        coefficient_bits=report['coefficient_bits'], exponential_bits=report['exponential_bits'],
        envelope_order=report['envelope_order'], cluster_order=report['cluster_order'], cells=_read_cells(report['residual_validation_cells']))
    _require(expected == report, 'full source residual, validation cells, scalar prices or endpoint changed')
    return expected



def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    helpers = (_require, _bindings, _cells, _cell_record, _read_cells, _translated,
        _cell_bound, _validated_defect, _piece, certify, verify, comb, lcm,
        _function, _signature, _check, clustered._cluster_order, clustered._clustered_defect,
        fixed._coefficient_grid, fixed._add, fixed._norm, gaussian._exponential, gaussian._precision,
        checked._modes, checked._descriptors, checked._evaluate, checked._difference,
        checked._initial, checked._gamma_price, checked._exact, checked._record_state,
        checked._copy, field._price_upper, checked.RetardedReceiptTrajectoryCertificate.record,
        checked.RetardedReceiptTrajectoryCertificate._input, integer.IntegerColumns.action,
        integer.IntegerColumns.phase_error, integer.RetardedComponentIntegerAction.record,
        trajectory.RetardedGaussianTrajectorySource.frame, trajectory.RetardedGaussianTrajectorySource._clock)
    return tuple(map(_function, helpers)), SCHEMA, full.DIMENSION


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             clustered._CHECK is _CLUSTERED_CHECK, 'residual-cell checker execution closure changed')
    _CLUSTERED_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
