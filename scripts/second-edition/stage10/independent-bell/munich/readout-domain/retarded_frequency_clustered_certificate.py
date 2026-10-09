"""Complete source residual prices on exact common frequency carriers.

Nearby exponents remain distinct.  Factoring an actual cluster anchor and
expanding only the exact complex difference produces one common polynomial;
its integrated norm and a strict complex exponential remainder price bound
the same full residual function.  Original columns, joins, scalar tails,
model prices and complete marked input remain on the fixed integer path.
"""
from fractions import Fraction as Q
from math import factorial, lcm
from pathlib import Path
import hashlib

import retarded_integer_residual_certificate as fixed

checked, integer, trajectory = fixed.checked, fixed.integer, fixed.trajectory
field, gaussian, full = fixed.field, fixed.gaussian, fixed.full
SCHEMA = 'stage10-source-retarded-frequency-clustered-residual-certificate/v1'
_FIXED_CHECK = fixed._CHECK


def _require(value, message):
    if not value:
        raise ValueError(message)


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), *(Path(m.__file__) for m in (fixed, integer, checked, trajectory)))}


def _cluster_order(order):
    _require(type(order) is int and 0 <= order <= 32, 'finite exact complex frequency expansion order required')


def _partition(residual, width):
    _require(type(width) is Q and width > 0 and type(residual) is dict,
             'positive exact source width and complete residual inventory required')
    clusters = []
    for exponent, polynomial in sorted(residual.items()):
        _require(type(exponent) is tuple and len(exponent) == 2 and all(type(x) is Q for x in exponent) and
                 width*exponent[0] <= Q(1, 2), 'exact residual exponent must retain the original growth bound')
        _require(type(polynomial) is dict and all(type(n) is int and n >= 0 and type(matrix) is dict
                 for n, matrix in polynomial.items()), 'complete nonnegative residual polynomial degrees required')
        _require(all(type(pair) is tuple and len(pair) == 2 and all(type(x) is int for x in pair)
                     for matrix in polynomial.values() for pair in matrix.values()),
                 'exact integer residual coefficient pairs required')
        polynomial = {n: matrix for n, matrix in polynomial.items() if matrix}
        if not polynomial:
            continue
        matching = next((cluster for cluster in clusters if
            width*(abs(exponent[0]-cluster[0][0])+abs(exponent[1]-cluster[0][1])) <= Q(1, 2)), None)
        if matching is None:
            matching = exponent, []
            clusters.append(matching)
        matching[1].append((exponent, polynomial))
    return clusters


def _cluster_bound(anchor, members, denominator, width, order):
    scalar_denominator = 1
    expansions = []
    separate = tail = Q(0)
    radius = Q(0)
    for exponent, polynomial in members:
        delta = width*(exponent[0]-anchor[0]), width*(exponent[1]-anchor[1])
        member_radius = abs(delta[0])+abs(delta[1])
        radius = max(radius, member_radius)
        _require(member_radius <= Q(1, 2), 'exact frequency difference exceeds the common carrier radius')
        powers = [(Q(1), Q(0))]
        for j in range(order):
            value = checked.fourier._multiply_pair(powers[-1], delta)
            powers.append((value[0]/Q(j+1), value[1]/Q(j+1)))
        for pair in powers:
            for value in pair:
                scalar_denominator = lcm(scalar_denominator, value.denominator)
        remainder = 4*member_radius**(order+1)/Q(factorial(order+1))
        for n, matrix in polynomial.items():
            norm = fixed._norm(matrix, denominator)
            separate += 2*norm/Q(n+1)
            tail += remainder*norm/Q(n+order+2)
        expansions.append((polynomial, powers))
    common = {}
    for polynomial, powers in expansions:
        weights = [tuple(value.numerator*(scalar_denominator//value.denominator) for value in pair)
                   for pair in powers]
        for n, matrix in polynomial.items():
            for j, factor in enumerate(weights):
                fixed._add(common.setdefault(n+j, {}), matrix, factor)
    common_price = 2*sum((fixed._norm(matrix, denominator*scalar_denominator)/Q(n+1)
                          for n, matrix in common.items()), Q(0))
    clustered = common_price+tail
    selected = min(separate, clustered)
    return selected, {'anchor_per_second': list(map(str, anchor)),
        'normalized_anchor_growth': str(width*anchor[0]),
        'exact_member_exponents_per_second': [list(map(str, exponent)) for exponent, _ in members],
        'normalized_complex_radius': str(radius), 'expansion_order': order,
        'original_separate_frequency_integral': str(separate),
        'common_polynomial_integral': str(common_price), 'complex_exponential_remainder': str(tail),
        'selected_residual_integral': str(selected),
        'selected_bound': 'common carrier' if clustered < separate else 'separate frequencies',
        'frequencies_identified_as_equal': False,
        'complete_residual_polynomial_degrees': sorted(common)}


def _clustered_defect(residual, denominator, width, order):
    _cluster_order(order)
    _require(type(denominator) is int and denominator > 0, 'positive exact residual coefficient denominator required')
    records = []
    total = Q(0)
    for anchor, members in _partition(residual, width):
        price, record = _cluster_bound(anchor, members, denominator, width, order)
        total += price
        records.append(record)
    return total, records


def _piece(source, columns, piece, current, start, mode_bits, exp_bits, envelope_order, cluster_order):
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
    defect, clusters = _clustered_defect(residual, denominator, width, cluster_order)
    begin, e0 = checked._evaluate(groups, width, Q(0), exp_bits)
    end, e1 = checked._evaluate(groups, width, Q(1), exp_bits)
    join = checked._difference(begin, current)+e0
    uniform = join+defect+rounding+tails+phases
    record = {'source_detector_interval_seconds': list(map(str, (start, start+width))),
        'source_exact_frequency_words_after_merge': len(residual), 'source_frequency_clusters': len(clusters),
        'frequency_cluster_prices': clusters,
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
            exponential_bits=192, envelope_order=10, cluster_order=12):
    _CHECK()
    _cluster_order(cluster_order)
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
            piece, current, time, mode_bits, exponential_bits, envelope_order, cluster_order)
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
        'envelope_order': envelope_order, 'cluster_order': cluster_order}


def verify(source, report):
    _CHECK()
    _require(type(report) is dict and report.get('schema') == SCHEMA+'/checked-complete-curve',
             'named frequency-clustered complete source certificate required')
    expected = certify(source, report['untrusted_trial'], upstream_error=(
        report['whole_upstream_trace_norm_error_once'] if source._inlet is None else 0),
        coefficient_bits=report['coefficient_bits'], exponential_bits=report['exponential_bits'],
        envelope_order=report['envelope_order'], cluster_order=report['cluster_order'])
    _require(expected == report, 'full clustered source residual, prices, frequency carriers or endpoint changed')
    return expected


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    helpers = (_require, _bindings, _cluster_order, _partition, _cluster_bound, _clustered_defect,
        _piece, certify, verify, factorial, lcm, _function, _signature, _check,
        fixed._coefficient_grid, fixed._add, fixed._norm, checked.fourier._multiply_pair,
        checked._modes, checked._descriptors, checked._evaluate, checked._difference,
        checked._initial, checked._gamma_price, checked._exact, checked._record_state,
        checked._copy, field._price_upper, checked.RetardedReceiptTrajectoryCertificate.record,
        checked.RetardedReceiptTrajectoryCertificate._input, integer.IntegerColumns.action,
        integer.IntegerColumns.phase_error, integer.RetardedComponentIntegerAction.record,
        trajectory.RetardedGaussianTrajectorySource.frame, trajectory.RetardedGaussianTrajectorySource._clock)
    return tuple(map(_function, helpers)), SCHEMA, full.DIMENSION


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             fixed._CHECK is _FIXED_CHECK, 'frequency-clustered residual checker execution closure changed')
    _FIXED_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
