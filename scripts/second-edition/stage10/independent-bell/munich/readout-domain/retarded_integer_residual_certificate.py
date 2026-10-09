"""Exact complete residuals on one common integer grid per source piece.

The original source issues the input and all G actions.  Exact rational
Gaussian/frequency scalars share a denominator before multiplication by
whole matrices; equal source frequency words still merge before the norm.
No source, Mark, matrix coordinate, or price is replaced by a cached value.
"""
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import hashlib

import retarded_component_integer_action as integer

checked, trajectory = integer.checked, integer.trajectory
field, gaussian, full = integer.field, trajectory.gaussian, integer.full
SCHEMA = 'stage10-source-retarded-common-integer-residual-certificate/v1'
_INTEGER_CHECK = integer._CHECK


def _require(value, message):
    if not value:
        raise ValueError(message)


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), Path(integer.__file__), Path(checked.__file__), Path(trajectory.__file__))}


def _coefficient_grid(matrix, bits):
    result = {}
    for key, (a, b) in matrix.items():
        values = []
        for value in (a, b):
            _require(type(value) is Q and value.denominator & (value.denominator-1) == 0 and
                     value.denominator.bit_length()-1 <= bits,
                     'original coefficient and integer G image must lie on their registered dyadic grid')
            values.append(value.numerator << (bits-value.denominator.bit_length()+1))
        if any(values):
            result[key] = tuple(values)
    return result


def _add(target, matrix, factor):
    real, imag = factor
    if not (real or imag):
        return
    for key, (a, b) in matrix.items():
        c, d = target.get(key, (0, 0))
        value = c+real*a-imag*b, d+real*b+imag*a
        if any(value):
            target[key] = value
        elif key in target:
            del target[key]


def _norm(matrix, denominator):
    return Q(sum(abs(a)+abs(b) for a, b in matrix.values()), denominator)


def _piece(source, columns, piece, current, start, mode_bits, exp_bits, envelope_order):
    width, groups = checked._modes(piece, mode_bits, source)
    states = [matrix for polynomial in groups.values() for matrix in polynomial.values()]
    active, descriptors = checked._descriptors(source, columns, start, start+width, states, envelope_order)
    # The curve's Hermitian conjugate introduces exactly one extra grid bit.
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
    residual = {}; rounding = tails = phases = Q(0)
    for exponent, polynomial in groups.items():
        lr, li = exponent
        for n, matrix in polynomial.items():
            coefficient = _coefficient_grid(matrix, grid_bits)
            _add(residual.setdefault(exponent, {}).setdefault(n, {}), coefficient,
                 weights[width*lr, width*li])
            if n:
                _add(residual.setdefault(exponent, {}).setdefault(n-1, {}), coefficient, weights[Q(n), Q(0)])
            for component, frequency, scalars, tail, _ in descriptors:
                image, error, _ = integer.IntegerColumns.action(columns, component, matrix, active)
                image_int = _coefficient_grid(image, grid_bits)
                target = lr, li+frequency
                for j, (a, b) in enumerate(scalars):
                    _add(residual.setdefault(target, {}).setdefault(n+j, {}), image_int,
                         weights[-width*a, -width*b])
                    rounding += 2*width*(abs(a)+abs(b))*error/Q(n+j+1)
                tails += 2*width*tail*(_norm(image_int, 1 << grid_bits)+error)/Q(n+1)
                phases += 2*width*integer.IntegerColumns.phase_error(columns, component, matrix, active)/Q(n+1)
    defect = 2*sum((_norm(matrix, denominator)/Q(n+1)
        for polynomial in residual.values() for n, matrix in polynomial.items()), Q(0))
    begin, e0 = checked._evaluate(groups, width, Q(0), exp_bits)
    end, e1 = checked._evaluate(groups, width, Q(1), exp_bits)
    join = checked._difference(begin, current)+e0
    uniform = join+defect+rounding+tails+phases
    record = {'source_detector_interval_seconds': list(map(str, (start, start+width))),
        'source_exact_frequency_words_after_merge': len(residual),
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
            for c, _, _, _, zero in descriptors if zero],
        'Hamiltonian_norm_exponential_used': False}
    return width, end, uniform, e1, record


def certify(source, trial, *, upstream_error=0, coefficient_bits=192,
            exponential_bits=192, envelope_order=10):
    _CHECK()
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
    time = start; accumulated = entry; records = []
    for piece in trial['pieces']:
        before = accumulated
        width, current, uniform, endpoint, detail = _piece(source._source, columns,
            piece, current, time, mode_bits, exponential_bits, envelope_order)
        time += width; accumulated += uniform+endpoint
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
        'coefficient_bits': coefficient_bits, 'exponential_bits': exponential_bits, 'envelope_order': envelope_order}


def verify(source, report):
    _CHECK()
    _require(type(report) is dict and report.get('schema') == SCHEMA+'/checked-complete-curve',
             'named common-integer complete source certificate required')
    expected = certify(source, report['untrusted_trial'], upstream_error=(
        report['whole_upstream_trace_norm_error_once'] if source._inlet is None else 0),
        coefficient_bits=report['coefficient_bits'], exponential_bits=report['exponential_bits'],
        envelope_order=report['envelope_order'])
    _require(expected == report, 'full source residual, prices, words or endpoint changed')
    return expected


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    helpers = (_require, _bindings, _coefficient_grid, _add, _norm, _piece, certify, verify, lcm,
        _function, _signature, _check, checked._modes, checked._descriptors, checked._evaluate,
        checked._difference, checked._initial, checked._gamma_price, checked._exact,
        checked._record_state, checked._copy, field._price_upper,
        checked.RetardedReceiptTrajectoryCertificate.record, checked.RetardedReceiptTrajectoryCertificate._input,
        integer.IntegerColumns.action, integer.IntegerColumns.phase_error,
        integer.RetardedComponentIntegerAction.record, trajectory.RetardedGaussianTrajectorySource.frame,
        trajectory.RetardedGaussianTrajectorySource._clock)
    return tuple(map(_function, helpers)), SCHEMA, full.DIMENSION


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
        integer._CHECK is _INTEGER_CHECK, 'common-integer residual checker execution closure changed')
    _INTEGER_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
