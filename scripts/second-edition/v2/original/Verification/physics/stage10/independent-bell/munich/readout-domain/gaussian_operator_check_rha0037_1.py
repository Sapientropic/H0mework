"""Check complete non-Hermitian operator streams against the same source K."""
from fractions import Fraction as Q
from pathlib import Path
import gzip
import hashlib
import json
import time

import gaussian_operator_flow_rha0037_1 as flow
import gaussian_operator_independent_rha0037_1 as independent
import chebyshev_basis_independent_rha0032 as polynomial


def restore(source, matrix, elapsed, bits):
    record = source.record(); a, b = map(Q, record['source_interval_seconds'])
    raw = record['original_Gaussian_source']; omega1 = Q(record['D1_frame_frequency_per_second'])
    if record['direction'] == 'forward': start, stop = a, a+elapsed
    else: start, stop, matrix = b-elapsed, b, flow.transpose(matrix)
    frequencies = [omega1 if s.family == 'D1' else Q(raw['carrier_angular_frequency_per_second']) if s.family == 'D2' else Q(0)
                   for s in flow.gaussian.dipole.STATES]
    answer = {}; errors = {}; phases = {}
    for (i, j), value in matrix.items():
        angle = frequencies[j]*start-frequencies[i]*stop
        if angle not in phases:
            phases[angle] = flow.gaussian._exponential(0, angle, bits) if angle else ((Q(1), Q(0)), Q(0))
        phase, price = phases[angle]
        answer[i, j] = flow.gaussian.dipole.ComplexRadical(*flow.gaussian.field._product(phase, value))
        errors[i, j] = price*(abs(value[0])+abs(value[1]))
    return answer, flow.gaussian.full._operator_bound(errors)


def certify(source, path, output, *, envelope_order=16, allow_float64=False, strategy='integer', progress=None):
    flow.require(type(source) is flow.GaussianOperatorFlow and strategy in ('integer', 'rational') and
                 type(allow_float64) is bool and type(envelope_order) is int and 0 <= envelope_order <= 32,
                 'closed operator flow and registered residual strategy required')
    raw = source.record(); path, output = Path(path), Path(output)
    output.mkdir(parents=True, exist_ok=False)
    with path.open('rb') as handle: witness_sha = hashlib.file_digest(handle, 'sha256').hexdigest()
    basis = polynomial.check(flow.basis.derivative_weights, flow.basis.product_weights, 2*envelope_order, 64)
    current = {(i, i): (Q(1), Q(0)) for i in range(33)}; elapsed = error = Q(0)
    columns = flow.IntegerColumns(source); started = time.monotonic(); records = []; cross = []
    with gzip.open(path, 'rt') as handle:
        header = json.loads(next(handle)); mode_bits = header['mode_bits']; flow.gaussian._precision(mode_bits)
        flow.require(header['schema'] == flow.SCHEMA+'/untrusted-stream' and
            header['flow_source_sha256'] == flow.digest(raw) and header['flow_interval_seconds'] == raw['flow_interval_seconds'] and
            header['direction'] == raw['direction'] and header['initial_operator_is_identity'] is True and
            header['operator_Hermitian_projected'] is False and header['inverse_propagator_used'] is False and
            header['writer_correctness_assumed'] is False and type(header['piece_count']) is int and header['piece_count'] > 0 and
            type(header['curve_degree']) is int and 1 <= header['curve_degree'] <= 64 and
            (header['numeric_mantissa_bits'] >= 64 and header['float64_override'] is False or allow_float64),
            'operator source, direction, complete inventory or arithmetic policy changed')
        for index, line in enumerate(handle):
            flow.require(index < header['piece_count'], 'extra operator piece')
            value = json.loads(line)
            if strategy == 'integer':
                width, endpoint, price, detail = flow.piece(source, columns, value, current, elapsed, mode_bits, envelope_order)
            else:
                width, endpoint, price = independent.piece(raw, value, current, elapsed, mode_bits, envelope_order)
                detail = {'whole_piece_operator_error': str(price), 'residual_strategy': 'independent rational'}
            if index in (0, header['piece_count']//2, header['piece_count']-1):
                w, end, p = independent.piece(raw, value, current, elapsed, mode_bits, envelope_order)
                flow.require(w == width and end == endpoint and abs(p-price) <= Q(1, 1 << 80),
                             'independent source/operator residual disagreement')
                cross.append({'piece': index+1, 'independent_piece_price': str(p), 'integer_piece_price': str(price),
                              'complete_endpoint_exactly_equal': True, 'price_difference_below_2pow_minus80': True})
            elapsed += width; error += price
            flow.require(elapsed <= Q(raw['flow_interval_seconds'][1]), 'operator curve crossed its source horizon')
            records.append(detail); current = endpoint
            checkpoint = {'piece': index+1, 'flow_source_sha256': flow.digest(raw), 'untrusted_stream_sha256': witness_sha,
                'checked_through_flow_seconds': str(elapsed), 'complete_rotating_endpoint': [
                    [i, j, str(a), str(b)] for (i, j), (a, b) in sorted(current.items())],
                'cumulative_rotating_operator_error': str(flow.gaussian.field._price_upper(error, raw['coefficient_bits']))}
            with (output/f'piece-{index+1:04d}.json').open('x') as saved:
                json.dump(checkpoint, saved, sort_keys=True); saved.write('\n')
            if progress is not None:
                progress({'operator_piece': index+1, 'pieces': header['piece_count'], 'direction': raw['direction'],
                          'error_upper': float(error), 'seconds': time.monotonic()-started})
        flow.require(len(records) == header['piece_count'] and elapsed == Q(raw['flow_interval_seconds'][1]),
                     'complete original operator interval required')
    a, b = map(Q, raw['source_interval_seconds'])
    gamma = source._pulse.Gamma_math_price(a, b, bits=raw['coefficient_bits'])
    physical, phase = restore(source, current, elapsed, raw['coefficient_bits'])
    total = error+gamma; endpoint_error = total+phase
    report = {'schema': flow.SCHEMA+'/checked-stream', 'flow_source': raw,
        'untrusted_stream': {'bytes': path.stat().st_size, 'sha256': witness_sha}, 'stream_header': header,
        'complete_piece_prices': records, 'independent_finite_basis_check': basis, 'independent_source_prefixes': cross,
        'complete_rotating_endpoint': [[i, j, str(a), str(b)] for (i, j), (a, b) in sorted(current.items())],
        'complete_physical_endpoint': flow.gaussian.channel._input_record(physical),
        'rotating_operator_error': str(flow.gaussian.field._price_upper(error, raw['coefficient_bits'])),
        'mathematical_Gamma_price': str(gamma), 'physical_endpoint_frame_price': str(phase),
        'whole_uniform_operator_error': str(flow.gaussian.field._price_upper(total, raw['coefficient_bits'])),
        'whole_endpoint_operator_error': str(flow.gaussian.field._price_upper(endpoint_error, raw['coefficient_bits'])),
        'registered_absolute_accuracy': '1/100000000', 'registered_accuracy_passed': endpoint_error <= Q(1, 10**8),
        'source_operator_contraction_used': True, 'operator_Hermitian_projected': False,
        'inverse_propagator_used': False, 'old_inlet_error_applied_to_operator': False,
        'complete_registered_instrument_certified': False, 'actual_hardware_uniquely_identified': False,
        'residual_arithmetic': strategy, 'controller_advance': False, 'seconds': time.monotonic()-started}
    with (output/'checked-curve.json').open('x') as handle: json.dump(report, handle, sort_keys=True); handle.write('\n')
    return report
