"""Untrusted full33 operator curves on a relative forward or coflow clock."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import time

import numpy as np
import gaussian_operator_flow_rha0037_1 as source
import chebyshev_density_proposal_rha0032_2 as stepping


def columns(matrix, bits):
    rows, before, values = [], [], []
    for (i, k), (a, b) in matrix.items():
        z = np.clongdouble(stepping.long_rational(a))+np.clongdouble(1j)*stepping.long_rational(b)
        for j in range(33):
            rows.append(33*i+j); before.append(33*k+j); values.append(z)
    return np.array(rows, dtype=np.int64), np.array(before, dtype=np.int64), np.array(values, dtype=np.clongdouble)


def propose(handoff, output, *, degree=64, piece_seconds=Q(1, 10**9), order=40,
            maximum_step_seconds=Q(1, 16*10**9), mode_bits=96, allow_float64=False):
    source.require(handoff['schema'] == source.SCHEMA+'/handoff' and type(allow_float64) is bool,
                   'frozen source operator handoff required')
    bits = np.finfo(np.longdouble).nmant+1
    source.require(bits >= 64 or allow_float64, 'extended numerical mantissa required; float64 is an explicit control override')
    record = handoff['flow_source']; raw = record['original_Gaussian_source']
    source.require(record['direction'] in source.DIRECTIONS and type(degree) is int and 1 <= degree <= 64 and
                   type(order) is int and 1 <= order <= 64 and Q(piece_seconds) > 0 and Q(maximum_step_seconds) > 0,
                   'registered full operator numerical budget required')
    parts, frequency = source.compiled_parts(raw, record['coefficient_bits'])
    k, _, v, _ = parts
    source.require(str(frequency) == record['D1_frame_frequency_per_second'], 'same source spectator carrier required')
    if record['direction'] == 'reverse_right': k, v = source.transpose(k), source.transpose(v)
    quiet, drive = columns(k, record['coefficient_bits']), columns(v, record['coefficient_bits'])
    scalar = dict(raw); scalar['centre_seconds'] = record['source_scalar_centre_in_flow_coordinate']
    start, stop = map(Q, record['flow_interval_seconds']); source.require(start == 0 < stop, 'source relative clock starts at zero')
    current = np.eye(33, dtype=np.clongdouble).reshape(-1)
    coordinates = tuple((i, j) for i in range(33) for j in range(33))
    norm = stepping.matrix_norm(quiet, 1089)+stepping.matrix_norm(drive, 1089)
    step = min(Q(maximum_step_seconds), Q(str(np.longdouble(3)/np.longdouble(norm))) if norm else Q(maximum_step_seconds))
    intervals = []; at = start
    while at < stop:
        following = min(stop, at+Q(piece_seconds)); intervals.append((at, following)); at = following
    source.require(len(intervals)*(degree+1)*1089 <= 12_000_000, 'serialized operator curve budget exceeded')
    n = np.arange(degree+1, dtype=np.longdouble); weights = np.ones(degree+1, dtype=np.longdouble); weights[[0, -1]] = .5
    pi = np.longdouble('3.1415926535897932384626433832795028841971693993751')
    nodes = np.clip((1+np.cos(pi*n/degree))/2, 0, 1)
    transform = (np.longdouble(2)/degree)*np.cos(pi*np.outer(n, n)/degree)*weights[None, :]; transform[[0, -1], :] *= .5
    origin = start; width = min(step, stop-origin)
    coefficients = stepping.taylor(quiet, drive, current, scalar, origin, width, order)
    output = Path(output); source.require(not output.exists(), 'the untrusted operator stream is immutable')
    started = time.monotonic(); steps = 1
    with output.open('xb') as handle, gzip.GzipFile(fileobj=handle, mode='wb', mtime=0) as compressed:
        def write(value): compressed.write((json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode())
        write({'schema': source.SCHEMA+'/untrusted-stream', 'flow_source_sha256': source.digest(record),
            'flow_interval_seconds': list(map(str, (start, stop))), 'direction': record['direction'],
            'mode_bits': mode_bits, 'piece_count': len(intervals), 'curve_degree': degree,
            'numeric_mantissa_bits': bits, 'float64_override': allow_float64,
            'initial_operator_is_identity': True, 'operator_Hermitian_projected': False,
            'inverse_propagator_used': False, 'writer_correctness_assumed': False})
        for index, (lo, hi) in enumerate(intervals):
            values = np.zeros((degree+1, 1089), dtype=np.clongdouble)
            targets = [lo+(hi-lo)*Q(str(node)) for node in nodes]
            for node in reversed(range(degree+1)):
                target = targets[node]
                while target > origin+width:
                    current = stepping.evaluate(coefficients, np.longdouble(1)); origin += width; width = min(step, stop-origin)
                    source.require(width > 0, 'operator relative clock exhausted')
                    coefficients = stepping.taylor(quiet, drive, current, scalar, origin, width, order); steps += 1
                values[node] = stepping.evaluate(coefficients, stepping.long_rational((target-origin)/width))
            fitted = transform@values
            write({'duration_seconds': str(hi-lo), 'chebyshev_coefficients': [
                stepping.rows_extended(coordinates, vector, mode_bits) for vector in fitted]})
            if index % 8 == 0 or index+1 == len(intervals):
                print(json.dumps({'operator_piece': index+1, 'pieces': len(intervals), 'direction': record['direction'],
                    'untrusted_Taylor_steps': steps, 'seconds': time.monotonic()-started}), flush=True)
    return {'schema': source.SCHEMA+'/untrusted-proposal', 'flow_source_sha256': source.digest(record),
        'direction': record['direction'], 'numeric_mantissa_bits': bits, 'float64_override': allow_float64,
        'curve': {'path': output.name, 'bytes': output.stat().st_size, 'sha256': hashlib.sha256(output.read_bytes()).hexdigest()},
        'piece_count': len(intervals), 'curve_degree': degree, 'source_checked': False,
        'seconds': time.monotonic()-started}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True); parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args(); result = propose(json.loads(args.input.read_text()), args.output)
    with args.receipt.open('x') as handle: json.dump(result, handle, sort_keys=True, indent=2); handle.write('\n')
