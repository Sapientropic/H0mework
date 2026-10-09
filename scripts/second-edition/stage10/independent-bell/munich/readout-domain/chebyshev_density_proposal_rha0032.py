"""Untrusted full-density Chebyshev proposals; this worker issues no source.

A frozen handoff supplies raw source data and a checked inlet factor.  NumPy
Taylor stepping proposes values at Lobatto nodes.  All interpolation, roundoff
and stepping error is left to the independent complete source residual.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import math
import time

import numpy as np
import gaussian_density_exponential_writer as shared
import chebyshev_density_rha0032 as core

density = shared.density


def matrix_norm(entries, size):
    _, columns, values = entries; totals = np.zeros(size, dtype=np.float64)
    np.add.at(totals, columns, np.abs(values))
    return float(totals.max(initial=0))


def gaussian_coefficients(raw, origin, width, degree):
    variance = float(Q(raw['sigma_squared_seconds'])); offset = origin-float(Q(raw['centre_seconds']))
    a, b = -offset*width/(2*variance), -width*width/(4*variance)
    result = [math.exp(-offset*offset/(4*variance))]
    for n in range(1, degree+1):
        result.append((a*result[n-1]+(2*b*result[n-2] if n >= 2 else 0))/n)
    return result


def taylor(quiet, drive, current, raw, origin, width, order):
    envelope = gaussian_coefficients(raw, origin, width, order)
    coefficients = [current]; drives = [shared._action(drive, current)]
    for n in range(order):
        value = shared._action(quiet, coefficients[n])
        for j in range(n+1): value += envelope[j]*drives[n-j]
        following = value*(width/(n+1))
        core.require(np.all(np.isfinite(following)), 'finite untrusted local stepping budget required')
        coefficients.append(following); drives.append(shared._action(drive, following))
    return coefficients


def evaluate(coefficients, x):
    result = np.zeros_like(coefficients[0])
    for value in reversed(coefficients): result = value+x*result
    return result


def propose(handoff, output, *, degree=64, piece_seconds=Q(1, 10**9), order=40,
            maximum_step_seconds=Q(1, 16*10**9), phase_step=3., mode_bits=96, coefficient_bits=192):
    core.require(handoff['schema'] == 'stage10-source-issued-free-density-handoff/rha0032' and
        type(degree) is int and 1 <= degree <= 64 and type(order) is int and 1 <= order <= 64 and
        Q(piece_seconds) > 0 and Q(maximum_step_seconds) > 0 and phase_step > 0,
        'registered finite raw proposal and source handoff required')
    source_record = handoff['source_record']; raw = source_record['Gaussian_source']
    initial = density.channel._read_input(handoff['complete_initial_matrix'], 33)
    start, stop = map(Q, handoff['source_interval_seconds']); core.require(start < stop, 'positive full free-flow interval required')
    original, pairs, _ = density._rotating_initial(raw, initial, start, mode_bits)
    coordinates, actions = shared._columns(raw, pairs, coefficient_bits)
    size = len(coordinates); core.require(size <= 1089, 'complete local coordinate budget exceeded')
    current = np.array([complex(float(pairs.get(k, (0, 0))[0]), float(pairs.get(k, (0, 0))[1])) for k in coordinates])
    addresses = {key: i for i, key in enumerate(coordinates)}
    adjoints = np.array([addresses[j, i] for i, j in coordinates], dtype=np.int64)
    norm = matrix_norm(actions['quiet'], size)+matrix_norm(actions['drive'], size)
    step = min(float(Q(maximum_step_seconds)), phase_step/norm if norm else float(Q(maximum_step_seconds)))
    intervals = []; at = start
    while at < stop:
        following = min(stop, at+Q(piece_seconds)); intervals.append((at, following)); at = following
    core.require(len(intervals)*(degree+1)*size <= 12_000_000, 'untrusted serialized curve row budget exceeded')
    k = np.arange(degree+1); weights = np.ones(degree+1); weights[[0, -1]] = .5
    transform = (2/degree)*np.cos(np.pi*np.outer(k, k)/degree)*weights[None, :]
    transform[[0, -1], :] *= .5
    origin, end = float(start), float(stop); width = min(step, end-origin)
    coefficients = taylor(actions['quiet'], actions['drive'], current, raw, origin, width, order)
    quantum = 1 << mode_bits; output = Path(output); core.require(not output.exists(), 'untrusted curve path is immutable')
    started = time.monotonic(); steps = 1
    with output.open('xb') as handle, gzip.GzipFile(fileobj=handle, mode='wb', mtime=0) as compressed:
        def write(value): compressed.write((json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode())
        write({'schema': core.SCHEMA+'/untrusted-stream', 'source_record_sha256': core.digest(source_record),
            'initial_matrix_sha256': core.digest(handoff['complete_initial_matrix']),
            'source_interval_seconds': list(map(str, (start, stop))), 'mode_bits': mode_bits,
            'piece_count': len(intervals), 'curve_degree': degree, 'source_factor_id': handoff['source_factor_id'],
            'writer_correctness_assumed': False, 'numpy_version': np.__version__})
        for index, (lo, hi) in enumerate(intervals):
            times = float(lo)+(float(hi-lo))*(1+np.cos(np.pi*k/degree))/2
            values = np.zeros((degree+1, size), dtype=np.complex128)
            for node in reversed(range(degree+1)):
                target = float(times[node])
                while target > origin+width+1e-22:
                    current = evaluate(coefficients, 1); origin += width; width = min(step, end-origin)
                    core.require(width > 0, 'numerical time cursor exhausted before its source endpoint')
                    coefficients = taylor(actions['quiet'], actions['drive'], current, raw, origin, width, order); steps += 1
                values[node] = evaluate(coefficients, max(0., min(1., (target-origin)/width)))
            fitted = transform@values
            fitted = (fitted+fitted[:, adjoints].conj())/2
            rows = [shared._rows(coordinates, vector, mode_bits) for vector in fitted]
            write({'duration_seconds': str(hi-lo), 'chebyshev_coefficients': rows})
            if index % 8 == 0 or index+1 == len(intervals):
                print(json.dumps({'piece': index+1, 'pieces': len(intervals), 'local_coordinates': size,
                    'untrusted_Taylor_steps': steps, 'seconds': time.monotonic()-started}), flush=True)
    return {'schema': core.SCHEMA+'/untrusted-proposal-receipt', 'source_factor_id': handoff['source_factor_id'],
        'curve': {'path': output.name, 'bytes': output.stat().st_size, 'sha256': hashlib.sha256(output.read_bytes()).hexdigest()},
        'piece_count': len(intervals), 'degree': degree, 'mode_bits': mode_bits, 'local_coordinates': size,
        'numerical_step_seconds': step, 'untrusted_Taylor_steps': steps, 'source_checked': False,
        'seconds': time.monotonic()-started}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True); parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args(); result = propose(json.loads(args.input.read_text()), args.output)
    with args.receipt.open('x') as handle: json.dump(result, handle, sort_keys=True, indent=2); handle.write('\n')
