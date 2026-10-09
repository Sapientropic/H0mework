"""Untrusted exponential proposals for the original full Gaussian density law.

The source supplies every quiet/drive column.  A small numerical Arnoldi
problem proposes frequencies, then the Gaussian jet supplies polynomial
corrections.  The original complete density residual checks the result.
"""
from fractions import Fraction as Q

import numpy as np
import gaussian_local_density_source as density


def _require(value, message):
    if not value:
        raise ValueError(message)


def _columns(source, initial, bits):
    owner = density._Columns(source, bits)
    space = set(initial); front = set(initial)
    while front:
        following = set()
        for key in front:
            for component in ('quiet', 'drive'):
                following.update(owner.column(component, key)[0])
        front = following-space; space.update(front)
    coordinates = tuple(sorted(space))
    addresses = {key: n for n, key in enumerate(coordinates)}
    actions = {}
    for component in ('quiet', 'drive'):
        entries = [(addresses[out], addresses[key], complex(float(a), float(b)))
                   for key in coordinates for out, (a, b) in owner.column(component, key)[0].items()]
        actions[component] = (
            np.array([a for a, _, _ in entries], dtype=np.int64),
            np.array([b for _, b, _ in entries], dtype=np.int64),
            np.array([c for _, _, c in entries], dtype=np.complex128))
    return coordinates, actions


def _action(entries, vector):
    rows, columns, values = entries
    result = np.zeros_like(vector)
    np.add.at(result, rows, values*vector[columns])
    return result


def _modes(quiet, drive, vector, envelope, midpoint, width, order, budget):
    size = vector.size; norm = np.linalg.norm(vector)
    if not norm:
        return [(0j, [vector.copy() for _ in range(order+1)])]
    maximum = min(budget, size)
    basis = np.zeros((size, maximum+1), dtype=np.complex128)
    hessenberg = np.zeros((maximum+1, maximum), dtype=np.complex128)
    basis[:, 0] = vector/norm; used = maximum
    for j in range(maximum):
        image = _action(quiet, basis[:, j])+midpoint*_action(drive, basis[:, j])
        for _ in range(2):
            projections = basis[:, :j+1].conj().T@image
            hessenberg[:j+1, j] += projections
            image -= basis[:, :j+1]@projections
        remaining = np.linalg.norm(image); hessenberg[j+1, j] = remaining
        if remaining <= 1e-13:
            used = j+1
            break
        basis[:, j+1] = image/remaining
    values, vectors = np.linalg.eig(hessenberg[:used, :used])
    starting = np.zeros(used, dtype=np.complex128); starting[0] = norm
    amplitudes = (basis[:, :used]@vectors)*np.linalg.solve(vectors, starting)
    result = []
    for exponent, initial in zip(values, amplitudes.T):
        # This only changes a numerical proposal.  The real source and its
        # contraction price are supplied exclusively by the checker.
        exponent = complex(min(0., exponent.real), exponent.imag)
        coefficients = [initial]; drives = [_action(drive, initial)]
        for n in range(order):
            image = _action(quiet, coefficients[n])-exponent*coefficients[n]
            for j in range(min(n+1, len(envelope))):
                image += envelope[j]*drives[n-j]
            coefficient = image*width/(n+1)
            _require(np.all(np.isfinite(coefficient)), 'finite exponential proposal budget required')
            coefficients.append(coefficient); drives.append(_action(drive, coefficient))
        result.append((exponent, coefficients))
    return result


def _rows(coordinates, vector, bits):
    result = []
    for (i, j), value in zip(coordinates, vector):
        a = round(float(value.real)*(1 << bits)); b = round(float(value.imag)*(1 << bits))
        if a or b:
            result.append([i, j, a, b])
    return result


def generate_trial(source, initial, stop, *, start=0, slices=8, order=8,
                   krylov_dimension=48, mode_bits=96, coefficient_bits=192, envelope_order=10):
    density._CHECK()
    _require(type(source) is density.GaussianLocalDensitySource,
             'closed original Gaussian density source required; a target action is not input')
    record = density.GaussianLocalDensitySource.record(source)
    raw = record['Gaussian_source']
    for bits in (mode_bits, coefficient_bits):
        density.gaussian._precision(bits)
    start, stop = map(density.full.nonnegative, (start, stop))
    _require(start <= stop and type(slices) is int and slices > 0 and type(order) is int and 0 <= order <= 64 and
             type(krylov_dimension) is int and 1 <= krylov_dimension <= 1089,
             'finite original source interval and numerical proposal budget required')
    original, pairs, _ = density._rotating_initial(raw, initial, start, mode_bits)
    coordinates, actions = _columns(raw, pairs, coefficient_bits)
    current = np.array([complex(float(pairs.get(k, (0, 0))[0]), float(pairs.get(k, (0, 0))[1]))
                        for k in coordinates], dtype=np.complex128)
    width = (stop-start)/slices; pieces = []
    for n in range(slices if start < stop else 0):
        origin = start+n*width
        polynomial, _ = density.gaussian._envelope_polynomial(raw, origin, width, envelope_order, coefficient_bits)
        middle = origin+width/2
        midpoint, _ = density.gaussian._exponential(
            -(middle-Q(raw['centre_seconds']))**2/(4*Q(raw['sigma_squared_seconds'])), 0, coefficient_bits)
        proposed = _modes(actions['quiet'], actions['drive'], current,
            [float(x) for x in polynomial], float(midpoint[0]), float(width), order, krylov_dimension)
        modes = [{'lambda_per_second': [str(Q.from_float(exponent.real)), str(Q.from_float(exponent.imag))],
                  'coefficients': [_rows(coordinates, vector, mode_bits) for vector in coefficients]}
                 for exponent, coefficients in proposed]
        piece = {'duration_seconds': str(width), 'modes': modes}
        # The next proposal uses the quantized previous witness, including
        # its entire Hermitian projection.  No certificate cache is involved.
        _, groups = density._density_modes(piece, mode_bits)
        endpoint = {}
        for (lr, li), polynomial in groups.items():
            value, _ = density.gaussian._exponential(lr*width, li*width, coefficient_bits)
            for matrix in polynomial.values():
                density.fourier._add_rational(endpoint, matrix, value)
        endpoint = density.fourier._hermitian(endpoint)
        current = np.array([complex(float(endpoint.get(k, (0, 0))[0]), float(endpoint.get(k, (0, 0))[1]))
                            for k in coordinates], dtype=np.complex128)
        pieces.append(piece)
    return {'schema': density.SCHEMA+'/untrusted-curve', 'source_record': record,
        'complete_initial_matrix': density.channel._input_record(original), 'start_seconds': str(start),
        'stop_seconds': str(stop), 'mode_bits': mode_bits, 'pieces': pieces, 'writer_correctness_assumed': False}
