"""Untrusted sparse BDF trial producer for the closed full-mark BSM checker."""
from fractions import Fraction as Q
import math

import numpy as np
from scipy import sparse
from scipy.integrate import solve_ivp

import atomic_full_forward as full
import bsm_retry_source as bsm
import bsm_channel as channel
from fluorescence_channel_search import _polynomial


def generate_marked(generator, initial, *, mode_bits=60, coefficient_bits=160,
                    rtol=1e-10, atol=1e-13, max_coordinates=50000):
    channel.channel._require(type(mode_bits) is int and 32 <= mode_bits <= 256, "registered trial-mode precision required")
    kernel = channel.SourceKernel(generator, coefficient_bits)
    initial = channel._initial_marked(initial)
    for tolerance in (rtol, atol):
        if type(tolerance) not in (float, int) or not math.isfinite(tolerance) or tolerance <= 0:
            raise ValueError("positive finite search tolerance required")
    duration = kernel.source.duration
    keys = kernel.reachable(initial, max_coordinates)
    if not keys:
        return [{"duration": str(duration), "modes": [{"lambda": [0, 0], "coefficients": [[]]}]}]
    addresses = {key: i for i, key in enumerate(keys)}
    rows, columns, values = [], [], []
    for key, column in addresses.items():
        for target, (a, b) in kernel.column(key).items():
            rows.append(addresses[target])
            columns.append(column)
            values.append(complex(float(a), float(b)))
    operator = sparse.csc_matrix((values, (rows, columns)), shape=(len(keys), len(keys)))
    state = np.zeros(len(keys), dtype=complex)
    for key, value in initial.items():
        a, _ = full.radical_midpoint(value.real, coefficient_bits)
        b, _ = full.radical_midpoint(value.imag, coefficient_bits)
        state[addresses[key]] = complex(float(a), float(b))
    endpoint = float(duration)
    if not math.isfinite(endpoint) or endpoint <= 0 or not np.all(np.isfinite(state)) or not np.all(np.isfinite(operator.data)):
        raise ValueError("finite numerical trial scale required")
    solution = solve_ivp(lambda _t, value: operator @ value, (0, endpoint), state,
                         method="BDF", jac=operator, rtol=rtol, atol=atol, dense_output=True)
    if not solution.success or solution.sol is None:
        raise ArithmeticError("BSM trial solver failed: "+solution.message)
    pieces, quantum = [], 1 << mode_bits
    for index, interpolant in enumerate(solution.sol.interpolants):
        start = Q.from_float(float(solution.t[index]))
        end = duration if index+1 == len(solution.sol.interpolants) else Q.from_float(float(solution.t[index+1]))
        width = end-start
        if width <= 0:
            raise ArithmeticError("source trial time partition is not increasing")
        matrices = []
        for row in _polynomial(interpolant, start, width):
            matrix = []
            for key, value in zip(keys, row):
                a, b = round(float(value.real)*quantum), round(float(value.imag)*quantum)
                if a or b:
                    matrix.append([*key, a, b])
            matrices.append(matrix)
        pieces.append({"duration": str(width), "modes": [{"lambda": [0, 0], "coefficients": matrices}]})
    return pieces


def generate(generator, initial, *, initial_mark=bsm.INITIAL, **kwargs):
    channel.channel._require(type(initial_mark) is bsm.Mark, "original initial BSM Mark required")
    matrix = channel.channel._initial(initial, bsm.joint.DIMENSION)
    return generate_marked(generator, {(initial_mark, i, j): value for (i, j), value in matrix.items()}, **kwargs)


def predict_marked(generator, initial, *, upstream_error=0, mode_bits=60, coefficient_bits=160,
                   exponential_bits=160, rtol=1e-10, atol=1e-13, max_coordinates=50000):
    pieces = generate_marked(generator, initial, mode_bits=mode_bits, coefficient_bits=coefficient_bits,
                             rtol=rtol, atol=atol, max_coordinates=max_coordinates)
    return channel.certify_marked(generator, initial, pieces, upstream_error=upstream_error,
                mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)


def predict(generator, initial, *, initial_mark=bsm.INITIAL, **kwargs):
    channel.channel._require(type(initial_mark) is bsm.Mark, "original initial BSM Mark required")
    matrix = channel.channel._initial(initial, bsm.joint.DIMENSION)
    return predict_marked(generator, {(initial_mark, i, j): value for (i, j), value in matrix.items()}, **kwargs)
