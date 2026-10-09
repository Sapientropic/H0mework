"""Sparse numerical trial curves for the separate fluorescence source checker.

Only the raw action's exact reachable coordinates are retained.  BDF Newton
interpolation is expanded as a polynomial in u=t/Delta and dyadically rounded;
the resulting coefficients remain untrusted until their source residual passes.
"""
from fractions import Fraction as Q
import math

import numpy as np
from scipy.integrate import solve_ivp
from scipy import sparse

import atomic_full_forward as full
import fluorescence_channel as channel


def _polynomial(interpolant, start, duration):
    required = ("order", "t_shift", "denom", "D")
    if not all(hasattr(interpolant, name) for name in required):
        raise ValueError("registered BDF Newton-polynomial output required")
    order = interpolant.order
    if not 1 <= order <= 5 or len(interpolant.D) != order + 1:
        raise ValueError("complete BDF difference inventory required")
    coefficients = np.zeros((order + 1, len(interpolant.D[0])), dtype=complex)
    coefficients[0] = interpolant.D[0]
    basis = np.array([1.0])
    for k in range(order):
        shift = (float(start) - interpolant.t_shift[k]) / interpolant.denom[k]
        width = float(duration) / interpolant.denom[k]
        basis = np.convolve(basis, [shift, width])
        for degree, value in enumerate(basis):
            coefficients[degree] += value * interpolant.D[k + 1]
    if not np.all(np.isfinite(coefficients)):
        raise ArithmeticError("nonfinite source trial coefficients")
    return coefficients


def generate(generator, initial, *, initial_counter=0, mode_bits=60, coefficient_bits=160,
             rtol=1e-10, atol=1e-13, max_coordinates=50000):
    channel._require(type(mode_bits) is int and 32 <= mode_bits <= 256, "registered trial-mode precision required")
    kernel = channel.SourceKernel(generator, coefficient_bits)
    channel._key((initial_counter, 0, 0), kernel.dimension, kernel.threshold)
    initial = channel._initial(initial, kernel.dimension)
    duration = channel._duration(kernel.source)
    if duration == 0:
        return []
    for tolerance in (rtol, atol):
        if type(tolerance) not in (float, int) or not math.isfinite(tolerance) or tolerance <= 0:
            raise ValueError("positive finite search tolerance required")
    keys = kernel.reachable(((initial_counter, i, j) for i, j in initial), max_coordinates)
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
    for (i, j), value in initial.items():
        a, _ = full.radical_midpoint(value.real, coefficient_bits)
        b, _ = full.radical_midpoint(value.imag, coefficient_bits)
        state[addresses[initial_counter, i, j]] = complex(float(a), float(b))
    endpoint = float(duration)
    if not math.isfinite(endpoint) or endpoint <= 0 or not np.all(np.isfinite(state)) or not np.all(np.isfinite(operator.data)):
        raise ValueError("finite numerical trial scale required")
    solution = solve_ivp(lambda _t, value: operator @ value, (0, endpoint), state,
                         method="BDF", jac=operator, rtol=rtol, atol=atol, dense_output=True)
    if not solution.success or solution.sol is None:
        raise ArithmeticError("source trial solver failed: " + solution.message)
    quantum, pieces = 1 << mode_bits, []
    for index, interpolant in enumerate(solution.sol.interpolants):
        start = Q.from_float(float(solution.t[index]))
        end = duration if index + 1 == len(solution.sol.interpolants) else Q.from_float(float(solution.t[index + 1]))
        width = end - start
        if width <= 0:
            raise ArithmeticError("source trial time partition is not increasing")
        polynomial = _polynomial(interpolant, start, width)
        matrices = []
        for row in polynomial:
            matrix = []
            for key, value in zip(keys, row):
                real, imag = round(float(value.real) * quantum), round(float(value.imag) * quantum)
                if real or imag:
                    matrix.append([*key, real, imag])
            matrices.append(matrix)
        pieces.append({"duration": str(width), "modes": [{"lambda": [0, 0], "coefficients": matrices}]})
    return pieces


def predict(generator, initial, *, initial_counter=0, upstream_error=0, mode_bits=60,
            coefficient_bits=160, exponential_bits=160, rtol=1e-10, atol=1e-13, max_coordinates=50000):
    pieces = generate(generator, initial, initial_counter=initial_counter, mode_bits=mode_bits,
                      coefficient_bits=coefficient_bits, rtol=rtol, atol=atol, max_coordinates=max_coordinates)
    return channel.certify(generator, initial, pieces, initial_counter=initial_counter,
                           upstream_error=upstream_error, mode_bits=mode_bits,
                           coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
