"""Independent rational operator residual from the original H/R/raising data."""
from fractions import Fraction as Q

import gaussian_atomic_pulse_source as gaussian
import chebyshev_density_rha0032 as basis


def parts(record):
    raw = record['original_Gaussian_source']; bits = record['coefficient_bits']
    h = gaussian._matrix(raw['complete_static_H_per_second']); r = gaussian._matrix(raw['complete_natural_R_per_second'])
    raising = gaussian._matrix(raw['source_raising_operator_per_second'])
    first_d1 = next(i for i, state in enumerate(gaussian.dipole.STATES) if state.family == 'D1')
    omega1 = h.get((first_d1, first_d1), gaussian.dipole.ComplexRadical()).real.as_rational()
    if str(omega1) != record['D1_frame_frequency_per_second']: raise ValueError('independent spectator source frame changed')
    quiet = gaussian._sum(gaussian._scale(h, gaussian.dipole.ComplexRadical(0, -1)), gaussian._scale(r, Q(-1, 2)))
    for i, state in enumerate(gaussian.dipole.STATES):
        frequency = omega1 if state.family == 'D1' else Q(raw['carrier_angular_frequency_per_second']) if state.family == 'D2' else Q(0)
        gaussian.field._add(quiet, {(i, i): gaussian.dipole.ComplexRadical(0, frequency)})
    phase, phase_error = gaussian._exponential(0, Q(raw['phase_radians']), bits) if Q(raw['phase_radians']) else ((Q(1), Q(0)), Q(0))
    amplitude = gaussian._scale(raising, gaussian.dipole.ComplexRadical(*phase))
    drive = gaussian._scale(gaussian._sum(amplitude, gaussian.dipole.matrix_adjoint(amplitude)), gaussian.dipole.ComplexRadical(0, -1))
    k, ek = gaussian._pairs(quiet, bits); v, ev = gaussian._pairs(drive, bits)
    ev += 2*phase_error*gaussian._norm(raising, bits)
    if record['direction'] == 'reverse_right':
        k = {(j, i): z for (i, j), z in k.items()}; v = {(j, i): z for (i, j), z in v.items()}
    elif record['direction'] != 'forward': raise ValueError('independent direction changed')
    return k, ek, v, ev


def multiply(left, right):
    rows = {}
    for (i, j), value in right.items(): rows.setdefault(i, []).append((j, value))
    result = {}
    for (i, k), (a, b) in left.items():
        for j, (c, d) in rows.get(k, ()):
            x, y = result.get((i, j), (Q(0), Q(0))); value = x+a*c-b*d, y+a*d+b*c
            if value == (0, 0): result.pop((i, j), None)
            else: result[i, j] = value
    return result


def piece(record, value, current, elapsed, mode_bits, envelope_order=16):
    k, ek, v, ev = parts(record); width = Q(value['duration_seconds'])
    if width <= 0: raise ValueError('independent positive operator interval required')
    matrices = [basis.density.fourier._coefficient(row, 1 << mode_bits) for row in value['chebyshev_coefficients']]
    scalar = dict(record['original_Gaussian_source']); scalar['centre_seconds'] = record['source_scalar_centre_in_flow_coordinate']
    polynomial, tail = basis.gaussian_polynomial(scalar, elapsed, width, envelope_order, record['coefficient_bits'])
    g = basis.monomial_to_chebyshev(polynomial); residual = {}; norm = basis.density.fourier._norm
    rounding = gaussian_price = Q(0)
    for n, matrix in enumerate(matrices):
        for degree, weight in basis.derivative_weights(n).items():
            basis.density.fourier._add_rational(residual.setdefault(degree, {}), matrix, (Q(weight), Q(0)))
        quiet, drive = multiply(k, matrix), multiply(v, matrix)
        basis.density.fourier._add_rational(residual.setdefault(n, {}), quiet, (-width, Q(0)))
        for j, coefficient in enumerate(g):
            if coefficient:
                for degree, weight in basis.product_weights(j, n).items():
                    basis.density.fourier._add_rational(residual.setdefault(degree, {}), drive, (-width*coefficient*weight, Q(0)))
        rounding += width*(ek+(sum(map(abs, g), Q(0))+tail)*ev)*norm(matrix)
        gaussian_price += width*tail*norm(drive)
    begin, end = basis.endpoint(matrices, False), basis.endpoint(matrices, True)
    price = basis.density.fourier._difference(begin, current)+sum(map(norm, residual.values()), Q(0))+rounding+gaussian_price
    return width, end, price
