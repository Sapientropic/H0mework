"""Full-source density residuals in the bounded shifted Chebyshev basis."""
from fractions import Fraction as Q
from math import comb, factorial
import hashlib
import json

import gaussian_local_density_source as density

SCHEMA = 'stage10-source-complete-Chebyshev-density/rha0032'


def require(value, reason):
    if not value: raise ValueError(reason)


def digest(value):
    return hashlib.sha256(density.channel._canonical(value).encode()).hexdigest()


def derivative_weights(n):
    result = {k: 4*n for k in range(n-1, 0, -2)}
    if n % 2: result[0] = 2*n
    return result


def product_weights(m, n):
    result = {m+n: Q(1, 2)}
    result[abs(m-n)] = result.get(abs(m-n), Q(0))+Q(1, 2)
    return result


def monomial_to_chebyshev(coefficients):
    result = {}; power = {0: Q(1)}
    for value in coefficients:
        for n, weight in power.items(): result[n] = result.get(n, Q(0))+Q(value)*weight
        following = {}
        for n, weight in power.items():
            following[n] = following.get(n, Q(0))+weight/2
            if n == 0: following[1] = following.get(1, Q(0))+weight/2
            else:
                following[n-1] = following.get(n-1, Q(0))+weight/4
                following[n+1] = following.get(n+1, Q(0))+weight/4
        power = following
    return [result.get(n, Q(0)) for n in range(len(coefficients))]


def endpoint(coefficients, right):
    result = {}
    for n, matrix in enumerate(coefficients):
        density.fourier._add_rational(result, matrix, (Q(1 if right or n % 2 == 0 else -1), Q(0)))
    return result


def gaussian_polynomial(raw, start, width, order, bits):
    variance = Q(raw['sigma_squared_seconds']); offset = Q(start)-Q(raw['centre_seconds'])
    b, c = offset*width/(2*variance), width**2/(4*variance); radius = abs(b)+c
    value, error = density.gaussian._exponential(-offset**2/(4*variance), Q(0), bits)
    coefficients = [Q(0)]*(2*order+1)
    for k in range(order+1):
        for j in range(k+1): coefficients[k+j] += Q(comb(k, j), factorial(k))*(-b)**(k-j)*(-c)**j
    exponent = -((-radius.numerator)//radius.denominator)
    growth = Q(3)**exponent
    # The original Gaussian factor multiplies the Taylor remainder.  Retain
    # it at late source times rather than imposing a short-slice restriction.
    tail = (abs(value[0])+error)*growth*radius**(order+1)/factorial(order+1)+error*growth
    return [value[0]*x for x in coefficients], tail


def piece(columns, raw, value, current, start, mode_bits, envelope_order):
    require(type(value) is dict and set(value) == {'duration_seconds', 'chebyshev_coefficients'} and
        type(value['chebyshev_coefficients']) is list and 1 <= len(value['chebyshev_coefficients']) <= 65,
        'complete degree<=64 shifted Chebyshev density piece required')
    width = Q(value['duration_seconds']); require(width > 0, 'positive original free-flow slice required')
    matrices = [density.fourier._coefficient(row, 1 << mode_bits) for row in value['chebyshev_coefficients']]
    require(all(density.full._hermitian(m) for m in matrices), 'every complete Chebyshev coefficient must be Hermitian')
    gaussian, tail = gaussian_polynomial(raw, start, width, envelope_order, columns.bits)
    g = monomial_to_chebyshev(gaussian)
    for j, value in enumerate(g):
        if abs(value) < Q(1, 1 << 96): tail += abs(value); g[j] = Q(0)
    residual = {}; column_price = gaussian_price = Q(0)
    for n, matrix in enumerate(matrices):
        for k, weight in derivative_weights(n).items():
            density.fourier._add_rational(residual.setdefault(k, {}), matrix, (Q(weight), Q(0)))
        quiet, eq = columns.action('quiet', matrix); drive, ev = columns.action('drive', matrix)
        density.fourier._add_rational(residual.setdefault(n, {}), quiet, (-width, Q(0)))
        for j, coefficient in enumerate(g):
            if not coefficient: continue
            for k, weight in product_weights(j, n).items():
                density.fourier._add_rational(residual.setdefault(k, {}), drive, (-width*coefficient*weight, Q(0)))
        column_price += width*(eq+(sum(map(abs, g), Q(0))+tail)*ev+columns.phase_error*density.fourier._norm(matrix))
        gaussian_price += width*tail*(density.fourier._norm(drive)+ev)
    defect = sum((density.fourier._norm(matrix) for matrix in residual.values()), Q(0))
    begin, end = endpoint(matrices, False), endpoint(matrices, True)
    join = density.fourier._difference(begin, current); price = join+defect+column_price+gaussian_price
    return width, end, price, {'source_interval_seconds': list(map(str, (start, start+width))),
        'complete_shifted_Chebyshev_defect_upper': str(density.field._price_upper(defect, columns.bits)),
        'source_column_and_phase_price': str(density.field._price_upper(column_price, columns.bits)),
        'source_Gaussian_uniform_remainder_price': str(density.field._price_upper(gaussian_price, columns.bits)),
        'initial_join_price': str(density.field._price_upper(join, columns.bits)),
        'whole_piece_error_upper': str(density.field._price_upper(price, columns.bits)),
        'curve_degree': len(matrices)-1, 'residual_degree': max(residual, default=0),
        'retained_scalar_Gaussian_Chebyshev_coefficients': sum(bool(x) for x in g),
        'complete_complex_coordinates': len(set().union(*(set(m) for m in matrices))),
        'monomial_conversion_of_quantum_curve_used': False, 'Hermitian_CPTP_contraction_used': True}
