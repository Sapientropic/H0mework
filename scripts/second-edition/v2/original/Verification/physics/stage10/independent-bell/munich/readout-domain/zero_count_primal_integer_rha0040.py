"""Common-denominator integer residual for the same full Chebyshev source.

Quantum coefficients and the paid source columns are dyadic.  Keep their
products as integers; only the Gaussian scalar polynomial is quantized, with
its entire difference added to the scalar uniform remainder.
"""
from fractions import Fraction as Q
from weakref import WeakKeyDictionary

import chebyshev_density_rha0032 as core
import zero_count_primal_source_rha0040 as source

density = core.density
_COMPILED = WeakKeyDictionary()


def ceil_scaled(value, bits):
    value = Q(value)*(1 << bits)
    return -((-value.numerator)//value.denominator)


class Columns:
    def __init__(self, original):
        core.require(type(original) is source.Columns, 'the original complete density columns are required')
        self.original = original; self.bits = original.bits; self.error_bits = self.bits+32; self.cache = {}

    def column(self, component, key):
        index = component, key
        if index not in self.cache:
            values, error = self.original.column(component, key); integers = {}
            for out, (a, b) in values.items():
                x, y = a*(1 << self.bits), b*(1 << self.bits)
                core.require(x.denominator == y.denominator == 1, 'source column is not its registered exact dyadic')
                integers[out] = x.numerator, y.numerator
            self.cache[index] = integers, ceil_scaled(error, self.error_bits)
        return self.cache[index]

    def action(self, component, matrix):
        result = {}; price = 0
        for key, (a, b) in matrix.items():
            values, error = self.column(component, key); price += (abs(a)+abs(b))*error
            for out, (x, y) in values.items():
                r, i = result.get(out, (0, 0)); result[out] = r+x*a-y*b, i+x*b+y*a
        return result, price


def add(target, source, weight):
    if not weight: return
    for key, (a, b) in source.items():
        r, i = target.get(key, (0, 0)); value = r+weight*a, i+weight*b
        if value == (0, 0): target.pop(key, None)
        else: target[key] = value


def norm(matrix):
    return sum(abs(a)+abs(b) for a, b in matrix.values())


def piece(original_columns, raw, value, current, start, mode_bits, envelope_order):
    core.require(type(value) is dict and set(value) == {'duration_seconds', 'chebyshev_coefficients'} and
        type(value['chebyshev_coefficients']) is list and 1 <= len(value['chebyshev_coefficients']) <= 65,
        'complete registered Chebyshev coefficient inventory required')
    width = Q(value['duration_seconds']); core.require(width > 0, 'positive original source interval required')
    quantum = 1 << mode_bits; matrices = [density.fourier._coefficient(row, quantum) for row in value['chebyshev_coefficients']]
    core.require(all(density.full._hermitian(m) for m in matrices), 'complete Hermitian coefficients required')
    integers = [{key: (int(a*quantum), int(b*quantum)) for key, (a, b) in matrix.items()} for matrix in matrices]
    compiled = _COMPILED.get(original_columns)
    if compiled is None: compiled = Columns(original_columns); _COMPILED[original_columns] = compiled
    scalar_bits = original_columns.bits; scalar_quantum = 1 << scalar_bits
    polynomial, tail = core.gaussian_polynomial(raw, start, width, envelope_order, original_columns.bits)
    g = core.monomial_to_chebyshev(polynomial); scalars = []
    for coefficient in g:
        chosen = 0 if abs(coefficient) < Q(1, 1 << 96) else round(coefficient*scalar_quantum)
        tail += abs(coefficient-Q(chosen, scalar_quantum)); scalars.append(chosen)
    g_norm = Q(sum(map(abs, scalars)), scalar_quantum)
    scale = width.denominator*(1 << (original_columns.bits+mode_bits+scalar_bits+1))
    derivative_scale = width.denominator*(1 << (original_columns.bits+scalar_bits+1))
    quiet_scale = width.numerator*(1 << (scalar_bits+1))
    residual = {}; quiet_error = drive_error = drive_norm = input_norm = 0
    for n, matrix in enumerate(integers):
        input_norm += norm(matrix)
        for k, weight in core.derivative_weights(n).items(): add(residual.setdefault(k, {}), matrix, weight*derivative_scale)
        quiet, eq = compiled.action('quiet', matrix); drive, ev = compiled.action('drive', matrix)
        quiet_error += eq; drive_error += ev; drive_norm += norm(drive)
        add(residual.setdefault(n, {}), quiet, -quiet_scale)
        for j, coefficient in enumerate(scalars):
            if not coefficient: continue
            for k, weight in core.product_weights(j, n).items():
                twice = 2*weight; core.require(twice.denominator == 1, 'exact doubled Chebyshev product weight required')
                add(residual.setdefault(k, {}), drive, -width.numerator*coefficient*twice.numerator)
    defect = Q(sum(norm(m) for m in residual.values()), scale)
    source_error_denominator = quantum*(1 << compiled.error_bits)
    column_price = width*(Q(quiet_error, source_error_denominator)+
        (g_norm+tail)*Q(drive_error, source_error_denominator)+Q(0)*Q(input_norm, quantum))
    gaussian_price = width*tail*(Q(drive_norm, quantum*(1 << compiled.bits))+Q(drive_error, source_error_denominator))
    begin, end = core.endpoint(matrices, False), core.endpoint(matrices, True)
    join = density.fourier._difference(begin, current); price = join+defect+column_price+gaussian_price
    return width, end, price, {'source_interval_seconds': list(map(str, (start, start+width))),
        'complete_shifted_Chebyshev_defect_upper': str(density.field._price_upper(defect, original_columns.bits)),
        'source_column_and_phase_price': str(density.field._price_upper(column_price, original_columns.bits)),
        'source_Gaussian_uniform_remainder_price': str(density.field._price_upper(gaussian_price, original_columns.bits)),
        'initial_join_price': str(density.field._price_upper(join, original_columns.bits)),
        'whole_piece_error_upper': str(density.field._price_upper(price, original_columns.bits)),
        'curve_degree': len(matrices)-1, 'residual_degree': max(residual, default=0),
        'complete_complex_coordinates': len(set().union(*(set(m) for m in matrices))),
        'retained_scalar_Gaussian_Chebyshev_coefficients': sum(bool(x) for x in scalars),
        'common_integer_residual_denominator_bits': original_columns.bits+mode_bits+scalar_bits+1,
        'exact_source_duration_denominator': str(width.denominator),
        'scalar_quantization_paid_in_uniform_Gaussian_tail': True,
        'monomial_conversion_of_quantum_curve_used': False, 'Hermitian_CP_TNI_trace_contraction_used': True}
