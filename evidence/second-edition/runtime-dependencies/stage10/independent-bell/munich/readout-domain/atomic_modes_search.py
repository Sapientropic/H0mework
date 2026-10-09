"""Generate a trial curve for the independent raw-generator residual checker."""
import numpy as np
from scipy.linalg import eig

import atomic_search as search


def generate(segment, *, mode_bits=60, threshold=1e-13):
    kernel = search.Kernel(segment)
    fields = [{q: search.complex_value(getattr(segment, name)[q]) for q in (-1, 0, 1)}
              for name in ("fields_r", "fields_c")]
    generator = kernel.generator(*fields, search.complex_value(segment.r), search.complex_value(segment.c)).getH().toarray()
    exponents, vectors = eig(generator, check_finite=False)
    initial = np.zeros(search.N ** 2, dtype=complex)
    initial[-1] = 1
    coefficients = np.linalg.solve(vectors, initial)
    weighted = vectors * coefficients[None, :]
    if not np.all(np.isfinite(exponents)) or not np.all(np.isfinite(weighted)):
        raise ArithmeticError("trial curve contains nonfinite modes")
    quantum, modes = 1 << mode_bits, []
    for exponent, column in zip(exponents, weighted.T):
        if np.sum(np.abs(column)) <= threshold:
            continue
        matrix = []
        for position, value in enumerate(column):
            real, imag = round(value.real * quantum), round(value.imag * quantum)
            if real or imag:
                # The source numerical kernel uses column-major vectorization.
                matrix.append([position % search.N, position // search.N, real, imag])
        modes.append({"lambda": [round(exponent.real * quantum), round(exponent.imag * quantum)], "matrix": matrix})
    return modes
