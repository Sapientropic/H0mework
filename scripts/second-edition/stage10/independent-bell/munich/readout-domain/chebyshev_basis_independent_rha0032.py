"""Finite exact integer audit of the registered basis calculus, degree<=64."""


def add(a, b, factor=1):
    result = list(a)+[0]*max(0, len(b)-len(a))
    for i, value in enumerate(b): result[i] += factor*value
    while result and result[-1] == 0: result.pop()
    return result


def multiply(a, b):
    result = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): result[i+j] += x*y
    while result and result[-1] == 0: result.pop()
    return result


def check(derivative_weights, product_weights, gaussian_degree=20, curve_degree=64):
    degree = gaussian_degree+curve_degree; polynomials = [[1], [-1, 2]]
    for n in range(1, degree): polynomials.append(add(multiply([-2, 4], polynomials[n]), polynomials[n-1], -1))
    for n in range(curve_degree+1):
        actual = [(i+1)*value for i, value in enumerate(polynomials[n][1:])]; expected = []
        for k, weight in derivative_weights(n).items(): expected = add(expected, polynomials[k], weight)
        if actual != expected: raise ValueError('shifted Chebyshev derivative basis mismatch')
    for m in range(gaussian_degree+1):
        for n in range(curve_degree+1):
            actual = [2*x for x in multiply(polynomials[m], polynomials[n])]; expected = []
            for k, weight in product_weights(m, n).items():
                if (2*weight).denominator != 1: raise ValueError('non-integral doubled product weight')
                expected = add(expected, polynomials[k], int(2*weight))
            if actual != expected: raise ValueError('shifted Chebyshev product basis mismatch')
    return {'derivative_columns_checked': curve_degree+1,
        'product_columns_checked': (gaussian_degree+1)*(curve_degree+1), 'exact_integer_polynomial_arithmetic': True}
