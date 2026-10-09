"""Minimal finite polynomial/observer sanity for the three new IR mouths.

Chosen operator polynomials are read first, and coefficients are inspected
before selecting any quotient. This verifies finite analytic algebra only,
not actual source generation, an infinite limit, or a physical error interval.
"""
import hashlib
import json
import math
from pathlib import Path
import sys


def matrix_scale(c, a):
    return [[c*x for x in row] for row in a]


def matrix_sub(a, b):
    return [[x-y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def max_entry(a):
    return max(abs(x) for row in a for x in row)


def scalar_polynomial(coefficients, z):
    value = 0j
    for coefficient in reversed(coefficients):
        value = value*z+coefficient
    return value


def matrix_polynomial(coefficients, z):
    return [[scalar_polynomial([c[i][j] for c in coefficients], z) for j in range(2)] for i in range(2)]


def run():
    positive, negative, failures, examples = {}, {}, [], {}

    def check(label, error, tolerance=2e-10):
        passed = math.isfinite(error) and error <= tolerance
        positive[label] = {"error": error, "tolerance": tolerance, "pass": passed}
        if not passed:
            failures.append(label)

    def reject(label, difference):
        passed = math.isfinite(difference) and difference > 1e-7
        negative[label] = {"difference": difference, "threshold": 1e-7, "pass": passed}
        if not passed:
            failures.append(label)

    leading = [[4, 1j], [2, 1]]
    response0 = [[1+1j, 2-1j], [-1+2j, 3+0.5j]]
    denominator = [1, 0.25-0.15j, 0.07]
    zero = [[0j, 0j], [0j, 0j]]
    observe = lambda op: -op[0][0]+4*op[1][1]
    check("complete observer kills nonzero original operator leading", abs(observe(leading)))
    reject("source operator leading genuinely nonzero", max_entry(leading))
    check("original denominator is nonzero at zero", abs(scalar_polynomial(denominator, 0)-1))

    def fixture(m, extra_zero=0):
        k = max(2*m-6, 0)
        operators, read_coefficients = [], []
        first = k+extra_zero
        for degree in range(first+3):
            read = zero if degree < first else matrix_scale([1, 1+1j, -0.25j][degree-first], response0)
            op_entries = [[None]*2 for _ in range(2)]
            for i in range(2):
                for j in range(2):
                    op = matrix_scale((degree+1)*(i+j+1), leading)
                    op[0][0] -= read[i][j]
                    op_entries[i][j] = op
            operators.append(op_entries)
            read_coefficients.append([[observe(op_entries[i][j]) for j in range(2)] for i in range(2)])
        return operators, read_coefficients

    def regular(coefficients, z, d=denominator):
        return matrix_scale(1/scalar_polynomial(d, z)**2, matrix_polynomial(coefficients, z))

    sigmas = [0.125, 0.0625, 0.03125, 0.0078125]
    for m, extra in [(1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (4, 1)]:
        label = "m="+str(m)+" extra="+str(extra)
        operators, coefficients = fixture(m, extra)
        k, q = max(2*m-6, 0), 2*m
        observed_order = next(i for i, coefficient in enumerate(coefficients) if max_entry(coefficient) > 0)
        check(label+" all required low coefficients vanish", max([max_entry(c) for c in coefficients[:k]]+[0]))
        check(label+" observed coefficient order is read from source", abs(observed_order-(k+extra)))
        # Quotient is chosen only after all required coefficient checks.
        quotient = coefficients[k:]
        g0 = coefficients[k] if q >= 6 else zero
        source_price = sum(abs(x) for coefficient in quotient for row in coefficient for x in row)
        if q >= 6:
            violations = [max(0, max_entry(regular(coefficients, s))-s**k*source_price) for s in sigmas]
            check(label+" full matrix real axis source price", max(violations))
        for z in [0.1, 0.1+0.07j]:
            r = regular(coefficients, z)
            pi = matrix_scale(z**(-q), r)
            g = regular(quotient, z) if q >= 6 else matrix_scale(z**(6-q), r)
            check(label+" same R sixth regularization at "+str(z), max_entry(matrix_sub(matrix_scale(z**6, pi), g)))
        real_errors, complex_errors = [], []
        for sigma in sigmas:
            for z, errors in [(sigma, real_errors), (sigma*(1+0.6j), complex_errors)]:
                r = regular(coefficients, z)
                normalized = matrix_scale(z**(6-q), r)
                errors.append(max_entry(matrix_sub(normalized, g0)))
        check(label+" real finite approach contracts", 0 if all(x>y for x, y in zip(real_errors, real_errors[1:])) else 1)
        check(label+" complex positive half plane approach contracts", 0 if all(x>y for x, y in zip(complex_errors, complex_errors[1:])) else 1)
        examples[label] = {"source_operator_leading_norm": max(max_entry(entry) for row in operators[0] for entry in row),
                           "required_zero_order": k, "read_numerator_order": observed_order,
                           "finite_source_total_entry_price": source_price,
                           "G0_max_entry": max_entry(g0), "real_errors": real_errors, "complex_errors": complex_errors}

    _, m3 = fixture(3)
    pi_large = max_entry(matrix_scale(sigmas[-1]**-6, regular(m3, sigmas[-1])))
    pi_small = max_entry(matrix_scale(sigmas[0]**-6, regular(m3, sigmas[0])))
    reject("sixth regularization does not imply unscaled Pi is finite", pi_large-pi_small)
    reject("nonzero source G0 is allowed", max_entry(m3[0]))
    _, low = fixture(2)
    reject("incorrectly cancel low branch as a high branch", max_entry(matrix_sub(matrix_scale(0.1**2, regular(low, 0.1)), regular(low, 0.1))))
    _, higher = fixture(4, 1)
    check("extra cancellation has zero sixth normalized value", max_entry(higher[2]))
    reject("sixth upper order need not be exact sixth pole order", max_entry(higher[3]))
    # Zero leading alone is insufficient for m=5: the required order is four.
    leading_only = [zero, response0]
    check("bad leading only fixture has zero leading read", max_entry(leading_only[0]))
    reject("leading zero alone leaves a forbidden lower coefficient", max_entry(leading_only[1]))
    sigma = 0.03125
    bad_price = sum(abs(x) for row in response0 for x in row)
    reject("leading only fixture violates the required fourth order real price", max_entry(regular(leading_only, sigma))-bad_price*sigma**4)
    bad_denominator = [0, 1]
    check("bad denominator genuinely vanishes at zero", abs(scalar_polynomial(bad_denominator, 0)))
    reject("ignoring denominator zero destroys regular quotient", max_entry(regular(m3, 0.0625, bad_denominator))-max_entry(regular(m3, 0.125, bad_denominator)))
    # The source uses max-entry norm; its total entry price can also bound other norms.
    ones = [[1, 1], [1, 1]]
    operator_on_unit = math.sqrt(2*(2/math.sqrt(2))**2)
    reject("max entry norm cannot be identified with operator two norm", operator_on_unit-max_entry(ones))

    return {"status": "pass" if not failures else "fail", "positive_count": len(positive), "negative_count": len(negative),
            "positive_checks": positive, "negative_checks": negative, "failures": failures,
            "scope": "finite observer reads of chosen operator polynomials divided by d(lambda)^2; verifies branch algebra, not actual source factor provenance or infinite limits",
            "matrix_norm": "max absolute entry as in original elementwise source norm; total entry price remains a valid coarse operator bound",
            "denominator_coefficients": [{"real": complex(c).real, "imag": complex(c).imag} for c in denominator],
            "examples": examples, "real_scales": sigmas, "complex_direction": {"real": 1, "imag": 0.6},
            "construction_order": "read complete operator coefficients first; inspect every low coefficient; then extract quotient from those same coefficients",
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == "__main__":
    try:
        result = run()
    except Exception as error:
        result = {"status": "fail", "failures": [type(error).__name__+": "+str(error)]}
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False)+"\n")
    print(json.dumps({key: result[key] for key in ["status", "positive_count", "negative_count", "failures"] if key in result}, sort_keys=True))
    print("json_sha256="+hashlib.sha256(output.read_bytes()).hexdigest())
    sys.exit(0 if result["status"] == "pass" else 1)
