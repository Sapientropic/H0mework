"""Minimal fourth IR branch sanity reusing the paid sixth-IR polynomial tools.

Chosen source operator coefficients are observed before quotient extraction.
Finite controls do not certify actual source provenance or infinite limits.
"""
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys


sys.dont_write_bytecode = True
ROOT = next(path for path in [Path.cwd(), *Path.cwd().parents] if (path / "Lean/lean-toolchain").is_file())
HELPER = ROOT / "Verification/physics/low-energy-phenomenology/alpha-source/em-identification/check_actual_dressed_ir_return.py"
spec = importlib.util.spec_from_file_location("paid_ir_tools", HELPER)
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)
scale, sub, norm = h.matrix_scale, h.matrix_sub, h.max_entry


def run():
    positive, negative, failures, examples = {}, {}, [], {}

    def check(name, error, tolerance=2e-10):
        passed = math.isfinite(error) and error <= tolerance
        positive[name] = {"error": error, "tolerance": tolerance, "pass": passed}
        if not passed:
            failures.append(name)

    def reject(name, difference):
        passed = math.isfinite(difference) and difference > 1e-7
        negative[name] = {"difference": difference, "threshold": 1e-7, "pass": passed}
        if not passed:
            failures.append(name)

    # Same paired observer, operator leading and polynomial data as paid IR6.
    operator_leading = [[4, 1j], [2, 1]]
    response0 = [[1+1j, 2-1j], [-1+2j, 3+0.5j]]
    denominator, zero = [1, 0.25-0.15j, 0.07], [[0j, 0j], [0j, 0j]]
    observe = lambda operator: -operator[0][0]+4*operator[1][1]

    def fixture(m, extra=0):
        first, coefficients = max(2*m-4, 0)+extra, []
        for degree in range(first+3):
            read = zero if degree < first else scale([1, 1+1j, -0.25j][degree-first], response0)
            coefficient = [[0j]*2 for _ in range(2)]
            for i in range(2):
                for j in range(2):
                    operator = scale((degree+1)*(i+j+1), operator_leading)
                    operator[0][0] -= read[i][j]
                    coefficient[i][j] = observe(operator)
            coefficients.append(coefficient)
        return coefficients

    def regular(coefficients, z, d=denominator):
        return scale(1/h.scalar_polynomial(d, z)**2, h.matrix_polynomial(coefficients, z))

    sigmas = [0.125, 0.0625, 0.03125, 0.0078125]
    check("original denominator is nonzero at zero", abs(h.scalar_polynomial(denominator, 0)-1))
    for m, extra in [(1, 0), (2, 0), (3, 0), (4, 0), (4, 1)]:
        label, q = "m="+str(m)+" extra="+str(extra), 2*m
        k, coefficients = max(q-4, 0), fixture(m, extra)
        check(label+" complete low coefficient cancellation", max([norm(c) for c in coefficients[:k]]+[0]))
        quotient = coefficients[k:]
        l4 = coefficients[k] if q >= 4 else zero
        price = sum(abs(x) for c in quotient for row in c for x in row)
        if q >= 4:
            check(label+" full matrix real axis source price", max(max(0, norm(regular(coefficients, s))-s**k*price) for s in sigmas))
        algebra4, algebra6 = [], []
        real4, complex4, real6, complex6 = [], [], [], []
        for sigma in sigmas:
            for z, errors4, errors6 in [(sigma, real4, real6), (sigma*(1+0.6j), complex4, complex6)]:
                r = regular(coefficients, z)
                pi = scale(z**(-q), r)
                g = regular(quotient, z) if q >= 4 else scale(z**(4-q), r)
                normalized4, normalized6 = scale(z**4, pi), scale(z**6, pi)
                algebra4.append(norm(sub(normalized4, g)))
                algebra6.append(norm(sub(normalized6, scale(z**2, g))))
                errors4.append(norm(sub(normalized4, l4)))
                errors6.append(norm(normalized6))
        check(label+" same R fourth regularization", max(algebra4))
        check(label+" sixth return retains extra two powers", max(algebra6))
        for name, errors in [("real fourth", real4), ("complex fourth", complex4), ("real sixth zero", real6), ("complex sixth zero", complex6)]:
            check(label+" "+name+" finite approach contracts", 0 if all(x>y for x, y in zip(errors, errors[1:])) else 1)
        examples[label] = {"required_zero_order": k, "read_order": k+extra, "L4_max_entry": norm(l4),
                           "source_total_entry_price": price, "real4_errors": real4, "complex4_errors": complex4,
                           "real6_zero_errors": real6, "complex6_zero_errors": complex6}

    threshold, low, more = fixture(2), fixture(1), fixture(4, 1)
    reject("threshold m two permits nonzero L4", norm(threshold[0]))
    check("low branch m one L4 is zero", examples["m=1 extra=0"]["L4_max_entry"])
    check("further high cancellation permits zero L4", examples["m=4 extra=1"]["L4_max_entry"])
    s, t = sigmas[0], sigmas[-1]
    reject("fourth regularization does not make unweighted Pi finite", norm(scale(t**-4, regular(threshold, t)))-norm(scale(s**-4, regular(threshold, s))))
    reject("fourth bound does not force exact fourth observed pole", norm(more[5]))
    reject("low branch cannot use high cancellation formula", norm(sub(scale(s**2, regular(low, s)), regular(low, s))))
    leading_only = [zero, response0]
    check("bad leading only read vanishes at origin", norm(leading_only[0]))
    price = sum(abs(x) for row in response0 for x in row)
    reject("leading zero is insufficient for m three required order two", norm(regular(leading_only, t))-t**2*price)
    bad_d = [0, 1]
    check("bad denominator genuinely vanishes at origin", abs(h.scalar_polynomial(bad_d, 0)))
    reject("ignoring zero denominator destroys analytic fourth quotient", norm(regular(threshold, t, bad_d))-norm(regular(threshold, s, bad_d)))

    return {"status": "pass" if not failures else "fail", "positive_count": len(positive), "negative_count": len(negative),
            "positive_checks": positive, "negative_checks": negative, "failures": failures, "examples": examples,
            "scope": "chosen finite operator polynomial observer-read fixture; actual source factor provenance is supplied by the Lean closure, not this fixture",
            "matrix_norm": "original elementwise max-entry norm; total entry price also remains a valid coarse operator norm bound",
            "normalization": "fourth regularization returns L4; original sixth regularization equals lambda squared times that same analytic read and returns zero",
            "finite_samples": {"real_scales": sigmas, "complex_direction": {"real": 1, "imag": 0.6}},
            "proof_scope": "finite equality and contracting trends only; not an infinite-limit proof, unweighted Pi finiteness, exact pole order or physical identification",
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
