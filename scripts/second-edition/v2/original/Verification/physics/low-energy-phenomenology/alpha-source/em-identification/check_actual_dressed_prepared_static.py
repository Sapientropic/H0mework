"""Focused Hilbert-norm source prices and finite-window static-read controls.

Vector norms are Euclidean. Frobenius norms explicitly upper-bound operator
2-norms. The source prices concern N2 variation and N1 background time only.
All quadrature below is finite-window numerical sanity; it asserts neither an
infinite Laplace integral nor a physical error interval or Lean proof.
"""
import cmath
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys


sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = next(path for path in HERE.parents if (path / "Lean/lean-toolchain").is_file())
PRODUCTION = ROOT / "Verification/physics/low-energy-phenomenology/alpha-source/em-identification"
FIELD_HELPER = PRODUCTION / "check_actual_dressed_number_field.py"
ZERO_HELPER = PRODUCTION / "check_actual_dressed_number_zero.py"
EXPECTED_SOURCES = {
    "ActualDressedPreparedTimePrice": "4ca13c3fe0946e7e9910206ab777fc21a1c6ce5bbc00c92cfc9ea14e7be428f2",
    "ActualDressedPreparedSlopePrice": "59e0cc42124dbac08b3dc009a76e86d4ab77aed0466ff0c3fe1cb8d44b232fe0",
    "ActualDressedPreparedSlopeGrowth": "566a78920b51010bcd6bab0d4a09148c1605c0310a23f803f7b1effef501aeec",
    "ActualDressedFiniteStaticRead": "7af57a46e9a766c1fd2a430f6f2ee0eae3557ab9825423530b8b89d349620614",
}


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


field = load(FIELD_HELPER, "field_controls")
base = load(ZERO_HELPER, "zero_controls")
zero, add, scale, mul, apply = base.zero, base.add, base.scale, base.mul, base.apply
product, product_jet, sub = field.product, field.product_jet, field.sub


def euclidean(vector):
    return math.sqrt(sum(abs(entry)**2 for entry in vector))


def frobenius(matrix):
    return math.sqrt(sum(abs(entry)**2 for row in matrix for entry in row))


def vector_sub(left, right):
    return [x-y for x, y in zip(left, right)]


def adjoint(matrix):
    return [[matrix[j][i].conjugate() for j in range(len(matrix))] for i in range(len(matrix))]


def occupation_price(order, a, time):
    return sum((abs(time)*a)**degree for degree in range(order+1))


def simpson(values, length):
    intervals = len(values)-1
    if intervals <= 0 or intervals % 2:
        raise ValueError("Simpson needs a positive even interval count")
    weights = [1]+[4 if i % 2 else 2 for i in range(1, intervals)]+[1]
    if isinstance(values[0], list):
        result = zero(len(values[0]))
        for weight, value in zip(weights, values):
            result = add(result, scale(weight, value))
        return scale(length/(3*intervals), result)
    return length*sum(weight*value for weight, value in zip(weights, values))/(3*intervals)


def prefix_jets(c, cp, a, ap, time, tails, label):
    """Ordered-word tangent recurrence, separate from the full Frechet block.

Layer l is the coefficient with exactly l occurrences of A. The 80th Taylor
polynomial keeps all noncommuting placements and their field tangents.
"""
    n = len(c)
    terms, slopes = [base.identity(n), zero(n), zero(n)], [zero(n) for _ in range(3)]
    totals, directions = [base.identity(n), zero(n), zero(n)], [zero(n) for _ in range(3)]
    for degree in range(1, 81):
        following, tangents = [], []
        for layer in range(3):
            value = mul(c, terms[layer])
            tangent = add(mul(cp, terms[layer]), mul(c, slopes[layer]))
            if layer:
                value = add(value, mul(a, terms[layer-1]))
                tangent = add(tangent, add(mul(ap, terms[layer-1]), mul(a, slopes[layer-1])))
            following.append(scale(-1j*time/degree, value))
            tangents.append(scale(-1j*time/degree, tangent))
        terms, slopes = following, tangents
        totals = [add(total, term) for total, term in zip(totals, terms)]
        directions = [add(total, term) for total, term in zip(directions, slopes)]
    # Upper bound for the norm of the augmented layer/tangent block generator.
    radius = abs(time)*(base.norm(c)+base.norm(a)+base.norm(cp)+base.norm(ap))
    # Summing up to three extracted layer blocks costs at most a factor three.
    tail = 3*math.exp(radius)*radius**81/math.factorial(81)
    if tail >= 1e-25:
        raise ArithmeticError("prefix tangent Taylor tail exceeds control limit")
    tails[label] = tail
    two = (add(totals[0], totals[1]), add(directions[0], directions[1]))
    three = (add(two[0], totals[2]), add(two[1], directions[2]))
    return three, two


def run():
    sources = {}
    for module, expected in EXPECTED_SOURCES.items():
        candidates = [HERE/(module+".lean"), PRODUCTION/(module+".lean")]
        if module == "ActualDressedFiniteStaticRead":
            candidates.append(ROOT / "Lean/scratch/AlphaSource/ActualDressedFiniteStaticReadOwn" / (module+".lean"))
        path = next((path for path in candidates if path.is_file()), None)
        if path is None:
            raise FileNotFoundError("fixed source missing: "+module)
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if digest != expected:
            raise ValueError("fixed source SHA mismatch: "+module)
        sources[str(path.relative_to(ROOT))] = digest

    positives, negatives, failures, tails, prices = {}, {}, [], {}, {}
    equality_limit, gap_limit = 2e-10, 1e-7

    def record(name, error, tolerance=equality_limit):
        passed = math.isfinite(error) and error <= tolerance
        positives[name] = {"error": error, "tolerance": tolerance, "pass": passed}
        if not passed:
            failures.append(name)

    def equality(name, left, right, tolerance=equality_limit):
        record(name, frobenius(sub(left, right)) if isinstance(left, list) else abs(left-right), tolerance)

    def bound(name, value, upper):
        tolerance = equality_limit*max(1, upper)
        record(name, max(0, value-upper), tolerance)
        prices[name] = {"observed_euclidean_norm": value, "upper_bound": upper, "slack": upper-value}

    def reject(name, gap):
        passed = math.isfinite(gap) and gap > gap_limit
        negatives[name] = {"difference": gap, "threshold": gap_limit, "pass": passed}
        if not passed:
            failures.append(name)

    data = field.family()
    c, cp, a, ap, lc, lcp, la, lap, q, qp = data
    n, energy = len(c), 0.31+0.79j
    g, current = add(c, a), add(cp, ap)
    af, jf = frobenius(a), frobenius(current)
    p2 = zero(n)
    for i in range(4, n):
        p2[i][i] = 1
    created, background = [0j]*n, [0j]*n
    created[4], created[5] = 1/math.sqrt(2), 1j/math.sqrt(2)
    background[0], background[1] = 1.7-0.2j, 0.6+0.4j
    scaled = [3.2*entry for entry in created]
    mixed = [0j]*n
    mixed[4], mixed[5], mixed[6], mixed[8], mixed[9] = 0.5-0.2j, 0.3j, 1.3+0.4j, -0.7+0.6j, 0.2+0.1j
    vectors = {"norm one created": created, "scaled created": scaled, "mixed N2 grades": mixed}
    equality("original base C is Hermitian", c, adjoint(c))
    equality("actual created vector is norm one", euclidean(created), 1)
    equality("complete current preserves entire N2", product(p2, current, p2), mul(current, p2))
    reject("original C and raising A do not commute", frobenius(sub(mul(c, a), mul(a, c))))

    def time(value, label):
        result, tail = base.exponential(scale(-1j*value, g))
        tails[label] = tail
        return result

    chosen_time, chosen_jet = None, None
    for t in [-0.7, 0.0, 0.45, 1.1]:
        label = "t="+str(t)
        jet = field.frechet_exp(scale(-1j*t, g), scale(-1j*t, current), tails, label+" full Frechet")
        duhamel_samples = []
        for index in range(33):
            s = t*index/32
            duhamel_samples.append(product(time(s, label+" Duhamel left "+str(index)), scale(-1j, current), time(t-s, label+" Duhamel right "+str(index))))
        duhamel = simpson(duhamel_samples, t)
        equality(label+" ordered Duhamel equals full Frechet direction", duhamel, jet[1], 3e-8)
        for name, vector in vectors.items():
            prefix = label+" "+name
            evolved, slope = apply(jet[0], vector), apply(jet[1], vector)
            record(prefix+" original slope remains N2", euclidean(vector_sub(apply(p2, slope), slope)))
            vnorm = euclidean(vector)
            polynomial = occupation_price(2, af, t)
            bound(prefix+" full time P2 price", euclidean(evolved), polynomial*vnorm)
            bound(prefix+" full ordered variation price", euclidean(slope), abs(t)*jf*polynomial**2*vnorm)
            bound(prefix+" explicit degree five price", euclidean(slope), jf*(1+af)**4*vnorm*(1+abs(t))**5)
        bound(label+" original unnormalized N1 background time price", euclidean(apply(jet[0], background)), occupation_price(1, af, t)*euclidean(background))
        if t == 0.45:
            chosen_time, chosen_jet = t, jet

    reject("whole generator is incorrectly treated as unitary", abs(euclidean(apply(chosen_jet[0], created))-euclidean(created)))
    cp_jet = field.frechet_exp(scale(-1j*chosen_time, g), scale(-1j*chosen_time, cp), tails, "wrong current C prime")
    ap_jet = field.frechet_exp(scale(-1j*chosen_time, g), scale(-1j*chosen_time, ap), tails, "wrong current A prime")
    reject("replace full current by C prime changes actual output", euclidean(vector_sub(apply(chosen_jet[1], created), apply(cp_jet[1], created))))
    reject("replace full current by A prime changes actual output", euclidean(vector_sub(apply(chosen_jet[1], created), apply(ap_jet[1], created))))
    reject("omit vector norm scale invalidates zero time price", euclidean(scaled)-occupation_price(2, af, 0))
    reject("incorrect norm one background invalidates zero time price", euclidean(background)-occupation_price(1, af, 0))

    eye = base.identity(n)
    r = base.inverse(add(g, scale(-energy, eye)))
    lr = base.inverse(add(add(lc, la), scale(-energy, eye)))
    lu = base.inverse(add(lc, scale(-energy, eye)))
    rp = scale(-1, product(r, current, r))
    lrp = scale(-1, product(lr, add(lcp, lap), lr))
    lup = scale(-1, product(lu, lcp, lu))
    w2 = field.green_jet(c, cp, a, ap, energy, 3)
    w1 = field.green_jet(c, cp, a, ap, energy, 2)

    def read(matrix, vector):
        return base.inner(vector, apply(matrix, vector))

    def observer(created_matrix, background_matrix):
        return -read(created_matrix, created)+read(background_matrix, background)

    def static_slopes(t, label):
        tj = field.frechet_exp(scale(-1j*t, g), scale(-1j*t, current), tails, label+" full right")
        ltj = field.frechet_exp(scale(1j*t, add(lc, la)), scale(1j*t, add(lcp, lap)), tails, label+" full left")
        lctj = field.frechet_exp(scale(1j*t, lc), scale(1j*t, lcp), tails, label+" C left")
        three, two = prefix_jets(c, cp, a, ap, t, tails, label+" finite tangent recurrence")
        full = product_jet(ltj, (lr, lrp), (q, qp), (r, rp), tj)[1]
        finite2 = product_jet(lctj, (lu, lup), (q, qp), w2, three)[1]
        finite1 = product_jet(lctj, (lu, lup), (q, qp), w1, two)[1]
        return observer(full, full), observer(finite2, finite1), three[0], two[0]

    window, intervals = 0.8, 32
    nodes = [window*index/intervals for index in range(intervals+1)]
    values = [static_slopes(t, "window node "+str(index)) for index, t in enumerate(nodes)]
    pointwise_errors = [abs(full-finite) for full, finite, _, _ in values]
    record("finite constant field slope equals original complete fivefactor jet at all window nodes", max(pointwise_errors))
    # Compare the separate ordered-word recurrence with the independent prefix helper.
    three, tail = base.prefixes(c, a, window, 3)
    tails["independent N2 prefix endpoint"] = tail
    two, tail = base.prefixes(c, a, window, 2)
    tails["independent N1 prefix endpoint"] = tail
    equality("ordered word tangent recurrence N2 value matches independent helper", values[-1][2], three)
    equality("ordered word tangent recurrence N1 value matches independent helper", values[-1][3], two)
    integrals = {}
    for lam in [0.8+0.2j, 1.3+0.1j]:
        original = [cmath.exp(-lam*t)*value[0] for t, value in zip(nodes, values)]
        finite = [cmath.exp(-lam*t)*value[1] for t, value in zip(nodes, values)]
        full_integral, finite_integral = simpson(original, window), simpson(finite, window)
        label = "lambda="+str(lam)
        equality(label+" same window damped original equals finite slope integral", full_integral, finite_integral)
        coarse = simpson(finite[::2], window)
        equality(label+" finite window Simpson convergence sanity", coarse, finite_integral, 1e-6)
        reject(label+" multiply actual window read by lambda changes read", abs(full_integral-lam*full_integral))
        integrals[label] = {"real": finite_integral.real, "imag": finite_integral.imag,
                            "coarse_fine_difference": abs(coarse-finite_integral), "extra_lambda_normalization": False}

    return {"status": "pass" if not failures else "fail", "positive_count": len(positives), "negative_count": len(negatives),
            "positive_checks": positives, "negative_checks": negatives, "price_checks": prices, "failures": failures,
            "source_sha256": sources, "expected_source_sha256": EXPECTED_SOURCES,
            "helper_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in [FIELD_HELPER, ZERO_HELPER]},
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "scope": "finite controls for fixed N2 time/variation prices, norm one source and original N1 background time; complete static read comparison on one finite window",
            "norms": {"vector": "Euclidean 2 norm", "operator_bound": "Frobenius upper bound on induced operator 2 norm",
                      "raising_frobenius_bound": af, "current_frobenius_bound": jf,
                      "N2_vector_norms": {name: euclidean(vector) for name, vector in vectors.items()},
                      "original_background_norm": euclidean(background), "price_field": 0,
                      "P2": "1+abs(t)*a+(abs(t)*a)^2", "P1": "1+abs(t)*a"},
            "price_times": [-0.7, 0.0, 0.45, 1.1],
            "ordered_duhamel": {"formula": "integral_0^t T(s)*(-i J)*T(t-s) ds", "Simpson_intervals": 32,
                                "role": "numerical sanity against independent Frechet block"},
            "static_window": {"length": window, "Simpson_intervals": intervals, "coarse_intervals": intervals//2,
                              "pointwise_full_finite_slope_errors": pointwise_errors, "damped_integrals": integrals,
                              "role": "finite-window numerical sanity only; no infinite-integral or physical-error inference"},
            "series": {"terms_through": 80, "tail_formula": "exp(radius)*radius^81/81!; prefix tangent sums use 3 times this bound; radius upper-bounds augmented generator infinity norm",
                       "tail_limit": 1e-25, "tail_bounds": tails, "scope": "exact-series truncation only, excluding roundoff and physical error"},
            "excluded_price_claims": ["N1 variation price", "complete fivefactor static sigma^-6 price"]}


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
