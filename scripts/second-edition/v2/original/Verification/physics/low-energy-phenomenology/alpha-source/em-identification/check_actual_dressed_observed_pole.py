"""Finite controls for left-free jet, N1 slope, complete source price and pole scope.

This is finite matrix/algebra sanity, not a Lean proof, infinite-limit proof,
physical prediction or error interval. No experimental target is consumed.
"""
import cmath
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys


sys.dont_write_bytecode = True
ROOT = next(path for path in [Path.cwd(), *Path.cwd().parents] if (path / "Lean/lean-toolchain").is_file())
HELPERS = ROOT / "Verification/physics/low-energy-phenomenology/alpha-source/em-identification"


def load(name):
    spec = importlib.util.spec_from_file_location(name, HELPERS/(name+".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


f = load("check_actual_dressed_number_field")
b = load("check_actual_dressed_number_zero")
zero, add, scale, mul, apply = b.zero, b.add, b.scale, b.mul, b.apply
product, sub = f.product, f.sub


def vnorm(v):
    return math.sqrt(sum(abs(x)**2 for x in v))


def fnorm(a):
    return math.sqrt(sum(abs(x)**2 for row in a for x in row))


def adjoint(a):
    return [[a[j][i].conjugate() for j in range(len(a))] for i in range(len(a))]


def run():
    positive, negative, failures, tails, bounds = {}, {}, [], {}, {}

    def equal(name, x, y, tolerance=2e-10):
        error = fnorm(sub(x, y)) if isinstance(x, list) else abs(x-y)
        passed = math.isfinite(error) and error <= tolerance
        positive[name] = {"error": error, "tolerance": tolerance, "pass": passed}
        if not passed:
            failures.append(name)

    def bound(name, value, price):
        equal(name, max(0, value-price), 0, 2e-10*max(1, price))
        bounds[name] = {"observed": value, "upper_bound": price}

    def reject(name, gap):
        passed = math.isfinite(gap) and gap > 1e-7
        negative[name] = {"difference": gap, "threshold": 1e-7, "pass": passed}
        if not passed:
            failures.append(name)

    c, cp, a, ap, lc, lcp, _, _, q, contact = f.family()
    n, energy = len(c), 0.31+0.79j
    eye, g = b.identity(n), add(c, a)
    j0 = add(cp, ap)
    # The source generator is C(h)+Y(h)-z*1. Its field derivative has no z term.
    jenergy = add(cp, ap)
    created, background = [0j]*n, [0j]*n
    created[4], created[5] = 1/math.sqrt(2), 1j/math.sqrt(2)
    background[0], background[1] = 1.7-0.2j, 0.6+0.4j
    bg2 = vnorm(background)**2
    p1 = zero(n)
    for i in range(4):
        p1[i][i] = 1

    def observed(matrix, normalize_background=False):
        created_read = b.inner(created, apply(matrix, created))
        background_read = b.inner(background, apply(matrix, background))
        return -created_read+background_read/(bg2 if normalize_background else 1)

    u = b.inverse(add(lc, scale(-energy, eye)))
    r = b.inverse(add(g, scale(-energy, eye)))
    up = scale(-1, product(u, lcp, u))
    rp = scale(-1, product(r, jenergy, r))
    cpf, uf, qf, rf = fnorm(lcp), fnorm(u), fnorm(q), fnorm(r)
    cf, jgf, jtf, af = fnorm(contact), fnorm(jenergy), fnorm(j0), fnorm(a)
    four_price = cpf*uf*qf*rf+uf**2*cpf*qf*rf+uf*cf*rf+uf*qf*rf**2*jgf
    kernel_price = four_price*(1+af)**2+uf*qf*rf*jtf*(1+af)**4
    source_price = kernel_price*(1+bg2)
    equal("source field current is energy independent", jenergy, j0)
    equal("original left base compression is Hermitian", lc, adjoint(lc))
    equal("actual creation is norm one", vnorm(created), 1)
    equal("whole N1 current range", product(p1, j0, p1), mul(j0, p1))
    reject("left compression current differs from right current", fnorm(sub(lcp, j0)))
    reject("original C A do not commute", fnorm(sub(mul(c, a), mul(a, c))))

    def jet(t, label):
        left = f.frechet_exp(scale(1j*t, lc), scale(1j*t, lcp), tails, label+" free left")
        right = f.frechet_exp(scale(-1j*t, g), scale(-1j*t, j0), tails, label+" original right")
        jets = [left, (u, up), (q, contact), (r, rp), right]
        terms = [product(*[derivative if index == position else value for index, (value, derivative) in enumerate(jets)]) for position in range(5)]
        total = zero(n)
        for term in terms:
            total = add(total, term)
        return total, terms, jets

    def read_family(h, t):
        left, tail = b.exponential(scale(1j*t, add(lc, scale(h, lcp))))
        tails["FD left "+str((h, t))] = tail
        right, tail = b.exponential(scale(-1j*t, add(g, scale(h, j0))))
        tails["FD right "+str((h, t))] = tail
        green_left = b.inverse(add(add(lc, scale(h, lcp)), scale(-energy, eye)))
        green_right = b.inverse(add(add(g, scale(h, jenergy)), scale(-energy, eye)))
        return observed(product(left, green_left, add(q, scale(h, contact)), green_right, right))

    chosen = None
    for t in [-0.4, 0.0, 0.35, 0.8]:
        label = "t="+str(t)
        total, terms, jets = jet(t, label)
        slope = observed(total)
        equal(label+" explicit five terms equal product derivative", total, f.product_jet(*jets)[1])
        equal(label+" free left time remains unitary", product(adjoint(jets[0][0]), jets[0][0]), eye)
        bound(label+" free left compression slope price", fnorm(jets[0][1]), abs(t)*cpf)
        bound(label+" free left Green source price", fnorm(up), cpf/abs(energy.imag)**2)
        bg_slope = apply(jets[-1][1], background)
        equal(label+" original background slope remains N1", euclidean_difference(apply(p1, bg_slope), bg_slope), 0)
        p_one = 1+abs(t)*af
        bound(label+" original background N1 variation price", vnorm(bg_slope), abs(t)*jtf*p_one**2*vnorm(background))
        bound(label+" complete observed source degree five price", abs(slope), source_price*(1+abs(t))**5)
        step = 0.0005
        samples = [read_family(k*step, t) for k in [-2, -1, 1, 2]]
        finite_difference = (samples[0]-8*samples[1]+8*samples[2]-samples[3])/(12*step)
        equal(label+" complete constant force field derivative sanity", finite_difference, slope, 3e-9)
        if t == 0.35:
            chosen = total, terms, jets

    total, terms, jets = chosen
    response = observed(total)
    names = ["left time Cp", "left Green Cp", "reader contact", "right Green Jenergy", "right time J0"]
    for name, term in zip(names, terms):
        reject("omit "+name+" term", abs(observed(term)))
    reject("assume original background norm one", abs(response-observed(total, True)))
    wrong_green = scale(-1, product(r, lcp, r))
    altered = list(jets)
    altered[3] = (r, wrong_green)
    reject("replace right Green current by independent left Cp", abs(response-observed(f.product_jet(*altered)[1])))
    wrong_time = f.frechet_exp(scale(-1j*0.35, g), scale(-1j*0.35, lcp), tails, "wrong right time current")
    altered = list(jets)
    altered[-1] = wrong_time
    reject("replace right time current by independent left Cp", abs(response-observed(f.product_jet(*altered)[1])))
    reject("whole generator falsely treated as unitary", abs(vnorm(apply(jets[-1][0], created))-1))
    reject("discard complete reader operator", abs(response-observed(f.product_jet(jets[0], jets[1], (eye, contact), jets[3], jets[4])[1])))

    # Same positive window: only numerical quadrature, with no infinite-tail inference.
    window, intervals, lam = 0.6, 16, 0.8+0.2j
    times = [window*i/intervals for i in range(intervals+1)]
    slopes = [observed(jet(t, "window "+str(i))[0]) for i, t in enumerate(times)]
    weights = [1]+[4 if i % 2 else 2 for i in range(1, intervals)]+[1]
    pi_window = window*sum(weight*cmath.exp(-lam*t)*slope for weight, t, slope in zip(weights, times, slopes))/(3*intervals)
    window_majorant = window*sum(weight*math.exp(-lam.real*t)*source_price*(1+t)**5 for weight, t in zip(weights, times))/(3*intervals)
    bound("same window damped response respects sampled polynomial price", abs(pi_window), window_majorant)
    reject("extra division by lambda changes actual window read", abs(pi_window-pi_window/lam))

    gamma_zero, gamma_fifth = math.factorial(0), math.factorial(5)
    generated_constant = 2**5*(gamma_zero+gamma_fifth)
    equal("3872 generated from Gamma zero and fifth moments", generated_constant, 3872)

    def scaled_polynomial_laplace(sigma):
        # sigma^6 times the factorial moment expansion for (1+t)^5.
        return sum(math.comb(5, k)*math.factorial(k)*sigma**(5-k) for k in range(6))

    for sigma in [1.0, 0.5, 0.125, 0.03125]:
        value = scaled_polynomial_laplace(sigma)
        gamma_bound = 32*(sigma**5*gamma_zero+gamma_fifth)
        bound("sigma="+str(sigma)+" degree five Laplace moment majorant", value, gamma_bound)
        bound("sigma="+str(sigma)+" sixth order complete source damping price", source_price*value, generated_constant*source_price)

    # Finite Laurent construction: operator order 2m can exceed observed order six.
    # Background scaling is retained in the leading matrix killed by this observer.
    sigmas = [0.5, 0.25, 0.125, 0.0625]
    leading, read_coefficient = [[bg2, 0j], [0j, 1]], [[0j, 0j], [0j, 1/bg2]]
    pair_observer = lambda matrix: -matrix[0][0]+bg2*matrix[1][1]
    equal("complete observer cancels nonzero operator leading coefficient", pair_observer(leading), 0)
    trends = {}
    for m in [4, 5]:
        values = []
        for sigma in sigmas:
            # Build the regular object directly to avoid subtractive pole cancellation.
            pi_value = scaled_polynomial_laplace(sigma)/sigma**6
            regular = add(leading, scale(sigma**(2*m)*pi_value, read_coefficient))
            observed_regular = pair_observer(regular)
            expected = sigma**(2*m-6)*scaled_polynomial_laplace(sigma)
            equal("m="+str(m)+" sigma="+str(sigma)+" actual regular observer read", observed_regular, expected)
            bound("m="+str(m)+" sigma="+str(sigma)+" squeeze envelope", abs(observed_regular), generated_constant*sigma**(2*m-6))
            values.append(abs(observed_regular))
        equal("m="+str(m)+" finite approach is strictly decreasing", all(x>y for x, y in zip(values, values[1:])), True)
        trends[str(m)] = values
    reject("incorrectly extend high order cancellation to m equals three", scaled_polynomial_laplace(sigmas[-1]))

    return {"status": "pass" if not failures else "fail", "positive_count": len(positive), "negative_count": len(negative),
            "positive_checks": positive, "negative_checks": negative, "price_checks": bounds, "failures": failures,
            "scope": "finite sanity for independent left free jets, original N1 variation and complete fifth degree source price; finite Laurent trend only",
            "current_semantics": "Jenergy and J0 are source equal because -z*1 is field constant; they are consumed at their separate Green/time positions; left Cp remains independent",
            "norm_semantics": "vectors use Euclidean 2 norm; Frobenius explicitly upper bounds induced operator 2 norms; free left unitary factor uses bound one",
            "source_price": {"kernel_upper_bound": kernel_price, "complete_upper_bound": source_price, "original_background_norm_squared": bg2,
                             "four_price": four_price, "form": "K*(1+abs(t))^5", "degree": 5},
            "Laplace_moment_controls": {"Gamma_zero": gamma_zero, "Gamma_fifth": gamma_fifth, "generated_constant": generated_constant,
                                        "scope": "finite evaluations of source factorial-moment algebra; no inference from window truncation to infinite integral"},
            "window_sanity": {"length": window, "Simpson_intervals": intervals, "lambda": {"real": lam.real, "imag": lam.imag},
                              "read": {"real": pi_window.real, "imag": pi_window.imag}, "extra_normalization": False},
            "high_order_scope_sanity": {"m": [4, 5], "sigma_samples": sigmas, "observed_regular_values": trends,
                                       "construction": "regular source operator = nonzero observer-annihilated leading matrix + sigma^(2m) times fifth-degree Laplace read coefficient",
                                       "scope": "finite trends do not prove an infinite limit or identify an observed minimal order"},
            "series": {"terms_through": 80, "tail_bounds": tails, "scope": "exact exponential series tails; numerical roundoff separate"},
            "experimental_inputs_consumed": False,
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


def euclidean_difference(x, y):
    return vnorm([a-b for a, b in zip(x, y)])


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
