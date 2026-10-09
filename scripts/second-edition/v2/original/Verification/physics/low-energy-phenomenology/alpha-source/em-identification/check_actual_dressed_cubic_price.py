"""Finite cubic tail-budget and complete observation-price controls.

This uses a small source-shaped noncommuting matrix family, not actual 289
numerical data. Price norms are Euclidean/Frobenius operator upper bounds.
Quadrature and factorial-moment evaluations are finite sanity, not Lean proofs,
infinite-limit proofs or physical predictions.
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


f, b = load("check_actual_dressed_number_field"), load("check_actual_dressed_number_zero")
zero, add, scale, mul, apply = b.zero, b.add, b.scale, b.mul, b.apply
product, sub = f.product, f.sub


def vnorm(v):
    return math.sqrt(sum(abs(x)**2 for x in v))


def fnorm(matrix):
    return vnorm([x for row in matrix for x in row])


def vsub(x, y):
    return [a-b for a, b in zip(x, y)]


def run():
    positive, negative, failures, prices, tails = {}, {}, [], {}, {}

    def check(name, error, tolerance=2e-10):
        passed = math.isfinite(error) and error <= tolerance
        positive[name] = {"error": error, "tolerance": tolerance, "pass": passed}
        if not passed:
            failures.append(name)

    def bound(name, value, price):
        check(name, max(0, value-price), 2e-10*max(1, price))
        prices[name] = {"observed": value, "upper_bound": price}

    def reject(name, gap):
        passed = math.isfinite(gap) and gap > 1e-7
        negative[name] = {"difference": gap, "threshold": 1e-7, "pass": passed}
        if not passed:
            failures.append(name)

    c, cp, a, ap, lc, lcp, _, _, reader, contact = f.family()
    n, energy = len(c), 0.31+0.79j
    g, current = add(c, a), add(cp, ap)
    af, jf = fnorm(a), fnorm(current)
    p, q, rflag, n1 = zero(n), zero(n), zero(n), zero(n)
    for i in range(4, n):
        p[i][i] = 1
    for i in range(6, n):
        q[i][i] = 1
    for i in range(8, n):
        rflag[i][i] = 1
    for i in range(4):
        n1[i][i] = 1
    created, background, mixed = [0j]*n, [0j]*n, [0j]*n
    created[4], created[5] = 1/math.sqrt(2), 1j/math.sqrt(2)
    background[0], background[1] = 1.7-0.2j, 0.6+0.4j
    mixed[4], mixed[6], mixed[8] = 1.2+0.3j, -0.6+0.4j, 0.8-0.2j
    bg2 = vnorm(background)**2
    for h in [-0.02, 0.0, 0.02]:
        ch, ah = add(c, scale(h, cp)), add(a, scale(h, ap))
        gh = sub(add(ch, ah), scale(energy, b.identity(n)))
        check("h="+str(h)+" Y takes N2 into first upper tail", fnorm(sub(product(q, ah, p), mul(ah, p))))
        check("h="+str(h)+" Y takes first into terminal upper tail", fnorm(sub(product(rflag, ah, q), mul(ah, q))))
        for label, flag in [("first", q), ("terminal", rflag)]:
            check("h="+str(h)+" generator preserves "+label+" tail", fnorm(sub(product(flag, gh, flag), mul(gh, flag))))
    for label, flag in [("whole N2", p), ("first upper", q), ("terminal upper", rflag)]:
        check("full field current preserves "+label+" tail", fnorm(sub(product(flag, current, flag), mul(current, flag))))

    def time(t, generator=g):
        value, tail = b.exponential(scale(-1j*t, generator))
        tails[str(t)+" generator="+("original" if generator is g else "free")] = tail
        return value

    def prefix_words(t):
        free, tail0 = b.prefixes(c, a, t, 1)
        first, tail1 = b.prefixes(c, a, t, 2)
        second, tail2 = b.prefixes(c, a, t, 3)
        tails["prefix blocks "+str(t)] = max(tail0, tail1, tail2)
        return free, sub(first, free), sub(second, first)

    left_green = b.inverse(sub(lc, scale(energy, b.identity(n))))
    right_green = b.inverse(sub(g, scale(energy, b.identity(n))))
    left_slope = scale(-1, product(left_green, lcp, left_green))
    right_slope = scale(-1, product(right_green, current, right_green))
    left_cp, lb, rq, rd = fnorm(lcp), fnorm(left_green), fnorm(reader), fnorm(right_green)
    four = left_cp*lb*rq*rd+lb**2*left_cp*rq*rd+lb*fnorm(contact)*rd+lb*rq*rd**2*jf
    kernel_price = four*(1+af)**2+lb*rq*rd*(3*jf*(1+af)**2)
    k3 = kernel_price*(1+bg2)

    def observe(matrix, normalize_background=False):
        return -b.inner(created, apply(matrix, created))+b.inner(background, apply(matrix, background))/(bg2 if normalize_background else 1)

    chosen, ordered = None, {}
    for t in [-0.6, -0.0001, 0.0, 0.0001, 0.4, 0.85]:
        label, x = "t="+str(t), abs(t)*af
        right = f.frechet_exp(scale(-1j*t, g), scale(-1j*t, current), tails, label+" original slope")
        words = prefix_words(t)
        check(label+" prefix one has its actual first tail", fnorm(sub(product(q, words[1], p), mul(words[1], p))))
        check(label+" prefix two has its actual terminal tail", fnorm(sub(product(rflag, words[2], p), mul(words[2], p))))
        ordered_one = product(words[1], time(-t, c))
        check(label+" original ordered one advances first to terminal tail", fnorm(sub(product(rflag, ordered_one, q), mul(ordered_one, q))))
        for name, vector in [("created norm one", created), ("mixed whole N2", mixed)]:
            slope_norm = vnorm(apply(right[1], vector))
            bound(label+" "+name+" exact cubic variation budget", slope_norm, abs(t)*jf*(1+2*x+3*x*x)*vnorm(vector))
            bound(label+" "+name+" common cubic growth", slope_norm, 3*jf*(1+af)**2*vnorm(vector)*(1+abs(t))**3)
        bg_slope = apply(right[1], background)
        check(label+" original background slope stays N1", vnorm(vsub(apply(n1, bg_slope), bg_slope)))
        bound(label+" original N1 price retained", vnorm(bg_slope), abs(t)*jf*(1+x)**2*vnorm(background))
        bound(label+" original N1 common cubic growth", vnorm(bg_slope), 3*jf*(1+af)**2*vnorm(background)*(1+abs(t))**3)
        left = f.frechet_exp(scale(1j*t, lc), scale(1j*t, lcp), tails, label+" left compression slope")
        jets = [left, (left_green, left_slope), (reader, contact), (right_green, right_slope), right]
        full_derivative = f.product_jet(*jets)[1]
        bound(label+" complete original fivefactor cubic price", abs(observe(full_derivative)), k3*(1+abs(t))**3)
        if t in [-0.6, 0.4]:
            samples, decomposition_errors = [], []
            for i in range(33):
                s = t*i/32
                inner_words = prefix_words(t-s)
                pieces = [product(time(s), scale(-1j, current), word, p) for word in inner_words]
                direct = product(time(s), scale(-1j, current), time(t-s), p)
                decomposition_errors.append(fnorm(sub(direct, add(add(pieces[0], pieces[1]), pieces[2]))))
                samples.append(direct)
            weights = [1]+[4 if i % 2 else 2 for i in range(1, 32)]+[1]
            integral = zero(n)
            for weight, sample in zip(weights, samples):
                integral = add(integral, scale(weight*t/96, sample))
            check(label+" ordered prefix decomposition", max(decomposition_errors))
            check(label+" full ordered variation matches original Frechet", fnorm(sub(integral, mul(right[1], p))), 2e-8)
            ordered[label] = fnorm(sub(integral, mul(right[1], p)))
        if t == 0.4:
            chosen = t, x, jets, full_derivative

    t, x, jets, derivative = chosen
    s, tau = 0.37*t, 0.63*t
    words = prefix_words(tau)
    pieces = [product(time(s), scale(-1j, current), word, p) for word in words]
    for i, factor in enumerate([1+x+x*x, (1+x)*x, x*x]):
        bound("tail "+str(i)+" uses its correct left time budget", vnorm(apply(pieces[i], mixed)), jf*factor*vnorm(mixed))
    check("terminal prefix uses genuinely free left time", fnorm(sub(pieces[2], product(time(s, c), scale(-1j, current), words[2], p))))
    reject("omit terminal prefix contribution changes ordered variation", fnorm(pieces[2]))
    reject("wrongly give first prefix terminal free left budget", fnorm(sub(pieces[1], product(time(s, c), scale(-1j, current), words[1], p))))
    check("tail sum generates one plus two x plus three x squared", abs((1+x+x*x)+(1+x)*x+x*x-(1+2*x+3*x*x)))
    lowering = [row[:] for row in current]
    lowering[4][6], lowering[4][8] = 0.45+0.2j, 0.35+0.2j
    reject("lowering current breaks first upper tail condition", fnorm(sub(product(q, lowering, q), mul(lowering, q))))
    reject("lowering current breaks terminal upper tail condition", fnorm(sub(product(rflag, lowering, rflag), mul(lowering, rflag))))
    bad_slope = f.frechet_exp(scale(-1j*t, g), scale(-1j*t, lowering), tails, "lowering current slope")
    reject("lowering current changes actual whole N2 variation", fnorm(sub(mul(bad_slope[1], p), mul(jets[-1][1], p))))
    reject("whole original generator is not unitary", abs(vnorm(apply(jets[-1][0], created))-1))
    reject("original background cannot be treated as norm one", abs(observe(derivative)-observe(derivative, True)))
    for position, name in enumerate(["left time Cp", "left Green Cp", "reader contact", "right Green full J", "right time full J"]):
        term = product(*[slope if i == position else value for i, (value, slope) in enumerate(jets)])
        reject("omit "+name+" changes complete response", abs(observe(term)))
    wrong_jets = list(jets)
    wrong_jets[3] = (right_green, scale(-1, product(right_green, lcp, right_green)))
    reject("swap right full current for independent left Cp", abs(observe(derivative)-observe(f.product_jet(*wrong_jets)[1])))
    lam = 0.8+0.2j
    reject("extra lambda normalization changes original response", abs(observe(derivative)-observe(derivative)/lam))

    gamma0, gamma3 = math.factorial(0), math.factorial(3)
    generated = 2**3*(gamma0+gamma3)
    check("56 generated from Gamma zero and third moments", abs(generated-56))
    moment_prices = {}
    for sigma in [1.0, 0.5, 0.125, 0.03125]:
        normalized = sum(math.comb(3, k)*math.factorial(k)*sigma**(3-k) for k in range(4))
        majorant = 8*(sigma**3+gamma3)
        bound("sigma="+str(sigma)+" cubic Laplace moment price", normalized, majorant)
        bound("sigma="+str(sigma)+" complete fourth order source price", k3*normalized, generated*k3)
        moment_prices[str(sigma)] = normalized
    reject("fourth damping bound does not make unscaled Pi finite", moment_prices["0.03125"]/(0.03125**4)-moment_prices["0.125"]/(0.125**4))
    # The lower-degree response 1+t satisfies the cubic bound and has pole order two.
    sigma = 0.03125
    lower_pi = 1/sigma+1/sigma**2
    reject("cubic price does not assert exact fourth pole order", abs(sigma**4*lower_pi-sigma**2*lower_pi))

    return {"status": "pass" if not failures else "fail", "positive_count": len(positive), "negative_count": len(negative),
            "positive_checks": positive, "negative_checks": negative, "price_checks": prices, "failures": failures,
            "scope": "finite small source-shaped matrix controls for cubic graded variation and complete constant-force observation value; no actual 289 numerical or infinite-limit claim",
            "source_price": {"complete_K3_upper_bound": k3, "background_norm_squared": bg2, "form": "K3*(1+abs(t))^3",
                             "norms": "Euclidean vectors, Frobenius upper bounds for induced operator 2 norms"},
            "tail_mechanism": {"prefix_i_ranges": ["whole N2", "upperOne", "upperTwo"], "left_prices": ["1+x+x^2", "1+x", "1"],
                               "sum": "1+2x+3x^2", "lowering_negative_scope": "tail hypotheses and actual operator differences; no claimed violation of a loose numerical price"},
            "ordered_variation_sanity": {"Simpson_intervals": 32, "errors": ordered, "role": "numerical sanity only"},
            "Gamma_moment_sanity": {"Gamma0": gamma0, "Gamma3": gamma3, "generated_constant": generated, "sigma4_polynomial_moments": moment_prices},
            "series": {"terms_through": 80, "helper_augmented_exponential_tail_bounds": tails},
            "response_scope": "original value component only; source price is not unscaled Pi finiteness, exact pole order, or alpha identification",
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
