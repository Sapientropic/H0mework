"""Focused finite controls for the all-field right-time prefix producer.

Dyson words are computed by a layer generator, independently of the full-time
generator. Derivatives use augmented block Frechet exponentials. Finite
differences are numerical sanity, not proofs or physical error intervals.
"""
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys


sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = next(path for path in HERE.parents if (path / "Lean/lean-toolchain").is_file())
HELPER_DIR = ROOT / "Verification/physics/low-energy-phenomenology/alpha-source/em-identification"
FIELD_HELPER = HELPER_DIR / "check_actual_dressed_number_field.py"
ZERO_HELPER = HELPER_DIR / "check_actual_dressed_number_zero.py"


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


field = load(FIELD_HELPER, "field_control")
base = load(ZERO_HELPER, "zero_control")
zero, add, scale, mul, norm = base.zero, base.add, base.scale, base.mul, base.norm
product, product_jet, sub = field.product, field.product_jet, field.sub
SOURCE_SHA256 = {
    "ActualDressedFieldTimeFull": "d27a64bfb087fd4f8d5a362fcb7699850cb4114a6ae2c10fca83f3b2800e7dbf",
    "ActualDressedFieldTimeSector": "7a8e2c6885f8a8b35f457f1b351bf0bb47bbf7eca74286e8cc30a2b20310135a",
    "ActualDressedFieldTimeConsumer": "35722b7c1d2ec30b56b64d0e681299b3a0a424bdf6f6686fd9a20eed00c5386b",
}


def adjoint(matrix):
    return [[matrix[j][i].conjugate() for j in range(len(matrix))] for i in range(len(matrix))]


def prefix_jet(c, cp, a, ap, age, count, tails, label):
    n = len(c)
    generator, slope = zero(count*n), zero(count*n)
    for layer in range(count):
        for i in range(n):
            for j in range(n):
                generator[layer*n+i][layer*n+j] = -1j*age*c[i][j]
                slope[layer*n+i][layer*n+j] = -1j*age*cp[i][j]
                if layer:
                    generator[layer*n+i][(layer-1)*n+j] = -1j*age*a[i][j]
                    slope[layer*n+i][(layer-1)*n+j] = -1j*age*ap[i][j]
    exp, derivative = field.frechet_exp(generator, slope, tails, label)
    value, direction = zero(n), zero(n)
    for layer in range(count):
        value = add(value, [row[:n] for row in exp[layer*n:(layer+1)*n]])
        direction = add(direction, [row[:n] for row in derivative[layer*n:(layer+1)*n]])
    return value, direction


def run():
    positive, negative, failures, tails = {}, {}, [], {}
    tolerance, fd_tolerance, minimum_gap = 2e-11, 3e-9, 1e-7

    def check(name, left, right, limit=tolerance):
        error = norm(sub(left, right)) if isinstance(left, list) else abs(left-right)
        passed = math.isfinite(error) and error <= limit
        positive[name] = {"error": error, "tolerance": limit, "pass": passed}
        if not passed:
            failures.append(name)

    def reject(name, left, right):
        gap = norm(sub(left, right)) if isinstance(left, list) else abs(left-right)
        passed = math.isfinite(gap) and gap > minimum_gap
        negative[name] = {"difference": gap, "threshold": minimum_gap, "pass": passed}
        if not passed:
            failures.append(name)

    source_hashes = {}
    for name, expected in SOURCE_SHA256.items():
        path = HERE / (name+".lean")
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        source_hashes[str(path.relative_to(ROOT))] = digest
        if digest != expected:
            failures.append("fixed source hash mismatch "+name)

    n, energy, age = 10, 0.31+0.79j, 0.37
    p1, p2 = zero(n), zero(n)
    for i in range(4):
        p1[i][i] = 1
    for i in range(4, n):
        p2[i][i] = 1
    created, background = [0j]*n, [0j]*n
    created[4], created[5] = 1/math.sqrt(2), 1j/math.sqrt(2)
    background[0], background[1] = 1.7-0.2j, 0.6+0.4j

    def read(matrix, vector):
        return base.inner(vector, base.apply(matrix, vector))

    def observer(created_matrix, background_matrix):
        return -read(created_matrix, created)+read(background_matrix, background)

    check("unchanged creation has unit norm", base.inner(created, created), 1)
    data = field.family()
    check("base C at zero is Hermitian", data[0], adjoint(data[0]))
    nonselfadjoint = list(field.family())
    # This preserves every grade block while removing self-adjointness for h!=0.
    for i in range(n):
        nonselfadjoint[1][i][i] += 0.23j*(i+1)/n
    nonselfadjoint = tuple(nonselfadjoint)

    def evaluate(h, family, label):
        full = field.evaluate(h, family, energy, age, tails, label)
        three, tail = base.prefixes(full["c"], full["a"], age, 3)
        tails[label+" three prefix"] = tail
        two, tail = base.prefixes(full["c"], full["a"], age, 2)
        tails[label+" two prefix"] = tail
        full["three"], full["two"] = three, two
        full["timefinite2"] = product(full["lct"], full["lu"], full["q"], full["w2"], three)
        full["timefinite1"] = product(full["lct"], full["lu"], full["q"], full["w1"], two)
        return full

    for name, family, samples in [("Hermitian field", data, [-0.02, 0.0, 0.02]),
                                   ("nonselfadjoint field", nonselfadjoint, [-0.02, 0.02])]:
        for h in samples:
            label = name+" h="+str(h)
            v = evaluate(h, family, label)
            if name == "nonselfadjoint field":
                reject(label+" C is not selfadjoint", v["c"], adjoint(v["c"]))
            check(label+" N2 entire projection time return", mul(v["t"], p2), mul(v["three"], p2))
            check(label+" N1 entire projection time return", mul(v["t"], p1), mul(v["two"], p1))
            check(label+" unchanged unit Noether read", read(v["finite2"], created), read(v["timefinite2"], created))
            check(label+" original background Noether read", read(v["finite1"], background), read(v["timefinite1"], background))
            check(label+" full original fivefactor Noether read", observer(v["full"], v["full"]), observer(v["timefinite2"], v["timefinite1"]))

    v = evaluate(0, data, "direction base")
    c, cp, a, ap, lc, lcp, la, lap, q, qp = data
    original_time = field.frechet_exp(scale(-1j*age, add(c, a)), scale(-1j*age, add(cp, ap)), tails, "original time Frechet")
    three_jet = prefix_jet(c, cp, a, ap, age, 3, tails, "N2 three prefix Frechet")
    two_jet = prefix_jet(c, cp, a, ap, age, 2, tails, "N1 two prefix Frechet")
    check("N2 prefix jet value agrees with independent prefixes helper", three_jet[0], v["three"])
    check("N1 prefix jet value agrees with independent prefixes helper", two_jet[0], v["two"])
    check("N2 projection prefix direction equals full timeSlope", mul(three_jet[1], p2), mul(original_time[1], p2))
    check("N1 projection prefix direction equals full timeSlope", mul(two_jet[1], p1), mul(original_time[1], p1))

    left_time = field.frechet_exp(scale(1j*age, add(lc, la)), scale(1j*age, add(lcp, lap)), tails, "full left Frechet")
    left_c_time = field.frechet_exp(scale(1j*age, lc), scale(1j*age, lcp), tails, "left C Frechet")
    lr, r, lu = v["lr"], v["r"], v["lu"]
    lrp = scale(-1, product(lr, add(lcp, lap), lr))
    rp = scale(-1, product(r, add(cp, ap), r))
    lup = scale(-1, product(lu, lcp, lu))
    w2, w1 = field.green_jet(c, cp, a, ap, energy, 3), field.green_jet(c, cp, a, ap, energy, 2)
    original_jet = product_jet(left_time, (lr, lrp), (q, qp), (r, rp), original_time)
    finite2_jet = product_jet(left_c_time, (lu, lup), (q, qp), w2, three_jet)
    finite1_jet = product_jet(left_c_time, (lu, lup), (q, qp), w1, two_jet)
    full_derivative = observer(original_jet[1], original_jet[1])
    finite_derivative = observer(finite2_jet[1], finite1_jet[1])
    check("created complete finite-time fivefactor derivative", read(original_jet[1], created), read(finite2_jet[1], created))
    check("background complete finite-time fivefactor derivative", read(original_jet[1], background), read(finite1_jet[1], background))
    check("complete finite-time Noether derivative", full_derivative, finite_derivative)

    # Each forbidden simplification must alter a nonzero actual read or sector map.
    reject("delete N2 second Dyson prefix on full projection", mul(v["three"], p2), mul(v["two"], p2))
    wrong_created = product(v["lct"], lu, q, v["w2"], v["two"])
    reject("delete N2 second Dyson prefix in complete read", observer(v["timefinite2"], v["timefinite1"]), observer(wrong_created, v["timefinite1"]))
    free_time, tail = base.exponential(scale(-1j*age, c))
    tails["free time negative control"] = tail
    wrong_background = product(v["lct"], lu, q, v["w1"], free_time)
    reject("delete N1 first Dyson correction in complete read", observer(v["timefinite2"], v["timefinite1"]), observer(v["timefinite2"], wrong_background))
    raise_time, tail = base.exponential(scale(-1j*age, a))
    tails["raising time negative control"] = tail
    reject("incorrect commuting C A exponential factorization", mul(v["t"], p2), product(free_time, raise_time, p2))
    reject("erase complex phase of complete finite-time derivative", finite_derivative, finite_derivative.real)
    block_reader = [[q[i][j] if i//2 == j//2 else 0j for j in range(n)] for i in range(n)]
    wrong_created = product(v["lct"], lu, block_reader, v["w2"], v["three"])
    wrong_background = product(v["lct"], lu, block_reader, v["w1"], v["two"])
    reject("incorrect block diagonal raw reader", observer(v["timefinite2"], v["timefinite1"]), observer(wrong_created, wrong_background))
    without_direction2 = product_jet(left_c_time, (lu, lup), (q, qp), w2, (three_jet[0], zero(n)))[1]
    without_direction1 = product_jet(left_c_time, (lu, lup), (q, qp), w1, (two_jet[0], zero(n)))[1]
    reject("erase original right timeSlope in finite-time derivative", finite_derivative, observer(without_direction2, without_direction1))

    for step in [0.001, 0.0005]:
        samples = [evaluate(k*step, data, "FD "+str(k*step)) for k in [-2, -1, 1, 2]]
        scalar = [observer(sample["timefinite2"], sample["timefinite1"]) for sample in samples]
        fd = (scalar[0]-8*scalar[1]+8*scalar[2]-scalar[3])/(12*step)
        check("finite-time Noether five point sanity s="+str(step), fd, full_derivative, fd_tolerance)
        for key, projection, derivative in [("three", p2, original_time[1]), ("two", p1, original_time[1])]:
            fd = scale(1/(12*step), add(sub(samples[0][key], scale(8, samples[1][key])), sub(scale(8, samples[2][key]), samples[3][key])))
            check(key+" prefix direction five point sanity s="+str(step), mul(fd, projection), mul(derivative, projection), fd_tolerance)

    helpers = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in [FIELD_HELPER, ZERO_HELPER]}
    return {"status": "pass" if not failures else "fail", "positive_count": len(positive), "negative_count": len(negative),
            "positive_checks": positive, "negative_checks": negative, "failures": failures,
            "scope": "independent finite noncommuting right-time prefix controls; no promotion, physical prediction or Lean proof",
            "source_sha256": source_hashes, "expected_source_sha256": SOURCE_SHA256,
            "helper_sha256": helpers, "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "parameters": {"dimension": n, "age": age, "energy": {"real": energy.real, "imag": energy.imag},
                           "Hermitian_field_samples": [-0.02, 0.0, 0.02], "nonselfadjoint_field_samples": [-0.02, 0.02],
                           "created_norm_squared": base.inner(created, created).real, "original_background_norm_squared": base.inner(background, background).real,
                           "states_fixed_across_field": True, "reader_all_entries_retained": True},
            "series": {"terms_through": 80, "tail_formula": "exp(norm(X))*norm(X)^81/81! in infinity operator norm",
                       "tail_limit": 1e-25, "tail_bounds": tails, "scope": "exact-series truncation only, excluding roundoff and physical error"},
            "response_derivative": {"real": full_derivative.real, "imag": full_derivative.imag},
            "finite_difference": {"formula": "(f(-2s)-8f(-s)+8f(s)-f(2s))/(12s)", "order": 4,
                                  "steps": [0.001, 0.0005], "absolute_tolerance": fd_tolerance,
                                  "role": "numerical sanity, not an asserted analytic remainder bound"}}


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
