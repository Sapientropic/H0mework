"""Finite noncommuting halfline Green/Schur sanity, with all nine null rows.

The 12-dimensional fixture is a mathematical model, not actual 289-entry data.
The kernel's elementary halfline transform is explicit. Finite windows check
the same event; they do not prove actual small-sigma regular membership.
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
path = ROOT / "Verification/physics/low-energy-phenomenology/alpha-source/em-identification/check_actual_dressed_number_zero.py"
spec = importlib.util.spec_from_file_location("finite_matrix_helpers", path)
b = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b)
zero, eye, add, scale, mul, apply, inverse = b.zero, b.identity, b.add, b.scale, b.mul, b.apply, b.inverse


def sub(a, b):
    return add(a, scale(-1, b))


def vadd(x, y):
    return [a+b for a, b in zip(x, y)]


def vsub(x, y):
    return [a-b for a, b in zip(x, y)]


def vscale(c, v):
    return [c*x for x in v]


def norm(v):
    return math.sqrt(sum(abs(x)**2 for x in v))


def frobenius(a):
    return norm([x for row in a for x in row])


def product(*matrices):
    out = matrices[0]
    for matrix in matrices[1:]:
        out = mul(out, matrix)
    return out


def determinant(matrix):
    rows, value, n = [row[:] for row in matrix], 1+0j, len(matrix)
    for j in range(n):
        pivot = max(range(j, n), key=lambda i: abs(rows[i][j]))
        if abs(rows[pivot][j]) < 1e-13:
            return 0j
        if pivot != j:
            rows[j], rows[pivot] = rows[pivot], rows[j]
            value = -value
        denominator = rows[j][j]
        value *= denominator
        for i in range(j+1, n):
            coefficient = rows[i][j]/denominator
            for k in range(j+1, n):
                rows[i][k] -= coefficient*rows[j][k]
    return value


def run():
    positives, negatives, failures = {}, {}, []

    def equal(name, error, tolerance=2e-10):
        passed = math.isfinite(error) and error <= tolerance
        positives[name] = {"error": error, "tolerance": tolerance, "pass": passed}
        if not passed:
            failures.append(name)

    def reject(name, gap):
        passed = math.isfinite(gap) and gap > 1e-7
        negatives[name] = {"difference": gap, "threshold": 1e-7, "pass": passed}
        if not passed:
            failures.append(name)

    n, active, null_count = 12, 3, 9
    identity = eye(n)
    change, row_change = eye(n), eye(n)
    for i in range(n):
        change[i][(i+4) % n] += (0.03+0.01j)*(1+i % 3)
        row_change[i][(i+7) % n] += (-0.025+0.015j)*(1+i % 2)
    change_inv, row_inv = inverse(change), inverse(row_change)
    d, dp, null_base = zero(n), zero(n), zero(n)
    for i, value in enumerate([1.2+0.1j, 1.7-0.2j, 2.1+0.3j]):
        d[i][i], dp[i][i] = value, 1/value
    for i in range(active, n):
        null_base[i][i] = 1
    null_pad = [[1 if i == active+j else 0j for j in range(null_count)] for i in range(n)]
    null_read = [[1 if j == active+i else 0j for j in range(n)] for i in range(null_count)]
    jacobi = product(row_change, d, change_inv)
    green = product(change, dp, row_inv)
    null = product(change, null_base, change_inv)
    lift = mul(change, null_pad)
    coordinates = mul(null_read, change_inv)
    cokernel = mul(null_read, row_inv)
    compatibility = mul(null_pad, cokernel)
    rowlift = row_change
    equal("original Green Jacobi equals one minus original null", frobenius(sub(mul(green, jacobi), sub(identity, null))))
    equal("original Jacobi Green preserves complete compatible residual", frobenius(sub(mul(jacobi, green), sub(identity, mul(rowlift, compatibility)))))
    equal("original null projection", frobenius(sub(mul(null, null), null)))
    equal("original null Green vanishes", frobenius(mul(null, green)))
    equal("original Euler kills null lift", frobenius(mul(jacobi, lift)))
    equal("original nine null coordinates invert lift", frobenius(sub(mul(coordinates, lift), eye(null_count))))
    equal("original nine cokernel kills Euler", frobenius(mul(cokernel, jacobi)))
    reject("initial null coordinates cannot replace cokernel rows", frobenius(sub(coordinates, cokernel)))

    sigma, omega, decay = 0.7, 0.8, 1.1
    lam, p0 = sigma-1j*omega, 1j*omega
    normalizer = lam+p0
    equal("physical normalizer is sigma alone", abs(normalizer-sigma))
    kernel = zero(n)
    for i in range(n):
        kernel[i][i] = (0.09+0.004*i)+0.01j
        kernel[i][(i+1) % n] = (0.012+0.006j)*(1+i % 2)
        kernel[i][(i+5) % n] = -0.008+0.005j
    half_polarization = scale(1/(lam+decay), kernel)
    correction = scale(normalizer, half_polarization)
    feedback = sub(identity, mul(green, correction))
    resolvent = inverse(feedback)
    price = sum(abs(x) for row in mul(green, correction) for x in row)
    feedback_det = determinant(feedback)
    equal("actual entry sum gives sufficient small source price", max(0, price-1+1e-12))
    reject("actual feedback determinant is regular", abs(feedback_det))
    equal("canonical feedback inverse right identity", frobenius(sub(mul(feedback, resolvent), identity)))
    equal("canonical feedback inverse left identity", frobenius(sub(mul(resolvent, feedback), identity)))
    reject("finite source Green and halfline correction do not commute", frobenius(sub(mul(green, correction), mul(correction, green))))
    arbitrary_seed = [complex((2*i+1) % 7-3, (i+3) % 5-2)/5 for i in range(n)]
    fixed = apply(resolvent, arbitrary_seed)
    equal("canonical feedback fixed point", norm(vsub(fixed, vadd(arbitrary_seed, apply(green, apply(correction, fixed))))))

    forcing = [complex((3*i+2) % 11-4, (i+2) % 7-3)/7 for i in range(n)]
    initial = [complex(i+1, 2-i)/13 for i in range(null_count)]
    pencil = sub(jacobi, correction)

    def response(force, start, inverse_feedback=resolvent):
        return apply(inverse_feedback, vadd(apply(green, force), apply(lift, start)))

    def schur_source(force):
        return vscale(-1, apply(cokernel, vadd(force, apply(correction, apply(resolvent, apply(green, force))))))

    schur = product(cokernel, correction, resolvent, lift)
    rhs = schur_source(forcing)
    raw_response = response(forcing, initial)
    effective_forcing = vadd(forcing, apply(correction, raw_response))
    row_residual = apply(cokernel, effective_forcing)
    equal("half response retains original null initial data", norm(vsub(apply(null, raw_response), apply(lift, initial))))
    equal("complete half response generated fixed point", norm(vsub(raw_response, vadd(apply(lift, initial), apply(green, effective_forcing)))))
    equal("all nine Schur rows equal complete cokernel residual", norm(vsub(row_residual, vsub(apply(schur, initial), rhs))))
    equal("original Euler residual retains rowlift compatible residual", norm(vsub(apply(pencil, raw_response), vsub(forcing, apply(rowlift, apply(compatibility, effective_forcing))))))
    reject("arbitrary source forcing is not already compatible", norm(apply(cokernel, forcing)))
    reject("ignoring complete nine row residual changes Euler equation", norm(vsub(apply(pencil, raw_response), forcing)))

    generated_initial = apply(inverse(schur), rhs)
    solution = response(forcing, generated_initial)
    equal("Schur response solves complete original Pencil", norm(vsub(apply(pencil, solution), forcing)))
    equal("full Pencil inverse matches response plus Schur", norm(vsub(solution, apply(inverse(pencil), forcing))))
    equal("original initial coordinates restore same full solution", norm(vsub(apply(coordinates, solution), generated_initial)))
    generated_forcing = apply(pencil, arbitrary_seed)
    restored = response(generated_forcing, apply(coordinates, arbitrary_seed))
    equal("every complete solution restores from its forcing and null coordinates", norm(vsub(restored, arbitrary_seed)))
    equal("every complete solution satisfies its Schur equation", norm(vsub(apply(schur, apply(coordinates, arbitrary_seed)), schur_source(generated_forcing))))

    bare = vadd(apply(green, forcing), apply(lift, generated_initial))
    reject("drop halfline correction back to bare Green response", norm(vsub(solution, bare)))
    no_initial = response(forcing, [0j]*null_count)
    reject("drop original null initial data", norm(vsub(solution, no_initial)))
    last_row = [0j]*null_count
    last_row[-1] = 0.4-0.1j
    wrong_initial = apply(inverse(schur), vadd(rhs, last_row))
    wrong_response = response(forcing, wrong_initial)
    wrong_rows = vsub(apply(schur, wrong_initial), rhs)
    equal("first eight rows alone pass the deliberately incomplete check", norm(wrong_rows[:-1]))
    reject("omit ninth original row loses genuine compatible residual", norm(vsub(apply(pencil, wrong_response), forcing)))
    projected_forcing = vsub(forcing, apply(rowlift, apply(compatibility, forcing)))
    projected_initial = apply(inverse(schur), schur_source(projected_forcing))
    reject("hard project source forcing to compatibility changes response", norm(vsub(solution, response(projected_forcing, projected_initial))))

    wrong_q = scale(lam, half_polarization)
    wrong_inv = inverse(sub(identity, mul(green, wrong_q)))
    reject("use lambda instead of physical sigma changes response", norm(vsub(raw_response, response(forcing, initial, wrong_inv))))
    twice_q = scale(1/lam, correction)
    twice_inv = inverse(sub(identity, mul(green, twice_q)))
    reject("extra division by lambda changes halfline response", norm(vsub(raw_response, response(forcing, initial, twice_inv))))
    anchor_kernel = scale(0.63, kernel)
    anchor_q = scale(normalizer/(lam+decay), anchor_kernel)
    anchor_inv = inverse(sub(identity, mul(green, anchor_q)))
    reject("replace event by anchor changes the complete response", norm(vsub(raw_response, response(forcing, initial, anchor_inv))))

    # A failed entry-sum condition is not a failed determinant condition.
    large_feedback = sub(identity, scale(2, mul(green, jacobi)))
    large_price = sum(abs(x) for row in scale(2, mul(green, jacobi)) for x in row)
    reject("sufficient entry sum condition need not hold for a regular inverse", large_price-1)
    equal("regular feedback beyond sufficient small price", frobenius(sub(mul(large_feedback, inverse(large_feedback)), identity)))
    singular_feedback = sub(identity, mul(green, jacobi))
    equal("determinant condition genuinely fails in singular fixture", abs(determinant(singular_feedback)))
    active_vector = apply(change, [1]+[0j]*(n-1))
    equal("singular feedback has nonzero active kernel", norm(apply(singular_feedback, active_vector)))
    reject("singular determinant cannot certify a claimed inverse", frobenius(sub(mul(singular_feedback, null), identity)))
    # Feedback regularity alone does not assert Schur uniqueness: Q=0 has nine free initials.
    equal("zero correction feedback is regular", abs(determinant(identity)-1))
    null_solution = apply(lift, initial)
    equal("zero correction has distinct homogeneous Pencil solutions", norm(apply(jacobi, null_solution)))
    reject("regular feedback does not erase singular Schur free initial data", norm(null_solution))

    windows, inverse_errors, determinant_values = [0.0, 0.5, 1.0, 2.0, 4.0, 8.0], [], []
    for time in windows:
        window_polarization = scale((1-cmath.exp(-(lam+decay)*time))/(lam+decay), kernel)
        window_q = scale(normalizer, window_polarization)
        window_feedback = sub(identity, mul(green, window_q))
        window_inverse = inverse(window_feedback)
        equal("same event window T="+str(time)+" inverse identity", frobenius(sub(mul(window_feedback, window_inverse), identity)))
        inverse_errors.append(frobenius(sub(window_inverse, resolvent)))
        determinant_values.append({"real": determinant(window_feedback).real, "imag": determinant(window_feedback).imag})
    equal("same event finite window inverse errors decrease", 0 if all(x>y for x, y in zip(inverse_errors, inverse_errors[1:])) else 1)
    equal("same event final window inverse is close to halfline inverse", inverse_errors[-1], 2e-7)

    return {"status": "pass" if not failures else "fail", "positive_count": len(positives), "negative_count": len(negatives),
            "positive_checks": positives, "negative_checks": negatives, "failures": failures,
            "scope": "12 dimensional finite noncommuting model, 3 active and all 9 null/cokernel rows; not actual 289 numerical data or a Lean proof",
            "halfline_model": {"kernel": "exp(-decay*t)*same_event_kernel_matrix", "decay": decay,
                               "polarization": "kernel_matrix/(lambda+decay)", "correction": "sigma*polarization", "normalization_count": 1,
                               "sigma": sigma, "omega": omega, "lambda": {"real": lam.real, "imag": lam.imag}},
            "feedback": {"entry_sum_price": price, "determinant": {"real": feedback_det.real, "imag": feedback_det.imag},
                         "Schur_determinant": {"real": determinant(schur).real, "imag": determinant(schur).imag},
                         "scope": "explicit regular parameters only; no actual small sigma membership claim"},
            "window_sanity": {"same_event": True, "windows": windows, "inverse_errors": inverse_errors, "determinants": determinant_values,
                              "scope": "finite convergence trend for the explicit halfline kernel; no substitute event or anchor"},
            "uniqueness_scope": "canonical feedback inverse under feedback determinant; full response also requires complete nine-row Schur compatibility, and Schur uniqueness is separate",
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
