"""Generate and check rational extrema certificates for the complete regular fiber."""
from fractions import Fraction
from math import isqrt

from model import decode


GAP = Fraction(1, 100_000_000)
ROOT_BITS = 80


def sqrt_bracket(value, bits=ROOT_BITS):
    value = Fraction(value)
    if value < 0:
        raise ValueError("Nonnegative square root required")
    n, d = isqrt(value.numerator), isqrt(value.denominator)
    if n * n == value.numerator and d * d == value.denominator:
        return Fraction(n, d), Fraction(n, d)
    unit = 1 << bits
    lower = Fraction(isqrt((value.numerator << (2 * bits)) // value.denominator), unit)
    return lower, lower + Fraction(1, unit)


def geometry(primitive, side):
    point = decode(primitive)
    if side not in ("alice", "bob"):
        raise ValueError("One physical side required")
    other = "bob" if side == "alice" else "alice"
    def coefficients(effects):
        return [(e.u ** 2, e.z ** 2, (1 - abs(e.mu)) ** 2) for e in effects]
    upper = coefficients(getattr(point, side))
    reciprocal = coefficients(getattr(point, other))
    if any(value <= 0 for row in (*upper, *reciprocal) for value in row):
        raise ValueError("Strictly positive coefficients required by this regular-fiber producer")
    return upper, reciprocal


def feasible(upper, reciprocal, coordinates):
    s, t = coordinates
    return (s > 0 and t > 0 and all(a * s + b * t <= c for a, b, c in upper)
            and all(p / s + q / t <= d for p, q, d in reciprocal))


def check_endpoint(primitive, side, setting, kind, certificate):
    if type(setting) is not int or setting not in (0, 1) or kind not in ("minimum", "maximum"):
        raise ValueError("Gain endpoint role required")
    if set(certificate) != {"multipliers", "sqrt_lower", "primal_squared_scales"}:
        raise ValueError("Only a primitive rational primal/dual certificate is admitted")
    weights = certificate["multipliers"]
    if set(weights) != {"upper", "reciprocal"} or any(len(weights[key]) != 2 for key in weights):
        raise ValueError("Four dual multipliers required")
    theta, lam = (tuple(map(Fraction, weights[key])) for key in ("upper", "reciprocal"))
    if any(w < 0 for w in (*theta, *lam)):
        raise ValueError("Nonnegative dual multipliers required")
    if len(certificate["sqrt_lower"]) != 2 or len(certificate["primal_squared_scales"]) != 2:
        raise ValueError("Two scale coordinates and two root bounds required")
    upper, reciprocal = geometry(primitive, side)
    sigma = 1 if kind == "minimum" else -1
    a, b, _ = upper[setting]
    first = sigma * a + sum(w * row[0] for w, row in zip(theta, upper))
    second = sigma * b + sum(w * row[1] for w, row in zip(theta, upper))
    p = sum(w * row[0] for w, row in zip(lam, reciprocal))
    q = sum(w * row[1] for w, row in zip(lam, reciprocal))
    constant = sum(w * row[2] for w, row in zip(theta, upper)) + sum(w * row[2] for w, row in zip(lam, reciprocal))
    r, v = map(Fraction, certificate["sqrt_lower"])
    if min(first, second, p, q, r, v) < 0 or r * r > first * p or v * v > second * q:
        raise ValueError("Dual square-root lower bounds not certified")
    scales = tuple(map(Fraction, certificate["primal_squared_scales"]))
    if not feasible(upper, reciprocal, scales):
        raise ValueError("Near-attaining point is outside the complete source fiber")
    attained = a * scales[0] + b * scales[1]
    dual = 2 * (r + v) - constant
    gap = sigma * attained - dual
    if not 0 <= gap <= GAP:
        raise ValueError("Uniform bound and legal attainable value are not within the frozen gap")
    return {"gain_squared_bound": str(sigma * dual), "attained_gain_squared": str(attained),
            "optimality_gap": str(gap), "all_continuous_members_covered": True}


def propose(primitive, side, setting, kind):
    # Floating minimization proposes witnesses; exact cone and dual checks decide acceptance.
    import numpy as np
    from scipy.optimize import minimize, nnls
    upper, reciprocal = geometry(primitive, side)
    aa = np.array([[float(a), float(b)] for a, b, _ in upper])
    bb = np.array([[float(p), float(q)] for p, q, _ in reciprocal])
    cc = np.array([float(c) for _, _, c in upper])
    dd = np.array([float(d) for _, _, d in reciprocal])
    w = aa[setting]
    sigma = 1 if kind == "minimum" else -1
    def residual(x):
        return np.r_[cc - aa @ x, dd - bb @ (1 / x)]
    def gradient(x):
        return np.r_[-aa, bb / (x * x)]
    fit = minimize(lambda x: sigma * (w @ x), np.ones(2), jac=lambda x: sigma * w,
                   constraints=[{"type": "ineq", "fun": residual, "jac": gradient}],
                   bounds=[(1 / 1024, 4), (1 / 1024, 4)], method="SLSQP",
                   options={"ftol": 1e-13, "maxiter": 1000})
    if not np.all(np.isfinite(fit.x)):
        raise ValueError("No finite primal proposal")
    if kind == "maximum":
        multipliers = [Fraction(int(i == setting)) for i in (0, 1)] + [Fraction(0), Fraction(0)]
    else:
        active = np.where(residual(fit.x) < 1e-7)[0]
        values = np.zeros(4)
        values[active] = nnls(-gradient(fit.x)[active].T, -sigma * w)[0]
        multipliers = [Fraction(round(float(value) * (1 << 40)), 1 << 40) for value in values]
    theta, lam = multipliers[:2], multipliers[2:]
    a, b, _ = upper[setting]
    first = sigma * a + sum(v * row[0] for v, row in zip(theta, upper))
    second = sigma * b + sum(v * row[1] for v, row in zip(theta, upper))
    p = sum(v * row[0] for v, row in zip(lam, reciprocal))
    q = sum(v * row[1] for v, row in zip(lam, reciprocal))
    roots = [sqrt_bracket(first * p)[0], sqrt_bracket(second * q)[0]]
    raw = [Fraction(round(float(x) * (1 << 48)), 1 << 48) for x in fit.x]
    for bits in (40, 36, 32, 28, 24, 20):
        epsilon = Fraction(1, 1 << bits)
        scales = [(1 - epsilon) * x + epsilon for x in raw]
        certificate = {"multipliers": {"upper": list(map(str, theta)), "reciprocal": list(map(str, lam))},
                       "sqrt_lower": list(map(str, roots)), "primal_squared_scales": list(map(str, scales))}
        try:
            checked = check_endpoint(primitive, side, setting, kind, certificate)
        except ValueError:
            continue
        return {"certificate": certificate, "checked": checked,
                "proposal_solver_success": bool(fit.success), "proposal_iterations": int(fit.nit)}
    raise ValueError("No exact near-attaining primal/dual certificate")


def channel_ranges(primitive, side, setting, minimum, maximum):
    lower = Fraction(minimum["gain_squared_bound"])
    upper = Fraction(maximum["gain_squared_bound"])
    mu = getattr(decode(primitive), side)[setting].mu
    if not 0 < lower <= upper <= (1 - abs(mu)) ** 2:
        raise ValueError("Positive legal gain interval required")
    lo, hi = sqrt_bracket(lower)[0], sqrt_bracket(upper)[1]
    return {"canonical_gain": list(map(str, (lo, hi))),
            "canonical_e0": list(map(str, (max(Fraction(0), (1 - hi - mu) / 2), (1 - lo - mu) / 2))),
            "canonical_e1": list(map(str, (max(Fraction(0), (1 - hi + mu) / 2), (1 - lo + mu) / 2))),
            "scope": "complete_regular_fiber_of_one_frozen_generated_joint_law",
            "coordinates": "alice_squared_scales" if side == "alice" else "bob_reciprocal_squared_scales",
            "actual_ideal_label_identity_selected": False, "whole_empirical_confidence_set_bounds": False}
