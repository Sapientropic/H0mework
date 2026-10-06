#!/usr/bin/env python3
"""Nominal fixed-environment calibration from its own public readout inverse."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[7]
FREEZE = "23294e59d99a22db32c97c3aed07450b9bff5e4f"
VERSION = "p23-nominal-environment-calibration-nec0001"
SCHEMA = "p23-nominal-environment-calibration-independent/v1"
OLD_COUNTS_SHA = "056df106ecfe6802014c20cb080501b8d2111edbd89ec525e9abcc511252e8d8"
TOL = F("1e-12")
# Bare losses contain a 1/n factor; the fringe inverse transports the full root interval.
STURM_WIDTH = F("1e-24")
COHERENCE_WIDTH = F("1e-18")
GRID = 10 ** 15
FLAGS = ("CH_optimization_executed", "old_scalar_inverse_gain_or_published_controls_admitted",
         "source_mapping_identified", "exact_calibration_inverse_kernel_claim",
         "new_full_Born_or_Gaussian_determinant_kernel_claim", "actual_source_or_hardware_identity_verified",
         "apparatus_optimum_verified", "controller_advance")


def require(value, reason):
    if not value:
        raise ValueError(reason)


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frozen(path, commit=None):
    path = Path(path).resolve()
    rel = str(path.relative_to(ROOT))
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", rel], cwd=ROOT, text=True).strip()
    require(bool(commit), "uncommitted_source:" + rel)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    require(subprocess.check_output(["git", "show", commit + ":" + rel], cwd=ROOT) == path.read_bytes(),
            "source_not_frozen:" + rel)
    return {"path": rel, "sha256": sha256(path), "commit": commit}


def load_interval_source():
    path = HERE / "independent_counts.py"
    frozen(path, FREEZE)
    require(sha256(path) == OLD_COUNTS_SHA, "occupation_source_changed")
    module_spec = importlib.util.spec_from_file_location("nec_independent_occupation", path)
    module = importlib.util.module_from_spec(module_spec)
    sys.modules[module_spec.name] = module
    module_spec.loader.exec_module(module)
    return module


born = load_interval_source()
I, C = born.I, born.C


def endpoint_gap(interval, target):
    target = F(target)
    return max(F(0), interval.lo - target, target - interval.hi)


def overlap_gap(a, b):
    return max(F(0), a.lo - b.hi, b.lo - a.hi)


def nearest_grid(interval):
    def rounded(x):
        value = x * GRID + F(1, 2)
        return value.numerator // value.denominator
    lo, hi = rounded(interval.lo), rounded(interval.hi)
    require(lo == hi, "SOURCE_GRID_UNRESOLVED")
    return F(lo, GRID)


def hyperbolic(x):
    x = I.of(x)
    require(x.lo >= 0 and x.hi <= 1, "hyperbolic_domain")
    x2 = x.square()
    sine, cosine, sn, cs = I(0), I(0), x, I(1)
    for k in range(24):
        sine, cosine = sine + sn, cosine + cs
        sn = sn * x2 / ((2 * k + 2) * (2 * k + 3))
        cs = cs * x2 / ((2 * k + 1) * (2 * k + 2))
    radius = x.hi
    sr = radius ** 49 / math.factorial(49) / (1 - radius ** 2 / (50 * 51))
    cr = radius ** 48 / math.factorial(48) / (1 - radius ** 2 / (49 * 50))
    return sine + I(0, sr), cosine + I(0, cr)


def geometric_from_gain(g):
    s, c = hyperbolic(g)
    return (s / c).square()


def source_at_drive(gain, beta):
    if F(beta) == 45:
        sine = cosine = I(F(1, 2)).sqrt()
    else:
        sine, cosine = born.trig(beta)
    return [geometric_from_gain(I.of(gain) * cosine), geometric_from_gain(I.of(gain) * sine)]


def pair_probability(gain, beta):
    t_h, t_v = source_at_drive(gain, beta)
    return 1 - (1 - t_h) * (1 - t_v)


def pair_probability_derivative(gain, beta):
    gain = I.of(gain)
    sine, cosine = born.trig(beta)
    sh, ch = hyperbolic(gain * cosine)
    sv, cv = hyperbolic(gain * sine)
    z = 1 / (ch.square() * cv.square())
    return 2 * z * ((sh / ch) * cosine + (sv / cv) * sine)


def gain_from_pair_probability(target, beta):
    target = F(target)
    interval = I(0, F(1, 8))
    require(pair_probability(interval.lo, beta).hi < target < pair_probability(interval.hi, beta).lo,
            "pair_probability_not_bracketed")
    steps = 0
    for steps in range(160):
        if interval.width <= F("1e-22"):
            break
        midpoint = interval.midpoint()
        value = pair_probability(midpoint, beta)
        if value.hi < target:
            interval = I(midpoint, interval.hi)
        elif value.lo > target:
            interval = I(interval.lo, midpoint)
        else:
            derivative = pair_probability_derivative(interval, beta)
            require(derivative.lo > 0, "pair_probability_monotonicity_unresolved")
            correction = I(midpoint) + (target - value) / derivative
            lo, hi = max(interval.lo, correction.lo), min(interval.hi, correction.hi)
            require(lo < hi and hi - lo < interval.width, "gain_inverse_precision_unresolved")
            interval = I(lo, hi)
    require(interval.width <= F("1e-22"), "gain_inverse_precision_unresolved")
    grid = nearest_grid(interval)
    balanced_sinh, _ = hyperbolic(I(grid) * I(F(1, 2)).sqrt())
    n = balanced_sinh.square()
    true_sinh, _ = hyperbolic(interval * I(F(1, 2)).sqrt())
    true_n = true_sinh.square()
    n_grid = nearest_grid(n)
    require(nearest_grid(true_n) == n_grid, "calibration_n_grid_depends_on_gain_rounding")
    require(endpoint_gap(pair_probability(grid, beta), target) <= TOL, "reference_pair_readback_failed")
    return {"G": grid, "G_enclosure": interval, "n": n, "n_grid": n_grid,
            "n_source_enclosure": true_n, "steps": steps + 1,
            "reference_q": pair_probability(grid, beta)}


def ptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    return ptrim([(a[k] if k < len(a) else 0) + (b[k] if k < len(b) else 0)
                  for k in range(max(len(a), len(b)))])


def pmul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return ptrim(out)


def pderivative(p):
    return [k * p[k] for k in range(1, len(p))] or [F(0)]


def peval(p, x):
    value = p[-1]
    for coefficient in reversed(p[:-1]):
        value = value * x + coefficient
    return value


def premainder(a, b):
    a, b = ptrim(a), ptrim(b)
    require(b != [0], "polynomial_zero_divisor")
    while len(a) >= len(b) and a != [0]:
        offset = len(a) - len(b)
        factor = a[-1] / b[-1]
        for i, coefficient in enumerate(b):
            a[offset + i] -= factor * coefficient
        a = ptrim(a)
    return a


def sturm_sequence(p):
    sequence = [ptrim(p), pderivative(p)]
    while sequence[-1] != [0]:
        remainder = premainder(sequence[-2], sequence[-1])
        if remainder == [0]:
            break
        # Positive rescaling preserves every variation and limits Fraction growth.
        scale = abs(remainder[-1])
        sequence.append([-x / scale for x in remainder])
    require(len(sequence[-1]) == 1 and sequence[-1][0] != 0, "multiple_cubic_root_unresolved")
    return sequence


def variations(sequence, x):
    signs = [(value > 0) - (value < 0) for value in (peval(p, x) for p in sequence)]
    signs = [s for s in signs if s]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def isolate_all_roots(polynomial):
    polynomial = ptrim(polynomial)
    require(len(polynomial) == 4, "K_polynomial_not_cubic")
    sequence = sturm_sequence(polynomial)
    bound = F(2 + math.ceil(max(abs(x / polynomial[-1]) for x in polynomial[:-1])))
    require(peval(polynomial, -bound) != 0 and peval(polynomial, bound) != 0, "Cauchy_bound_root")
    total = variations(sequence, -bound) - variations(sequence, bound)
    roots, queue, split_count = [], [(-bound, bound, total)], 0
    while queue:
        lo, hi, count = queue.pop()
        if not count:
            continue
        if count == 1 and hi - lo <= STURM_WIDTH:
            roots.append(I(lo, hi))
            continue
        middle = (lo + hi) / 2
        vm, vh, vl = variations(sequence, middle), variations(sequence, hi), variations(sequence, lo)
        middle_root, right_root = int(peval(polynomial, middle) == 0), int(peval(polynomial, hi) == 0)
        left, right = vl - vm - middle_root, vm - vh - right_root
        require(left >= 0 and right >= 0 and left + right + middle_root == count, "Sturm_partition_error")
        if middle_root:
            roots.append(I(middle))
        queue.extend([(middle, hi, right), (lo, middle, left)])
        split_count += 1
    roots.sort(key=lambda x: x.lo)
    require(len(roots) == total and all(x.width <= STURM_WIDTH for x in roots), "incomplete_Sturm_cover")
    return roots, {"polynomial": [str(x) for x in polynomial], "sequence": [[str(x) for x in p] for p in sequence],
                   "Cauchy_bound": str(bound), "all_real_root_count": total, "split_count": split_count,
                   "root_intervals": [x.packet() for x in roots], "full_real_cover": True}


def k_inverse(n, ka, kb, background):
    n, ka, kb = F(n), F(ka), F(kb)
    ba, bb = [F(x) for x in background]
    require(n > 0 and 0 < ka <= 1 and 0 < kb <= 1, "invalid_K_input")
    ratio, w, zeta = kb / ka, 1 + kb / ka - kb, (1 - ba) * (1 - bb)
    q = [1 - ba - bb - ba * bb / n,
         ba * ratio + bb + (bb + ratio * ba) / n,
         -ratio * (1 + 1 / n)]
    polynomial = padd(pmul([1, -w], q), [-zeta * x for x in pmul([1, -1], [1, -ratio])])
    roots, certificate = isolate_all_roots(polynomial)
    lower = max(ba, bb / ratio)
    upper = min((ba + n) / (1 + n), (bb + n) / (ratio * (1 + n)))
    require(lower <= upper, "empty_K_physical_domain")
    retained, classification = [], []
    for index, interval in enumerate(roots):
        if interval.hi < lower or interval.lo > upper:
            classification.append({"index": index, "status": "OUTSIDE_PHYSICAL_DOMAIN"})
            continue
        require(lower <= interval.lo <= interval.hi <= upper, "K_domain_boundary_unresolved")
        require(interval.lo > 0 and (ratio * interval).lo > 0 and interval.hi < 1 and
                (ratio * interval).hi < 1, "K_herald_or_denominator_unresolved")
        ta = (interval - ba) / (n * (1 - interval))
        tb = (ratio * interval - bb) / (n * (1 - ratio * interval))
        require(0 <= ta.lo <= ta.hi <= 1 and 0 <= tb.lo <= tb.hi <= 1, "bare_loss_not_physical")
        readback = matched_readout(I(n), ta, tb, background)
        require(all(endpoint_gap(readback[k], target) <= TOL for k, target in (("K_A", ka), ("K_B", kb))),
                "K_cubic_readback_failed")
        retained.append({"root_index": index, "a": interval, "TA": ta, "TB": tb})
        classification.append({"index": index, "status": "PHYSICAL_ROOT_RETAINED"})
    certificate.update({"physical_domain": [str(lower), str(upper)], "classification": classification,
                        "physical_root_count": len(retained), "no_root_selection_by_target": True})
    return retained, certificate


def matched_readout(n, ta, tb, background):
    za, zb = [1 - F(x) for x in background]
    p0a, p0b, p00 = 1 / (1 + n * ta), 1 / (1 + n * tb), 1 / (1 + n * (ta + tb - ta * tb))
    sa, sb = 1 - za * p0a, 1 - zb * p0b
    joint = 1 - za * p0a - zb * p0b + za * zb * p00
    require(sa.lo > 0 and sb.lo > 0, "zero_herald")
    return {"S_A": sa, "S_B": sb, "J": joint, "K_A": joint / sb, "K_B": joint / sa}


SYMBOLS = ("n", "A", "B", "xa", "xb", "y", "w", "z", "k", "uA", "uB", "c")


class S:
    """Exact sparse polynomial ring for native two-polarization determinants."""
    def __init__(self, terms=0):
        if isinstance(terms, S):
            self.terms = terms.terms
        elif isinstance(terms, dict):
            self.terms = {m: F(c) for m, c in terms.items() if c}
        else:
            self.terms = {} if terms == 0 else {(0,) * len(SYMBOLS): F(terms)}

    @staticmethod
    def variable(name):
        exponent = [0] * len(SYMBOLS)
        exponent[SYMBOLS.index(name)] = 1
        return S({tuple(exponent): F(1)})

    def __add__(self, other):
        other = S(other)
        result = dict(self.terms)
        for exponent, coefficient in other.terms.items():
            result[exponent] = result.get(exponent, 0) + coefficient
        return S(result)

    __radd__ = __add__

    def __neg__(self):
        return S({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-S(other))

    def __rsub__(self, other):
        return S(other) - self

    def __mul__(self, other):
        other = S(other)
        result = {}
        for a, x in self.terms.items():
            for b, y in other.terms.items():
                exponent = tuple(i + j for i, j in zip(a, b))
                result[exponent] = result.get(exponent, 0) + x * y
        return S(result)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        return S({m: c / F(scalar) for m, c in self.terms.items()})

    def __pow__(self, n):
        result = S(1)
        for _ in range(n):
            result = result * self
        return result

    def substitute(self, replacements):
        result = S()
        for monomial, coefficient in self.terms.items():
            term = S(coefficient)
            for name, exponent in zip(SYMBOLS, monomial):
                if exponent:
                    term = term * replacements.get(name, S.variable(name)) ** exponent
            result = result + term
        return result

    def packet(self):
        return {"*".join(name + "^" + str(e) for name, e in zip(SYMBOLS, monomial) if e) or "1": str(coefficient)
                for monomial, coefficient in sorted(self.terms.items())}


def smm(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), S())
             for j in range(len(b[0]))] for i in range(len(a))]


def determinant(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def angular_reduce(polynomial, basis):
    y, z = S.variable("y"), S.variable("z")
    result = S()
    for monomial, coefficient in polynomial.terms.items():
        exponents = dict(zip(SYMBOLS, monomial))
        term = S(coefficient)
        if basis == "DA":
            require(exponents["w"] % 2 == 0, "native_DA_odd_cosine_did_not_cancel")
            term = term * (1 - y ** 2) ** (exponents.pop("w") // 2)
            require(exponents.pop("k") == 0 and exponents.pop("z") == 0, "native_DA_wrong_angle_symbol")
        else:
            require(exponents["k"] % 2 == 0, "native_HV_odd_sine_cosine_did_not_cancel")
            term = term * (z - z ** 2) ** (exponents.pop("k") // 2)
            require(exponents.pop("w") == 0 and exponents.pop("y") == 0, "native_HV_wrong_angle_symbol")
        ea, eb = exponents.pop("xa"), exponents.pop("xb")
        term = term * S.variable("uA") ** (ea // 2) * S.variable("uB") ** (eb // 2)
        require(ea % 2 == eb % 2, "unpaired_environment_overlap")
        if ea % 2:
            term = term * S.variable("c")
        for name, exponent in exponents.items():
            term = term * S.variable(name) ** exponent
        result = result + term
    return result


def generate_native_fringe_polynomials():
    n, a, b, xa, xb, y, w, z, k = [S.variable(x) for x in SYMBOLS[:9]]
    unit = [[S(1), S()], [S(), S(1)]]
    result = {}
    for basis in ("HV", "DA"):
        if basis == "HV":
            ea = [[a * (1 - z), a * xa * k], [a * xa * k, a * z]]
            eb = [[S(), S()], [S(), b]]
        else:
            ea = [[a * (1 - w) / 2, a * xa * y / 2], [a * xa * y / 2, a * (1 + w) / 2]]
            eb = [[b / 2, b * xb / 2], [b * xb / 2, b / 2]]
        product = smm(ea, eb)
        interaction = [[ea[i][j] + eb[i][j] - product[i][j] for j in range(2)] for i in range(2)]
        qa = determinant([[unit[i][j] + n * ea[i][j] for j in range(2)] for i in range(2)])
        qb = determinant([[unit[i][j] + n * eb[i][j] for j in range(2)] for i in range(2)])
        qab = determinant([[unit[i][j] + n * interaction[i][j] for j in range(2)] for i in range(2)])
        polynomials = {name: angular_reduce(polynomial, basis) for name, polynomial in (("QA", qa), ("QB", qb), ("QAB", qab))}
        angle = SYMBOLS.index("z" if basis == "HV" else "y")
        require(all(max((m[angle] for m in p.terms), default=0) <= 2 for p in polynomials.values()), "fringe_degree_changed")
        result[basis] = polynomials
    return result


@dataclass(frozen=True)
class Jet:
    value: I
    derivative: I

    def __init__(self, value, derivative=0):
        object.__setattr__(self, "value", I.of(value))
        object.__setattr__(self, "derivative", I.of(derivative))

    @staticmethod
    def of(x):
        return x if isinstance(x, Jet) else Jet(x)

    def __add__(self, other):
        other = Jet.of(other)
        return Jet(self.value + other.value, self.derivative + other.derivative)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.value, -self.derivative)

    def __sub__(self, other):
        return self + (-Jet.of(other))

    def __rsub__(self, other):
        return Jet.of(other) - self

    def __mul__(self, other):
        other = Jet.of(other)
        return Jet(self.value * other.value, self.derivative * other.value + self.value * other.derivative)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Jet.of(other)
        return Jet(self.value / other.value,
                   (self.derivative * other.value - self.value * other.derivative) / other.value.square())

    def __rtruediv__(self, other):
        return Jet.of(other) / self

    def __pow__(self, n):
        result = Jet(1)
        for _ in range(n):
            result = result * self
        return result


def allocation_parameters(c, allocation):
    if allocation == "symmetric":
        return c, c
    if allocation == "Alice_rank_one":
        return c * 0 + 1, c ** 2
    if allocation == "Bob_rank_one":
        return c ** 2, c * 0 + 1
    raise ValueError("unknown_allocation")


def evaluate_coefficients(polynomial, basis, parameters):
    index = SYMBOLS.index("z" if basis == "HV" else "y")
    zero = Jet(0) if any(isinstance(x, Jet) for x in parameters.values()) else I(0)
    result = [zero for _ in range(3)]
    for monomial, coefficient in polynomial.terms.items():
        value = zero + coefficient
        for j, exponent in enumerate(monomial):
            if j != index and exponent:
                require(SYMBOLS[j] in parameters, "uneliminated_fringe_symbol:" + SYMBOLS[j])
                value = value * parameters[SYMBOLS[j]] ** exponent
        result[monomial[index]] = result[monomial[index]] + value
    return result


def fringe_coefficients(symbolic, n, ta, tb, c, allocation, basis, derivative_c=False):
    if derivative_c:
        c = Jet(c, 1)
        u_a, u_b = allocation_parameters(c, allocation)
        parameters = {"n": Jet(n), "A": Jet(ta), "B": Jet(tb), "c": c, "uA": u_a, "uB": u_b}
    else:
        c = I.of(c)
        u_a, u_b = allocation_parameters(c, allocation)
        parameters = {"n": I.of(n), "A": ta, "B": tb, "c": c, "uA": u_a, "uB": u_b}
    return {name: evaluate_coefficients(polynomial, basis, parameters) for name, polynomial in symbolic[basis].items()}


def horner(coefficients, x):
    value = coefficients[-1]
    for coefficient in reversed(coefficients[:-1]):
        value = value * x + coefficient
    return value


def raw_fringe(coefficients, x, background):
    za, zb = [1 - F(t) for t in background]
    qa, qb, qab = [horner(coefficients[name], x) for name in ("QA", "QB", "QAB")]
    for value in (qa, qb, qab):
        require((value.value if isinstance(value, Jet) else value).lo > 0, "fringe_denominator_unresolved")
    return 1 - za / qa - zb / qb + za * zb / qab


def fringe_derivative(coefficients, domain, background):
    za, zb = [1 - F(t) for t in background]
    qa, qb, qab = [horner(coefficients[name], domain) for name in ("QA", "QB", "QAB")]
    require(all(x.lo > 0 for x in (qa, qb, qab)), "fringe_derivative_denominator_unresolved")
    dqa = coefficients["QA"][1] + 2 * coefficients["QA"][2] * domain
    dqb = coefficients["QB"][1] + 2 * coefficients["QB"][2] * domain
    dqab = coefficients["QAB"][1] + 2 * coefficients["QAB"][2] * domain
    return za * dqa / qa.square() + zb * dqb / qb.square() - za * zb * dqab / qab.square()


def raw_visibility(coefficients, background):
    minimum, maximum = raw_fringe(coefficients, -1, background), raw_fringe(coefficients, 1, background)
    denominator = minimum + maximum
    require((denominator.value if isinstance(denominator, Jet) else denominator).lo > 0, "zero_fringe_denominator")
    return (maximum - minimum) / denominator


def low_coherence_exclusion(n, ta, tb, background, c_upper):
    n, ta, tb = I.of(n), I.of(ta), I.of(tb)
    require(0 < n.lo <= n.hi <= 1, "first_pair_tail_domain")
    t = n / (1 + n)
    z = (1 - t).square()
    source_pair = z * t
    # For two balanced geometric branches, this is P(total pairs >= 2).
    tail_two = 3 * t.square() - 2 * t ** 3
    ba, bb = [F(x) for x in background]
    za, zb = 1 - ba, 1 - bb
    common = source_pair * ta * tb / 2
    lower = za * zb * common * (1 - F(c_upper)) + ba * zb * source_pair * tb + bb * za * source_pair * ta + ba * bb
    upper = (za * zb * (common * (1 + F(c_upper)) + tail_two) +
             ba * zb * (source_pair * tb + tail_two) + bb * za * (source_pair * ta + tail_two) + ba * bb)
    require(lower.lo > 0, "low_coherence_fringe_lower_unresolved")
    bound = (upper - lower) / (upper + lower)
    return {"domain": ["0", str(c_upper)], "pair_total_mass": (2 * source_pair).packet(),
            "source_total_pair_ge_2_tail": tail_two.packet(), "all_fringe_J_lower": lower.packet(),
            "all_fringe_J_upper": upper.packet(), "raw_visibility_upper_bound": bound.packet(),
            "upper": bound.hi, "source_zero_one_pair_and_original_tail": True}


def coherence_inverse(symbolic, n, ta, tb, target, allocation, spec):
    domain = I(*spec["coherence_inverse_domain"])
    background = spec["background_per_pulse"]
    derivative_coefficients = fringe_coefficients(symbolic, n, ta, tb, domain, allocation, "DA", True)
    derivative = raw_visibility(derivative_coefficients, background).derivative
    require(derivative.lo > 0, "visibility_inverse_monotonicity_unresolved")
    da_coefficients = fringe_coefficients(symbolic, n, ta, tb, domain, allocation, "DA")
    angular_derivative = fringe_derivative(da_coefficients, I(-1, 1), background)
    require(angular_derivative.lo > 0, "full_DA_fringe_extrema_unresolved")
    target = F(target)
    def value(c):
        return raw_visibility(fringe_coefficients(symbolic, n, ta, tb, c, allocation, "DA"), background)
    endpoints = [value(domain.lo), value(domain.hi)]
    require(endpoints[0].hi < target < endpoints[1].lo, "coherence_target_not_bracketed")
    low_domain = low_coherence_exclusion(n, ta, tb, background, spec["coherence_low_domain"][1])
    minimum_target = F(spec["DA_raw_visibility"]["box_low"])
    require(low_domain["upper"] < minimum_target, "low_coherence_exclusion_unresolved")
    root = domain
    steps = 0
    for steps in range(160):
        if root.width <= COHERENCE_WIDTH:
            break
        midpoint = root.midpoint()
        enclosure = value(midpoint)
        if enclosure.hi < target:
            root = I(midpoint, root.hi)
        elif enclosure.lo > target:
            root = I(root.lo, midpoint)
        else:
            correction = I(midpoint) + (target - enclosure) / derivative
            lo, hi = max(root.lo, correction.lo), min(root.hi, correction.hi)
            require(lo < hi and hi - lo < root.width, "coherence_inverse_precision_unresolved")
            root = I(lo, hi)
    require(root.width <= F(spec["root_interval_max_width"]), "coherence_root_too_wide")
    readback = value(root)
    require(readback.width <= TOL and endpoint_gap(readback, target) <= TOL, "DA_visibility_readback_failed")
    hv_coefficients = fringe_coefficients(symbolic, n, ta, tb, root, allocation, "HV")
    hv_derivative = fringe_derivative(hv_coefficients, I(0, 1), background)
    require(hv_derivative.lo > 0, "full_HV_fringe_extrema_unresolved")
    hv_min, hv_max = raw_fringe(hv_coefficients, 0, background), raw_fringe(hv_coefficients, 1, background)
    hv_visibility = (hv_max - hv_min) / (hv_max + hv_min)
    require(F(spec["HV_raw_visibility"]["box_low"]) <= hv_visibility.lo <= hv_visibility.hi <=
            F(spec["HV_raw_visibility"]["box_high"]), "HV_visibility_outside_public_box")
    low_domain.pop("upper")
    return root, {"low_coherence_exclusion": low_domain,
                  "DA_y_domain": ["-1", "1"], "DA_full_domain_dJ_dy": angular_derivative.packet(),
                  "coherence_inverse_domain": spec["coherence_inverse_domain"],
                  "full_domain_dV_dc": derivative.packet(), "endpoint_visibility": [x.packet() for x in endpoints],
                  "HV_z_domain": ["0", "1"], "HV_full_domain_dJ_dz": hv_derivative.packet(),
                  "HV_visibility": hv_visibility.packet(), "DA_visibility": readback.packet(),
                  "root_steps": steps + 1, "c_root": root.packet(),
                  "HV_coefficients": {k: [x.packet() for x in v] for k, v in hv_coefficients.items()},
                  "DA_coefficients": {k: [x.packet() for x in v] for k, v in
                                      fringe_coefficients(symbolic, n, ta, tb, root, allocation, "DA").items()},
                  "full_fringe_extrema_generated_before_endpoint_readout": True,
                  "coherence_is_visibility_input": False}


def environment_effect(transmission, xi, degrees):
    transmission, xi = I.of(transmission), I.of(xi)
    require(0 <= transmission.lo <= transmission.hi <= 1 and 0 <= xi.lo <= xi.hi <= 1,
            "illegal_local_source_primitive")
    complement = (1 - xi.square()).sqrt()
    embedding = [[C(1), C()], [C(), C()], [C(), C(xi)], [C(), C(complement)]]
    root = transmission.sqrt()
    transmitted = [[entry * root for entry in row] for row in embedding]
    sine, cosine = born.trig(degrees)
    vector = [sine, cosine]
    projection = [[C(vector[p] * vector[q] if e == f else 0) for q in range(2) for f in range(2)]
                  for p in range(2) for e in range(2)]
    click = born.mm(born.adjoint(transmitted), born.mm(projection, transmitted))
    no_click = born.mm(born.adjoint(transmitted), born.mm(born.matrix_subtract(born.identity(4), projection), transmitted))
    no_click = [[no_click[p][q] + C((1 - transmission) if p == q else 0) for q in range(2)] for p in range(2)]
    require(born.same_matrices(born.mm(born.adjoint(embedding), embedding), born.identity(2)), "native_embedding_isometry_failed")
    require(born.same_matrices(no_click, born.matrix_subtract(born.identity(2), click)), "native_projector_loss_closure_failed")
    return {"embedding": embedding, "projection": projection, "click": click, "no_click": no_click}


def source_packet(source, beta_degrees):
    t_h, t_v = source_at_drive(source["G"], beta_degrees)
    c = source["c"]
    if source["allocation"] == "symmetric":
        xa = xb = c.sqrt()
    elif source["allocation"] == "Alice_rank_one":
        xa, xb = I(1), c
    else:
        xa, xb = c, I(1)
    return {"tH": t_h, "tV": t_v, "TA": source["TA"], "TB": source["TB"],
            "xiA": xa, "xiB": xb, "phase": [F(1), F(0)], "beta_deg": F(beta_degrees)}


def exact_tail(t_h, t_v, cutoff):
    z = (1 - t_h) * (1 - t_v)
    return 1 - z * sum(t_h ** h * t_v ** (n - h) for n in range(cutoff + 1) for h in range(n + 1))


def packet_tail(packet, cutoff):
    # Independent geometric coordinates couple monotonically to total pair number.
    lo = exact_tail(packet["tH"].lo, packet["tV"].lo, cutoff)
    hi = exact_tail(packet["tH"].hi, packet["tV"].hi, cutoff)
    require(0 <= lo <= hi <= 1, "source_tail_range_failed")
    return I(lo, hi)


def sector_amplitudes(packet, n):
    root_h, root_v = packet["tH"].sqrt(), packet["tV"].sqrt()
    root_z = ((1 - packet["tH"]) * (1 - packet["tV"])).sqrt()
    return [root_z * root_h ** h * root_v ** (n - h) for h in range(n + 1)]


def real_block(matrix):
    require(all(entry.im.lo == entry.im.hi == 0 for row in matrix for entry in row), "fixed_phase_zero_block_not_real")
    return [[entry.re for entry in row] for row in matrix]


def coherent_contract(amplitudes, a, b):
    return sum((amplitudes[h] * amplitudes[k] * a[h][k] * b[h][k]
                for h in range(len(amplitudes)) for k in range(len(amplitudes))), I(0))


def independent_born(packet, effects, cutoff, background):
    blocks = [[real_block(born.occupation_polynomial(site["no_click"], n)) for n in range(cutoff + 1)]
              for site in effects]
    no_click = [I(0), I(0), I(0)]
    outcomes = {key: I(0) for key in ("++", "+0", "0+", "00")}
    sector_rows = []
    mass_prefix = I(0)
    for n in range(cutoff + 1):
        amplitudes = sector_amplitudes(packet, n)
        unit = [[I(int(h == k)) for k in range(n + 1)] for h in range(n + 1)]
        ga, gb = blocks[0][n], blocks[1][n]
        ca = [[unit[h][k] - ga[h][k] for k in range(n + 1)] for h in range(n + 1)]
        cb = [[unit[h][k] - gb[h][k] for k in range(n + 1)] for h in range(n + 1)]
        local_a = sum((amplitudes[h].square() * ga[h][h] for h in range(n + 1)), I(0))
        local_b = sum((amplitudes[h].square() * gb[h][h] for h in range(n + 1)), I(0))
        joint_zero = coherent_contract(amplitudes, ga, gb)
        sector_outcomes = {"++": coherent_contract(amplitudes, ca, cb), "+0": coherent_contract(amplitudes, ca, gb),
                           "0+": coherent_contract(amplitudes, ga, cb), "00": joint_zero}
        source_mass = sum((amplitude.square() for amplitude in amplitudes), I(0))
        require((sum(sector_outcomes.values(), I(0)) - source_mass).contains(0), "occupation_sector_mass_identity_failed")
        no_click = [total + value for total, value in zip(no_click, (local_a, local_b, joint_zero))]
        mass_prefix = mass_prefix + source_mass
        for key in outcomes:
            outcomes[key] = outcomes[key] + sector_outcomes[key]
        sector_rows.append({"total_pairs": n, "mass": source_mass.packet(),
                            "no_click": [x.packet() for x in (local_a, local_b, joint_zero)],
                            "outcomes": {k: v.packet() for k, v in sector_outcomes.items()}})
    tail = packet_tail(packet, cutoff)
    require((mass_prefix + tail).contains(1), "original_number_mass_tail_identity_failed")
    prefix_mass_upper = 1 - tail.lo
    full_zero = [born.physical_interval(x, prefix_mass_upper, "no_click_prefix") + I(0, tail.hi) for x in no_click]
    full_zero = [born.physical_interval(x, 1, "no_click_full") for x in full_zero]
    signal_outcomes = {key: born.physical_interval(value, prefix_mass_upper, "outcome_prefix") + I(0, tail.hi)
                       for key, value in outcomes.items()}
    derived = born.outcomes_from_no_click(full_zero)
    signal_outcomes = {key: born.intersect(born.physical_interval(value, 1, key),
                                          born.physical_interval(derived[key], 1, key), "full_Born_" + key)
                       for key, value in signal_outcomes.items()}
    ba, bb = [F(x) for x in background]
    za, zb = 1 - ba, 1 - bb
    observed_zero = [za * full_zero[0], zb * full_zero[1], za * zb * full_zero[2]]
    observed_outcomes = {"++": signal_outcomes["++"] + bb * signal_outcomes["+0"] +
                                ba * signal_outcomes["0+"] + ba * bb * signal_outcomes["00"],
                         "+0": zb * (signal_outcomes["+0"] + ba * signal_outcomes["00"]),
                         "0+": za * (signal_outcomes["0+"] + bb * signal_outcomes["00"]),
                         "00": za * zb * signal_outcomes["00"]}
    require(sum(signal_outcomes.values(), I(0)).contains(1) and sum(observed_outcomes.values(), I(0)).contains(1),
            "full_Born_outcomes_mass_failed")
    return {"no_click": full_zero, "signal": {"S_A": 1 - full_zero[0], "S_B": 1 - full_zero[1],
                                               "J": signal_outcomes["++"]},
            "observed": {"S_A": 1 - observed_zero[0], "S_B": 1 - observed_zero[1],
                         "J": observed_outcomes["++"]},
            "signal_outcomes": signal_outcomes, "observed_outcomes": observed_outcomes,
            "prefix_mass": mass_prefix, "tail": tail, "sectors": sector_rows,
            "Gamma_sector_dimensions": list(range(1, cutoff + 2)), "prefix_renormalized": False}


def determinant_readout(packet, effects, background):
    d = [[C(packet["tH"].sqrt()), C()], [C(), C(packet["tV"].sqrt())]]
    a, b = [site["no_click"] for site in effects]
    dd = born.mm(born.adjoint(d), d)
    matrices = [born.mm(born.adjoint(d), born.mm(a, d)), born.mm(dd, born.transpose(b)),
                born.mm(born.mm(born.adjoint(d), born.mm(a, d)), born.transpose(b))]
    z = (1 - packet["tH"]) * (1 - packet["tV"])
    p0 = []
    for matrix in matrices:
        denominator = born.real_enclosure(born.determinant_2(born.matrix_subtract(born.identity(2), matrix)), "native_det")
        require(denominator.lo > 0, "native_source_denominator_failed")
        p0.append(z / denominator)
    za, zb = [1 - F(x) for x in background]
    signal = {"S_A": 1 - p0[0], "S_B": 1 - p0[1], "J": 1 - p0[0] - p0[1] + p0[2]}
    observed = {"S_A": 1 - za * p0[0], "S_B": 1 - zb * p0[1], "J": 1 - za * p0[0] - zb * p0[1] + za * zb * p0[2]}
    return {"no_click": p0, "signal": signal, "observed": observed}


def born_probes(source, spec):
    settings = [("HV_max", "0", "0"), ("HV_min", "90", "0"),
                ("DA_max", "45", "45"), ("DA_min", "-45", "45")]
    cache, rows, readbacks = {}, [], {}
    for preparation, beta in (("balanced", spec["balanced_pump_beta_deg"]),
                              ("reference", spec["reference_pump_beta_deg"])):
        packet = source_packet(source, beta)
        for name, a, b in settings:
            keys = (("A", a), ("B", b))
            for side, angle in keys:
                if (side, angle) not in cache:
                    cache[(side, angle)] = environment_effect(packet["T" + side], packet["xi" + side], angle)
            effects = [cache[key] for key in keys]
            result = independent_born(packet, effects, spec["total_pair_prefix"], spec["background_per_pulse"])
            algebraic = determinant_readout(packet, effects, spec["background_per_pulse"])
            gaps = {family: {key: overlap_gap(result[family][key], algebraic[family][key])
                             for key in ("S_A", "S_B", "J")} for family in ("signal", "observed")}
            require(all(x <= TOL for family in gaps.values() for x in family.values()), "native_occupation_vs_det_failed")
            if preparation == "balanced":
                readbacks[name] = algebraic["observed"]
            rows.append({"preparation": preparation, "beta_deg": str(beta), "probe": name, "angles_deg": [a, b],
                         "source": {"tH": packet["tH"].packet(), "tV": packet["tV"].packet(), "phase": ["1", "0"]},
                         "total_pair_prefix": spec["total_pair_prefix"], "prefix_renormalized": False,
                         "source_mass_prefix": result["prefix_mass"].packet(), "number_mass_tail": result["tail"].packet(),
                         "Gamma_sector_dimensions": result["Gamma_sector_dimensions"], "sector_readout": result["sectors"],
                         "coherent_Born_signal": {k: v.packet() for k, v in result["signal"].items()},
                         "coherent_Born_observed": {k: v.packet() for k, v in result["observed"].items()},
                         "coherent_Born_signal_outcomes": {k: v.packet() for k, v in result["signal_outcomes"].items()},
                         "coherent_Born_observed_outcomes": {k: v.packet() for k, v in result["observed_outcomes"].items()},
                         "native_determinant_signal": {k: v.packet() for k, v in algebraic["signal"].items()},
                         "native_determinant_observed": {k: v.packet() for k, v in algebraic["observed"].items()},
                         "comparison_gap": {f: {k: str(v) for k, v in g.items()} for f, g in gaps.items()},
                         "comparison_passed": True})
            print("occupation calibration " + source["source_id"] + " " + preparation + "/" + name,
                  file=sys.stderr, flush=True)
    vv = readbacks["HV_max"]
    require(vv["S_A"].lo > 0 and vv["S_B"].lo > 0, "native_zero_herald")
    k_a, k_b = vv["J"] / vv["S_B"], vv["J"] / vv["S_A"]
    hv = (readbacks["HV_max"]["J"] - readbacks["HV_min"]["J"]) / (
        readbacks["HV_max"]["J"] + readbacks["HV_min"]["J"])
    da = (readbacks["DA_max"]["J"] - readbacks["DA_min"]["J"]) / (
        readbacks["DA_max"]["J"] + readbacks["DA_min"]["J"])
    return rows, {"K_A": k_a, "K_B": k_b, "HV_raw_visibility": hv, "DA_raw_visibility": da}


def efficiency_units(text, source_text, spec):
    declared = re.findall(r"双百分数\s*([\d.]+)±([\d.]+)%／([\d.]+)±([\d.]+)%", text)
    require(len(declared) == 1, "ambiguous_efficiency_text")
    public = re.findall(r"efficiencies\s+([\d.]+)\s*\+\-\s*([\d.]+)\s*%\s*\(Alice\)\s*and\s*"
                        r"([\d.]+)\s*\+\-\s*([\d.]+)\s*%\s*\(Bob\)", source_text)
    require(len(public) == 1 and tuple(F(x) for x in public[0]) == tuple(F(x) for x in declared[0]),
            "public_efficiency_text_mismatch")
    a, da, b, db = [F(x) / 100 for x in declared[0]]
    require((a, da) == (F(spec["K_A"]["center"]), F(spec["K_A"]["half_width"])) and
            (b, db) == (F(spec["K_B"]["center"]), F(spec["K_B"]["half_width"])), "efficiency_unit_mismatch")
    return {"probability_center": [str(a), str(b)], "probability_half_width": [str(da), str(db)],
            "percent_text_independently_parsed": True, "public_text_and_machine_block_agree": True}


def load_frozen():
    text = (HERE / "calibration-criterion.md").read_text()
    blocks = re.findall(r"<!-- NEC-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- NEC-FROZEN-END -->", text, re.S)
    require(len(blocks) == 1, "ambiguous_calibration_contract")
    spec = json.loads(blocks[0])
    sources = json.loads((HERE / "calibration-sources.json").read_text())
    bindings = {"criterion": frozen(HERE / "calibration-criterion.md", FREEZE),
                "sources": frozen(HERE / "calibration-sources.json", FREEZE),
                "program": frozen(Path(__file__)), "input_sources": []}
    require(spec["version"] == sources["version"] == VERSION and all(spec[k] is False for k in FLAGS), "calibration_scope_changed")
    require(spec["precision_digits"] == 40 and spec["source_grid_digits"] == 15 and
            spec["source_grid_tie_rule"] == "toward_positive_infinity" and spec["total_pair_prefix"] == 6 and
            spec["prefix_renormalized"] is False and F(spec["readout_tolerance"]) == TOL and
            spec["calibration_pulses"] == 1 and spec["source_phase"] == ["1", "0"], "calibration_numerical_method_changed")
    require(spec["event_files_read"] == 0 and spec["retrospective"] is True and
            sources["published_r_angles_or_Table_SII_used_as_inverse_inputs"] is False and
            sources["publication_configuration_identified"] is False, "calibration_input_role_changed")
    require(len(sources["inputs"]) == 24, "calibration_source_inventory_changed")
    for row in sources["inputs"]:
        binding = frozen(ROOT / row["path"], FREEZE)
        require(binding["sha256"] == row["sha256"], "calibration_source_digest_changed:" + row["path"])
        bindings["input_sources"].append(binding)
    public_text = (HERE.parents[1] / "shalm2015-channel-inputs.txt").read_text()
    units = efficiency_units(text, public_text, spec)
    return spec, bindings, units


def input_points(spec):
    axes = spec["four_box_axes_order"]
    center = {name: spec[name]["center"] for name in axes}
    result = [{"point_id": "default:center", "allocation": spec["default_allocation"], "inputs": center}]
    boxes = [(str(F(spec[name]["center"]) - F(spec[name]["half_width"])),
              str(F(spec[name]["center"]) + F(spec[name]["half_width"])))
             if "half_width" in spec[name] else (spec[name]["box_low"], spec[name]["box_high"]) for name in axes]
    for bits in itertools.product((0, 1), repeat=4):
        result.append({"point_id": "default:corner_" + "".join(map(str, bits)), "allocation": spec["default_allocation"],
                       "inputs": {name: box[bit] for name, box, bit in zip(axes, boxes, bits)}})
    for allocation in spec["center_allocation_overrides"]:
        result.append({"point_id": allocation + ":center", "allocation": allocation, "inputs": dict(center)})
    require(len(result) == spec["total_source_points_with_overrides"] == 19 and len(result[:-2]) == spec["default_point_count"] == 17,
            "calibration_point_inventory_changed")
    return result


def source_as_json(source):
    u_a, u_b = allocation_parameters(source["c"], source["allocation"])
    packet = source_packet(source, 45)
    return {"source_id": source["source_id"], "allocation": source["allocation"],
            "G_grid15": str(source["G"]), "balanced_n_grid15": str(source["n_grid"]),
            "G_enclosure": source["G_enclosure"].packet(), "balanced_n_enclosure": source["n"].packet(),
            "balanced_n_from_unrounded_G": source["n_source_enclosure"].packet(),
            "transmission_A": source["TA"].packet(), "transmission_B": source["TB"].packet(),
            "c": source["c"].packet(), "xiA": packet["xiA"].packet(), "xiB": packet["xiB"].packet(),
            "uA": u_a.packet(), "uB": u_b.packet(), "phase": ["1", "0"],
            "same_gain_for_all_preparations": True,
            "reference": {"beta_deg": "16", "tH": source_packet(source, 16)["tH"].packet(),
                          "tV": source_packet(source, 16)["tV"].packet()},
            "balanced": {"beta_deg": "45", "tH": packet["tH"].packet(), "tV": packet["tV"].packet()}}


def generate(progress=True):
    spec, bindings, units = load_frozen()
    symbolic = generate_native_fringe_polynomials()
    points = input_points(spec)
    rows, gains = [], {}
    for point in points:
        row = dict(point)
        row["sources"] = []
        try:
            inputs = point["inputs"]
            q = F(inputs["pair_probability"])
            if q not in gains:
                gains[q] = gain_from_pair_probability(q, spec["reference_pump_beta_deg"])
            gain = gains[q]
            roots, sturm = k_inverse(gain["n_grid"], inputs["K_A"], inputs["K_B"], spec["background_per_pulse"])
            row["K_inverse"] = sturm
            row["gain_inverse"] = {"G_grid15": str(gain["G"]), "G_enclosure": gain["G_enclosure"].packet(),
                                    "balanced_n_grid15": str(gain["n_grid"]), "balanced_n_enclosure": gain["n"].packet(),
                                    "balanced_n_from_unrounded_G": gain["n_source_enclosure"].packet(),
                                    "q_reference_readback": gain["reference_q"].packet(), "iterations": gain["steps"]}
            if not roots:
                row["status"] = "MODEL_INPUT_REJECTED"
            else:
                for root in roots:
                    source = {**gain, "TA": root["TA"], "TB": root["TB"], "allocation": point["allocation"],
                              "source_id": point["point_id"] + "/root" + str(root["root_index"])}
                    c, fringe = coherence_inverse(symbolic, gain["n"], source["TA"], source["TB"],
                                                   inputs["DA_raw_visibility"], point["allocation"], spec)
                    source["c"] = c
                    probes, readback = born_probes(source, spec)
                    targets = {"K_A": F(inputs["K_A"]), "K_B": F(inputs["K_B"]),
                               "DA_raw_visibility": F(inputs["DA_raw_visibility"])}
                    require(all(endpoint_gap(readback[name], value) <= TOL for name, value in targets.items()), "actual_source_readback_failed")
                    require(readback["DA_raw_visibility"].width <= TOL and
                            F(spec["HV_raw_visibility"]["box_low"]) <= readback["HV_raw_visibility"].lo and
                            readback["HV_raw_visibility"].hi <= F(spec["HV_raw_visibility"]["box_high"]), "actual_visibility_readback_failed")
                    require(overlap_gap(readback["HV_raw_visibility"], I(fringe["HV_visibility"]["exact_lower"],
                                                                         fringe["HV_visibility"]["exact_upper"])) <= TOL and
                            overlap_gap(readback["DA_raw_visibility"], I(fringe["DA_visibility"]["exact_lower"],
                                                                         fringe["DA_visibility"]["exact_upper"])) <= TOL, "symbolic_native_fringe_identity_failed")
                    row["sources"].append({"source": source_as_json(source), "fringe_certificate": fringe,
                                           "source_readback": {k: v.packet() for k, v in readback.items()},
                                           "target_gaps": {k: str(endpoint_gap(readback[k], v)) for k, v in targets.items()},
                                           "coherent_occupation_Born_probes": probes, "status": "SOURCE_GENERATED"})
                row["status"] = "SOURCE_GENERATED"
        except ValueError as error:
            row["status"] = "UNRESOLVED"
            row["reason"] = str(error)
        rows.append(row)
        if progress:
            print("nominal calibration " + point["point_id"] + " " + row["status"], file=sys.stderr, flush=True)
    generated = [source for row in rows for source in row["sources"]]
    complete = all(row["status"] == "SOURCE_GENERATED" for row in rows)
    checks = {"criterion_text_and_machine_efficiency_units": units["public_text_and_machine_block_agree"],
              "nineteen_point_inventory": len(rows) == 19,
              "seventeen_default_sources_separate_from_overrides": all(row["allocation"] == "symmetric" for row in rows[:17]) and
                    [row["allocation"] for row in rows[17:]] == spec["center_allocation_overrides"],
              "complete_real_Sturm_root_isolation": all(row.get("K_inverse", {}).get("full_real_cover") is True for row in rows),
              "all_physical_roots_preserved": all(len(row["sources"]) == row.get("K_inverse", {}).get("physical_root_count", -1) for row in rows),
              "all_points_source_generated": complete,
              "full_fringe_certified_before_endpoints": complete and all(s["fringe_certificate"]["full_fringe_extrema_generated_before_endpoint_readout"]
                                                                         for s in generated),
              "raw_visibility_not_assigned_to_overlap": complete and all(s["fringe_certificate"]["coherence_is_visibility_input"] is False
                                                                         for s in generated),
              "all_calibration_and_reference_Born_probes": complete and all(len(s["coherent_occupation_Born_probes"]) == 8 and
                        all(p["comparison_passed"] is True for p in s["coherent_occupation_Born_probes"]) for s in generated),
              "source_phase_and_environment_fixed_across_preparation": complete and all(s["source"]["phase"] == ["1", "0"] and
                        s["source"]["same_gain_for_all_preparations"] is True for s in generated),
              "no_prefix_renormalization": complete and all(p["prefix_renormalized"] is False for s in generated for p in s["coherent_occupation_Born_probes"])}
    return {"schema": SCHEMA, "version": VERSION, "criterion_freeze": FREEZE, "bindings": bindings,
            "efficiency_unit_readback": units, "precision_digits": 40, "pi_interval": [str(x) for x in born.PI],
            "trig_terms": 14, "hyperbolic_terms": 24, "source_grid_digits": 15,
            "Sturm_root_interval_max_width": str(STURM_WIDTH), "coherence_root_interval_max_width": str(COHERENCE_WIDTH),
            "native_fringe_symbolic_denominators": {basis: {k: p.packet() for k, p in polynomials.items()}
                                                    for basis, polynomials in symbolic.items()},
            "rows": rows, "checks": checks, "passed": all(checks.values()),
            "outcome": "NOMINAL_FIXED_ENVIRONMENT_CALIBRATION_SOURCE_GENERATED" if all(checks.values()) else "UNRESOLVED",
            **{key: False for key in FLAGS}, "publication_configuration_identified": False,
            "retrospective": True, "event_files_read": 0,
            "published_r_angles_or_Table_SII_used_as_inverse_inputs": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "calibration-independent.json")
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    require(args.check_only or not args.output.exists(), "first_calibration_receipt_already_exists")
    report = generate()
    raw = (json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()
    if args.check_only:
        sys.stdout.buffer.write(raw)
    else:
        args.output.write_bytes(raw)
        print(json.dumps({"path": str(args.output), "sha256": hashlib.sha256(raw).hexdigest(),
                          "passed": report["passed"], "outcome": report["outcome"]}), flush=True)
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
