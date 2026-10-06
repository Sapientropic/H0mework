#!/usr/bin/env python3
"""Native six-port source effects and complete Gaussian threshold counts."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[7]
VERSION = "p23-environment-count-evg0001"
SCHEMA = "p23-environment-source-counts/v1"
CONTRACT_COMMIT = "75ecac81d9"
DIGITS = 40
SCALE = 10 ** DIGITS
TOL = F("1e-12")
PI = (F("3.14159265358979323846"), F("3.14159265358979323847"))
FALSE_FLAGS = ("source_mapping_identified", "new_full_Born_or_Gaussian_determinant_kernel_claim",
               "full_fringe_extrema_certified", "apparatus_optimum_verified", "controller_advance")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def rational(value):
    require(type(value) in (str, int, F), "nonliteral_or_boolean_rational")
    return F(value)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frozen(path, commit=None):
    path = Path(path).resolve()
    name = path.relative_to(ROOT).as_posix()
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", name],
                                         cwd=ROOT, text=True).strip()
    require(bool(commit), "UNFROZEN_SOURCE:" + name)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    require(subprocess.check_output(["git", "show", commit + ":" + name], cwd=ROOT) == path.read_bytes(),
            "UNFROZEN_SOURCE:" + name)
    return {"path": name, "commit": commit, "sha256": digest(path)}


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    def __init__(self, lo=0, hi=None):
        lo, hi = F(lo), F(lo if hi is None else hi)
        require(lo <= hi, "reversed_interval")
        object.__setattr__(self, "lo", lo)
        object.__setattr__(self, "hi", hi)

    @staticmethod
    def of(value):
        return value if isinstance(value, I) else I(value)

    @staticmethod
    def outward(lo, hi):
        a, b = F(lo) * SCALE, F(hi) * SCALE
        return I(F(a.numerator // a.denominator, SCALE),
                 F(-((-b.numerator) // b.denominator), SCALE))

    def __add__(self, other):
        other = I.of(other)
        return I.outward(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -I.of(other)

    def __rsub__(self, other):
        return I.of(other) - self

    def __mul__(self, other):
        other = I.of(other)
        p = (self.lo * other.lo, self.lo * other.hi,
             self.hi * other.lo, self.hi * other.hi)
        return I.outward(min(p), max(p))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = I.of(other)
        require(not other.lo <= 0 <= other.hi, "interval_division_through_zero")
        return self * I.outward(1 / other.hi, 1 / other.lo)

    def __rtruediv__(self, other):
        return I.of(other) / self

    def square(self):
        return I.outward(0 if self.contains(0) else min(self.lo ** 2, self.hi ** 2),
                         max(self.lo ** 2, self.hi ** 2))

    def __pow__(self, n):
        require(type(n) is int and n >= 0, "invalid_interval_power")
        if n == 0:
            return I(1)
        if n % 2 == 0:
            return self.square() ** (n // 2)
        return self * (self ** (n - 1))

    def sqrt(self):
        require(self.lo >= 0, "negative_square_root")
        def floor(value):
            return math.isqrt(value.numerator * SCALE * SCALE // value.denominator)
        low, high = floor(self.lo), floor(self.hi)
        upper = F(high, SCALE)
        if upper * upper < self.hi:
            upper += F(1, SCALE)
        return I(F(low, SCALE), upper)

    def contains(self, value):
        return self.lo <= F(value) <= self.hi

    @property
    def width(self):
        return self.hi - self.lo

    def packet(self):
        return {"lower": float(self.lo), "upper": float(self.hi),
                "exact_lower": str(self.lo), "exact_upper": str(self.hi)}


@dataclass(frozen=True)
class C:
    re: I
    im: I

    def __init__(self, re=0, im=0):
        object.__setattr__(self, "re", I.of(re))
        object.__setattr__(self, "im", I.of(im))

    @staticmethod
    def of(value):
        return value if isinstance(value, C) else C(value)

    def __add__(self, other):
        other = C.of(other)
        return C(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self):
        return C(-self.re, -self.im)

    def __sub__(self, other):
        return self + -C.of(other)

    def __rsub__(self, other):
        return C.of(other) - self

    def __mul__(self, other):
        other = C.of(other)
        return C(self.re * other.re - self.im * other.im,
                 self.re * other.im + self.im * other.re)

    __rmul__ = __mul__

    def __truediv__(self, real):
        require(not isinstance(real, C), "complex_divisor_not_used_by_this_consumer")
        return C(self.re / real, self.im / real)

    def conjugate(self):
        return C(self.re, -self.im)

    def packet(self):
        return {"real": self.re.packet(), "imaginary": self.im.packet()}


def real_part(value, reason):
    value = C.of(value)
    require(value.im.contains(0) and value.im.width <= TOL, reason + ":nonreal")
    return value.re


def near_zero(value):
    value = C.of(value)
    return (value.re.contains(0) and value.im.contains(0) and
            value.re.width <= TOL and value.im.width <= TOL)


def trig_sin_cos(degrees):
    degrees = rational(degrees)
    degrees %= 360
    if degrees > 180:
        degrees -= 360
    sign_sin, sign_cos = 1, 1
    if degrees > 90:
        degrees = 180 - degrees
        sign_cos = -1
    elif degrees < -90:
        degrees = -180 - degrees
        sign_cos = -1
    if degrees < 0:
        degrees = -degrees
        sign_sin = -1
    x = I(*PI) * (degrees / 180)
    sine, cosine = I(0), I(0)
    for k in range(12):
        sine += ((-1) ** k) * (x ** (2 * k + 1)) / math.factorial(2 * k + 1)
        cosine += ((-1) ** k) * (x ** (2 * k)) / math.factorial(2 * k)
    sine_error = x.hi ** 25 / math.factorial(25)
    cosine_error = x.hi ** 24 / math.factorial(24)
    return (sign_sin * (sine + I(-sine_error, sine_error)),
            sign_cos * (cosine + I(-cosine_error, cosine_error)))


def complex_literal(value, field):
    require(type(value) is list and len(value) == 2, "invalid_complex_literal:" + field)
    a, b = map(rational, value)
    return (a, b), C(a, b)


def fixture(value):
    require(type(value) is dict, "fixture_not_object")
    expected = {"id", "tH", "tV", "phase", "TA", "TB", "xiA", "xiB", "angles"}
    require(set(value) == expected, "fixture_field_set_changed")
    require(type(value["id"]) is str and bool(value["id"]), "invalid_fixture_id")
    th, tv = rational(value["tH"]), rational(value["tV"])
    require(0 <= th < 1 and 0 <= tv < 1, "geometric_ratio_out_of_domain")
    phase_raw, phase = complex_literal(value["phase"], "phase")
    require(sum(x * x for x in phase_raw) == 1, "nonunit_source_phase")
    result = {"id": value["id"], "tH": th, "tV": tv, "phase": phase,
              "phase_raw": phase_raw, "literal": value}
    for arm in ("A", "B"):
        require(type(value["T" + arm]) is list and len(value["T" + arm]) == 2,
                "invalid_polarization_loss_pair")
        losses = tuple(map(rational, value["T" + arm]))
        require(all(0 <= t <= 1 for t in losses), "transmission_out_of_domain")
        xi_raw, xi = complex_literal(value["xi" + arm], "xi" + arm)
        norm = sum(x * x for x in xi_raw)
        require(norm <= 1, "environment_overlap_out_of_domain")
        result[arm] = {"transmissions": losses, "xi": xi, "xi_normSq": norm,
                       "xi_raw": xi_raw}
    require(type(value["angles"]) is list and len(value["angles"]) == 2,
            "invalid_angle_pair")
    result["angles"] = tuple(map(rational, value["angles"]))
    return result


def six_rows(station, sine, cosine):
    th, tv = station["transmissions"]
    h, v = I(th).sqrt(), I(tv).sqrt()
    xi = station["xi"]
    r = I(1 - station["xi_normSq"]).sqrt()
    return ((C(h * sine), xi * (v * cosine)),
            (C(0), C(v * r * cosine)),
            (C(h * cosine), -xi * (v * sine)),
            (C(0), C(-v * r * sine)),
            (C(I(1 - th).sqrt()), C(0)),
            (C(0), C(I(1 - tv).sqrt())))


def gram(rows):
    return tuple(tuple(sum((row[i].conjugate() * row[j] for row in rows), C())
                       for j in range(2)) for i in range(2))


def identity():
    return ((C(1), C(0)), (C(0), C(1)))


def mm(a, b):
    return tuple(tuple(sum((a[i][k] * b[k][j] for k in range(2)), C())
                       for j in range(2)) for i in range(2))


def transpose(a):
    return tuple(zip(*a))


def adjoint(a):
    return tuple(tuple(a[j][i].conjugate() for j in range(2)) for i in range(2))


def matrix_sub(a, b):
    return tuple(tuple(a[i][j] - b[i][j] for j in range(2)) for i in range(2))


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def matrix_packet(a):
    return [[v.packet() for v in row] for row in a]


def source(value):
    th, tv = value["tH"], value["tV"]
    d = ((C(I(th).sqrt()), C(0)),
         (C(0), value["phase"] * I(tv).sqrt()))
    z = (1 - th) * (1 - tv)
    masses = [z * sum(th ** h * tv ** (n - h) for h in range(n + 1)) for n in range(7)]
    tail = 1 - sum(masses)
    require(tail >= 0, "negative_source_tail")
    return d, z, {"geometric_ratio": [str(th), str(tv)], "source_phase": value["phase"].packet(),
                  "Z": I(z).packet(), "sector_mass_0_through_6": [I(x).packet() for x in masses],
                  "total_pair_prefix": 6, "prefix_renormalized": False,
                  "numberMass_tail": I(tail).packet(), "paired_D": matrix_packet(d)}


def gaussian_no_click(d, z, xa, xb, *, wrong_bob=False):
    dagger = adjoint(d)
    da = mm(mm(dagger, xa), d)
    bob = xb if wrong_bob else transpose(xb)
    db = mm(mm(dagger, d), bob)
    dab = mm(da, bob)
    probabilities, denominators = {}, {}
    for name, matrix in (("A", da), ("B", db), ("AB", dab)):
        denominator = det(matrix_sub(identity(), matrix))
        real = real_part(denominator, "Gaussian_denominator_" + name)
        require(real.lo > 0, "nonpositive_Gaussian_denominator:" + name)
        probabilities[name] = z / real
        denominators[name] = denominator
    return probabilities, denominators


def window(probabilities, pulses):
    require(type(pulses) is int and pulses in (1, 5), "unregistered_window_count")
    pa, pb, pab = (probabilities[k] ** pulses for k in ("A", "B", "AB"))
    outcomes = {"++": 1 - pa - pb + pab, "+0": pb - pab,
                "0+": pa - pab, "00": pab}
    require(all(x.lo >= -TOL and x.hi <= 1 + TOL for x in outcomes.values()),
            "outcome_outside_physical_probability_domain")
    require(near_zero(C(sum(outcomes.values(), I(0)) - 1)), "outcome_normalization_unresolved")
    return outcomes


def actual_station(station, angle):
    sine, cosine = trig_sin_cos(angle)
    rows = six_rows(station, sine, cosine)
    clicked, no_click, complete = gram(rows[:2]), gram(rows[2:]), gram(rows)
    require(all(near_zero(complete[i][j] - identity()[i][j]) for i in range(2) for j in range(2)),
            "six_port_isometry_unresolved")
    require(all(near_zero(clicked[i][j] + no_click[i][j] - identity()[i][j])
                for i in range(2) for j in range(2)), "click_no_click_complement_unresolved")
    return {"rows": rows, "clicked": clicked, "no_click": no_click,
            "complete": complete, "sine": sine, "cosine": cosine}


def evaluate(raw):
    value = fixture(raw)
    d, z, source_receipt = source(value)
    arms = {arm: actual_station(value[arm], angle)
            for arm, angle in zip(("A", "B"), value["angles"])}
    no_click, denominators = gaussian_no_click(d, z, arms["A"]["no_click"], arms["B"]["no_click"])
    require(all(p.width <= TOL for p in no_click.values()), "Gaussian_readout_width_unresolved")
    windows = {str(n): window(no_click, n) for n in (1, 5)}
    return value, arms, no_click, windows, {
        "input": raw, "source": source_receipt,
        "station_ports": {arm: {"six_rows_HV_columns": matrix_packet(a["rows"]),
            "clicked_Gram": matrix_packet(a["clicked"]), "no_click_Gram": matrix_packet(a["no_click"]),
            "six_port_Gram": matrix_packet(a["complete"]), "six_port_isometry_verified": True,
            "click_no_click_complement_verified": True} for arm, a in arms.items()},
        "Gaussian_denominators": {k: v.packet() for k, v in denominators.items()},
        "pulse_no_click": {k: v.packet() for k, v in no_click.items()},
        "windows": {k: {label: p.packet() for label, p in w.items()} for k, w in windows.items()},
        "fresh_pulse_OR": True, "background_per_pulse": ["0", "0"],
        "arithmetic_probability_clipping_used": False}


def pair_click(value, arms, *, wrong_bob=False):
    d, _, _ = source(value)
    coefficients = (d[0][0], d[1][1])
    total = value["tH"] + value["tV"]
    require(total > 0, "single_pair_conditioning_vacuum")
    ea, eb = arms["A"]["clicked"], arms["B"]["clicked"]
    result = C()
    for i in range(2):
        for j in range(2):
            bob = eb[j][i] if wrong_bob else eb[i][j]
            result += coefficients[i].conjugate() * coefficients[j] * ea[i][j] * bob
    return real_part(result, "conditioned_single_pair_click") / total


def rank_one_reference(value, arms):
    require(all(t[0] == t[1] for t in (value["A"]["transmissions"], value["B"]["transmissions"])),
            "rank_one_reference_requires_scalar_loss")
    require(value["phase_raw"] == (1, 0), "rank_one_reference_fixed_phase")
    nh, nv = (value[k] / (1 - value[k]) for k in ("tH", "tV"))
    ta, tb = value["A"]["transmissions"][0], value["B"]["transmissions"][0]
    sa, ca = arms["A"]["sine"], arms["A"]["cosine"]
    sb, cb = arms["B"]["sine"], arms["B"]["cosine"]
    ma, mb = ta * (nh * sa.square() + nv * ca.square()), tb * (nh * sb.square() + nv * cb.square())
    correlation = ta * tb * (I(nh * (1 + nh)).sqrt() * sa * sb +
                              I(nv * (1 + nv)).sqrt() * ca * cb).square()
    return {"A": 1 / (1 + ma), "B": 1 / (1 + mb),
            "AB": 1 / ((1 + ma) * (1 + mb) - correlation)}


def controls(results):
    value, arms, p, _, _ = results["rank_one"]
    reference = rank_one_reference(value, arms)
    rank_diffs = {k: p[k] - reference[k] for k in p}
    require(all(near_zero(C(x)) for x in rank_diffs.values()), "rank_one_limit_disagrees")
    value, arms, _, w, _ = results["complex_transpose"]
    single_correct = pair_click(value, arms)
    single_wrong = pair_click(value, arms, wrong_bob=True)
    d, z, _ = source(value)
    wrong, _ = gaussian_no_click(d, z, arms["A"]["no_click"], arms["B"]["no_click"], wrong_bob=True)
    wrong_joint = window(wrong, 1)["++"]
    t = value["tH"]
    require(near_zero(C(single_correct)) and near_zero(C(single_wrong - F(1, 2))),
            "complex_transpose_single_pair_control_failed")
    require(near_zero(C(w["1"]["++"] - t * t)) and near_zero(C(wrong_joint - t)),
            "complex_transpose_full_source_control_failed")
    a = results["same_product_one_side"]
    b = results["same_product_split"]
    product_difference = pair_click(a[0], a[1]) - pair_click(b[0], b[1])
    bucket_difference = a[2]["A"] - b[2]["A"]
    require(near_zero(C(product_difference)) and bucket_difference.lo > 0,
            "same_single_pair_product_was_collapsed_in_bucket_law")
    unequal = results["unequal_polarization_losses"]
    flattened = json.loads(json.dumps(unequal[0]["literal"]))
    for arm in ("A", "B"):
        mean = sum(unequal[0][arm]["transmissions"]) / 2
        flattened["T" + arm] = [str(mean), str(mean)]
    fake = evaluate(flattened)
    unequal_difference = unequal[2]["A"] - fake[2]["A"]
    require(not unequal_difference.contains(0), "unequal_polarization_losses_collapsed")
    for name in ("vacuum", "all_lost"):
        for n in ("1", "5"):
            for label, probability in results[name][3][n].items():
                require(near_zero(C(probability - (1 if label == "00" else 0))),
                        name + "_full_outcome_control_failed")
    vacuum_clicked = real_part(det(results["vacuum"][1]["A"]["clicked"]), "xi_zero_clicked_Gram")
    require(vacuum_clicked.lo > 0, "xi_zero_second_click_environment_port_missing")
    return {"old_scalar_rank_one_limit_verified": True,
        "rank_one_no_click_differences": {k: x.packet() for k, x in rank_diffs.items()},
        "complex_transpose": {"conditioned_single_pair_correct": single_correct.packet(),
            "conditioned_single_pair_wrong": single_wrong.packet(), "full_joint_correct": w["1"]["++"].packet(),
            "full_joint_wrong": wrong_joint.packet(), "wrong_Bob_transpose_detected": True},
        "same_product": {"conditioned_single_pair_difference": product_difference.packet(),
            "local_no_click_difference": bucket_difference.packet(), "product_only_shortcut_detected": True},
        "unequal_polarization_losses": {"local_no_click_difference_from_scalarized_losses": unequal_difference.packet(),
            "scalarization_detected": True, "source_phase_i_preserved": True},
        "vacuum_complete_outcomes_verified": True, "all_lost_complete_outcomes_verified": True,
        "xi_zero_clicked_Gram_determinant": vacuum_clicked.packet(), "xi_zero_two_click_ports_verified": True}


def ptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1].re.lo == p[-1].re.hi == p[-1].im.lo == p[-1].im.hi == 0:
        p.pop()
    return p


def padd(a, b):
    return ptrim([(a[i] if i < len(a) else C()) + (b[i] if i < len(b) else C())
                  for i in range(max(len(a), len(b)))])


def pscale(a, k):
    return ptrim([x * k for x in a])


def pmul(a, b):
    out = [C() for _ in range(len(a) + len(b) - 1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return ptrim(out)


def pconjugate(a):
    return [x.conjugate() for x in a]


def pmm(a, b):
    return [[padd(pmul(a[i][0], b[0][j]), pmul(a[i][1], b[1][j])) for j in range(2)] for i in range(2)]


def pdet(a):
    return padd(pmul(a[0][0], a[1][1]), pscale(pmul(a[0][1], a[1][0]), -1))


def polynomial_packet(p):
    return [real_part(x, "fringe_polynomial_coefficient").packet() for x in p]


def peval(p, q):
    value = C()
    for coefficient in reversed(p):
        value = value * q + coefficient
    return value


def fringe_polynomials(value, arms, no_click):
    h, v = (I(x).sqrt() for x in value["A"]["transmissions"])
    xi = value["A"]["xi"]
    r = I(1 - value["A"]["xi_normSq"]).sqrt()
    # Polynomial numerators of the actual two clicked rows, divided by sqrt(1+q^2).
    rows = (([C(), C(h)], [xi * v]), ([C()], [C(v * r)]))
    clicked = [[padd(pmul(pconjugate(rows[0][i]), rows[0][j]),
                      pmul(pconjugate(rows[1][i]), rows[1][j])) for j in range(2)] for i in range(2)]
    w = [C(1), C(), C(1)]
    iw = [[w, [C()]], [[C()], w]]
    xa = [[padd(iw[i][j], pscale(clicked[i][j], -1)) for j in range(2)] for i in range(2)]
    d, z, _ = source(value)
    dp = [[[x] for x in row] for row in d]
    dagger = [[[x] for x in row] for row in adjoint(d)]
    da = pmm(pmm(dagger, xa), dp)
    bob = [[[x] for x in row] for row in transpose(arms["B"]["no_click"])]
    dab = pmm(da, bob)
    qa = pdet([[padd(iw[i][j], pscale(da[i][j], -1)) for j in range(2)] for i in range(2)])
    qab = pdet([[padd(iw[i][j], pscale(dab[i][j], -1)) for j in range(2)] for i in range(2)])
    denominator = pmul(qa, qab)
    ww = pmul(w, w)
    numerator = padd(pscale(denominator, 1 - no_click["B"]),
                     padd(pscale(pmul(ww, qab), -z), pscale(pmul(ww, qa), z)))
    # The i=j coefficient vanishes algebraically; no interval threshold removes the degree-15 term.
    derivative = [C() for _ in range(max(1, len(numerator) + len(denominator) - 2))]
    for i, x in enumerate(numerator):
        for j, y in enumerate(denominator):
            if i != j:
                derivative[i + j - 1] += (i - j) * x * y
    derivative = ptrim(derivative)
    degrees = {"QA": len(qa) - 1, "QAB": len(qab) - 1,
               "joint_numerator": len(numerator) - 1, "joint_denominator": len(denominator) - 1,
               "derivative_numerator": len(derivative) - 1}
    require(degrees["QA"] <= 4 and degrees["QAB"] <= 4 and
            degrees["joint_numerator"] <= 8 and degrees["joint_denominator"] <= 8 and
            degrees["derivative_numerator"] <= 14, "general_Gram_fringe_degree_cap_exceeded")
    probes = []
    for q in (F(0), F(1), F(-1), F(1, 3)):
        root = I(1 + q * q).sqrt()
        a_rows = six_rows(value["A"], I(q) / root, 1 / root)
        direct, _ = gaussian_no_click(d, z, gram(a_rows[2:]), arms["B"]["no_click"])
        direct_joint = window(direct, 1)["++"]
        polynomial_joint = real_part(peval(numerator, q), "fringe_numerator_eval") / real_part(
            peval(denominator, q), "fringe_denominator_eval")
        residual = direct_joint - polynomial_joint
        require(near_zero(C(residual)), "q_fringe_native_rows_disagree")
        probes.append({"q": str(q), "native_joint": direct_joint.packet(),
                       "polynomial_joint": polynomial_joint.packet(), "difference": residual.packet()})
    inf_rows = six_rows(value["A"], I(1), I(0))
    inf_direct, _ = gaussian_no_click(d, z, gram(inf_rows[2:]), arms["B"]["no_click"])
    require(len(numerator) <= len(denominator), "unbounded_fringe_at_infinity")
    infinity_numerator = numerator[-1] if len(numerator) == len(denominator) else C()
    infinity_joint = real_part(infinity_numerator, "fringe_infinity_numerator") / real_part(
        denominator[-1], "fringe_infinity_denominator")
    infinity_difference = window(inf_direct, 1)["++"] - infinity_joint
    require(near_zero(C(infinity_difference)), "q_infinity_native_rows_disagree")
    return {"parameter": "q=tan(Alice angle)", "source_unchanged": True,
        "balanced_source": value["tH"] == value["tV"], "fixed_Bob_degrees": str(value["angles"][1]),
        "coefficient_order": "ascending powers of q", "coefficient_domain": "real rational outward intervals",
        "QA": polynomial_packet(qa), "QAB": polynomial_packet(qab),
        "joint_numerator": polynomial_packet(numerator), "joint_denominator": polynomial_packet(denominator),
        "derivative_numerator": polynomial_packet(derivative), "degrees": degrees,
        "degree_15_cancelled_algebraically": True, "native_row_probes": probes,
        "q_infinity_joint": infinity_joint.packet(), "q_infinity_native_difference": infinity_difference.packet(),
        "extrema_search_performed": False, "full_fringe_extrema_certified": False}


def inputs():
    program = frozen(__file__)
    criterion = frozen(HERE / "numeric-criterion.md", CONTRACT_COMMIT)
    manifest_freeze = frozen(HERE / "numeric-sources.json", CONTRACT_COMMIT)
    subprocess.run(["git", "merge-base", "--is-ancestor", CONTRACT_COMMIT, program["commit"]],
                   cwd=ROOT, check=True)
    blocks = re.findall(r"```json\s*(.*?)\s*```", (HERE / "numeric-criterion.md").read_text(), re.S)
    require(len(blocks) == 1, "nonunique_environment_count_contract")
    config = json.loads(blocks[0])
    manifest = json.loads((HERE / "numeric-sources.json").read_text())
    require(config["version"] == manifest["version"] == VERSION and
            config["status"] == manifest["status"] == "frozen_before_execution", "wrong_environment_count_contract")
    require(type(config["precision_digits"]) is int and config["precision_digits"] == DIGITS and
            rational(config["implementation_tolerance"]) == TOL and
            type(config["total_pair_prefix"]) is int and config["total_pair_prefix"] == 6 and
            config["prefix_renormalized"] is False and config["window_pulse_probes"] == [1, 5] and
            config["background_per_pulse"] == ["0", "0"] and config["full_fringe_derivative_degree_cap"] == 14,
            "environment_count_precision_or_scope_changed")
    require(all(config[k] is False for k in FALSE_FLAGS) and
            manifest["actual_source_or_hardware_identity_verified"] is False and
            manifest["new_full_Born_or_Gaussian_determinant_kernel_claim"] is False and
            config["event_files_read"] == manifest["event_files_read"] == 0,
            "environment_count_claim_scope_changed")
    bindings = {}
    for row in manifest["inputs"]:
        path = (ROOT / row["path"]).resolve()
        require(path.is_relative_to(ROOT) and digest(path) == row["sha256"], "environment_input_binding_changed")
        frozen(path)
        bindings[row["path"]] = row["sha256"]
    parsed = [fixture(x) for x in config["fixtures"]]
    require(len(parsed) == 8 and len({x["id"] for x in parsed}) == 8, "environment_fixture_inventory_changed")
    return config, bindings, {"criterion": criterion, "manifest": manifest_freeze, "program": program}


def run():
    start = time.monotonic()
    config, bindings, freeze = inputs()
    results = {raw["id"]: evaluate(raw) for raw in config["fixtures"]}
    control = controls(results)
    fringes = {name: fringe_polynomials(item[0], item[1], item[2]) for name, item in results.items()}
    return {"schema": SCHEMA, "version": VERSION, "status": "verified_numeric_source_count_readout",
        "freeze": freeze, "source_bindings": bindings, "precision_digits": DIGITS,
        "pi_interval": [str(x) for x in PI], "trigonometric_terms": 12,
        "implementation_tolerance": str(TOL), "method": "six_row_Grams_and_same_pair_D_Gaussian_determinants",
        "complex_arithmetic": "pairs of exact rational outward real intervals",
        "matrix_coordinate_order": ["H", "V"], "Bob_operation": "ordinary_transpose",
        "fixture_order": [x["id"] for x in config["fixtures"]],
        "fixtures": {name: result[4] for name, result in results.items()},
        "controls": control, "fringe_polynomials": fringes,
        "all_eight_fixtures_verified": True, "all_N1_N5_complete_outcomes_verified": True,
        "source_generated_general_fringe_coefficients_verified": True,
        "independence": {"foreign_new_science_program_read": False, "foreign_new_science_output_read": False,
                         "comparison_performed": False, "first_receipt_protected": True},
        "prior_rank_one_inverse_gain_admitted": False, "fixtures_are_actual_calibration_data": False,
        **{name: False for name in FALSE_FLAGS}, "actual_source_or_hardware_identity_verified": False,
        "global_optimum_kernel_proof": False, "event_files_read": 0, "retrospective": True,
        "runtime_seconds": time.monotonic() - start}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "counts-primary.json")
    args = parser.parse_args()
    require(not args.output.exists(), "protected_existing_scientific_receipt")
    report = run()
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": report["status"], "fixtures": len(report["fixtures"]),
                      "N1_N5_complete_outcomes": True, "fringe_degree_bound": 14,
                      "output": str(args.output), "sha256": digest(args.output)}))


if __name__ == "__main__":
    main()
