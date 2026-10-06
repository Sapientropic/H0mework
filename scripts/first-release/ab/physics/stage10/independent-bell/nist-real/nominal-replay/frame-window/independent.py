#!/usr/bin/env python3
"""Independent coherent Fock source, coupled calibration and full-fringe enclosure."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import itertools
import json
import math
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
CONTRACT = "4c86dd68e7"
VERSION = "p23-frame-window-fw0001"
DIGITS = 40
SCALE = 10 ** DIGITS
PI_LO = F("3.14159265358979323846")
PI_HI = F("3.14159265358979323847")
FLAGS = ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
         "actual_window_model_identified", "calibration_protocol_identified", "noise_channel_identified",
         "source_pair_rate_reference_identified", "common_Jones_map_identified",
         "equal_branch_conversion_identified", "actual_pump_actuator_identified")


def require(value, reason):
    if not value:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frozen(path, commit=None):
    path = Path(path).resolve()
    rel = str(path.relative_to(ROOT))
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", rel], cwd=ROOT,
                                         text=True).strip()
    require(bool(commit), "uncommitted_independent_candidate")
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    blob = subprocess.check_output(["git", "show", commit + ":" + rel], cwd=ROOT)
    require(blob == path.read_bytes(), "unfrozen_independent_candidate:" + rel)
    return {"commit": commit, "path": rel, "sha256": digest(path)}


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    def __init__(self, lo, hi=None):
        lo, hi = F(lo), F(lo if hi is None else hi)
        require(lo <= hi, "reversed_interval")
        object.__setattr__(self, "lo", lo)
        object.__setattr__(self, "hi", hi)

    @staticmethod
    def outward(lo, hi):
        lo, hi = F(lo), F(hi)
        return I(F((lo * SCALE).numerator // (lo * SCALE).denominator, SCALE),
                 F(-((-hi * SCALE).numerator // (-hi * SCALE).denominator), SCALE))

    @staticmethod
    def of(x):
        return x if isinstance(x, I) else I(x)

    def __add__(self, other):
        b = I.of(other)
        return I.outward(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-I.of(other))

    def __rsub__(self, other):
        return I.of(other) - self

    def __mul__(self, other):
        b = I.of(other)
        values = (self.lo * b.lo, self.lo * b.hi, self.hi * b.lo, self.hi * b.hi)
        return I.outward(min(values), max(values))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = I.of(other)
        require(not b.lo <= 0 <= b.hi, "interval_division_through_zero")
        return self * I.outward(1 / b.hi, 1 / b.lo)

    def __rtruediv__(self, other):
        return I.of(other) / self

    def square(self):
        return I.outward(0 if self.lo <= 0 <= self.hi else min(self.lo ** 2, self.hi ** 2),
                         max(self.lo ** 2, self.hi ** 2))

    def power(self, n):
        if n == 0:
            return I(1)
        if n % 2 == 0:
            return self.square().power(n // 2)
        return self * self.power(n - 1)

    __pow__ = power

    def sqrt(self):
        require(self.lo >= 0, "negative_square_root")
        def floor(x):
            return math.isqrt(x.numerator * SCALE * SCALE // x.denominator)
        left, right = floor(self.lo), floor(self.hi)
        upper = F(right, SCALE)
        if upper * upper < self.hi:
            upper += F(1, SCALE)
        return I(F(left, SCALE), upper)

    @property
    def width(self):
        return self.hi - self.lo

    def midpoint(self):
        return (self.lo + self.hi) / 2

    def packet(self):
        return {"lower": float(self.lo), "upper": float(self.hi),
                "exact_lower": str(self.lo), "exact_upper": str(self.hi)}

    def contained(self, lo, hi):
        return F(lo) <= self.lo and self.hi <= F(hi)


@dataclass(frozen=True)
class Q:
    """One exact ordered quadratic field; no floating sign decisions."""
    a: F
    b: F
    d: F

    def __init__(self, a, b=0, d=0):
        a, b, d = F(a), F(b), F(d)
        require(d >= 0, "negative_quadratic_discriminant")
        nr, dr = math.isqrt(d.numerator), math.isqrt(d.denominator)
        if nr * nr == d.numerator and dr * dr == d.denominator:
            a, b = a + b * F(nr, dr), F(0)
        object.__setattr__(self, "a", a)
        object.__setattr__(self, "b", b)
        object.__setattr__(self, "d", d)

    def coerce(self, x):
        if isinstance(x, Q):
            require(x.d == self.d or x.b == 0, "mixed_quadratic_fields")
            if x.d != self.d:
                return Q(x.a, 0, self.d)
            return x
        return Q(x, 0, self.d)

    def __add__(self, x):
        x = self.coerce(x)
        return Q(self.a + x.a, self.b + x.b, self.d)

    __radd__ = __add__

    def __neg__(self):
        return Q(-self.a, -self.b, self.d)

    def __sub__(self, x):
        return self + (-self.coerce(x))

    def __rsub__(self, x):
        return self.coerce(x) - self

    def __mul__(self, x):
        x = self.coerce(x)
        return Q(self.a * x.a + self.b * x.b * self.d,
                 self.a * x.b + self.b * x.a, self.d)

    __rmul__ = __mul__

    def __truediv__(self, x):
        x = self.coerce(x)
        norm = x.a * x.a - x.b * x.b * self.d
        require(norm != 0, "zero_quadratic_divisor")
        return self * Q(x.a / norm, -x.b / norm, self.d)

    def __rtruediv__(self, x):
        return self.coerce(x) / self

    @lru_cache(maxsize=65536)
    def sign(self):
        if self.b == 0:
            return (self.a > 0) - (self.a < 0)
        if self.a == 0 or (self.a > 0) == (self.b > 0):
            return (self.b > 0) - (self.b < 0)
        difference = self.a * self.a - self.b * self.b * self.d
        if difference == 0:
            return 0
        return ((self.a > 0) - (self.a < 0)) if difference > 0 else ((self.b > 0) - (self.b < 0))

    @lru_cache(maxsize=16384)
    def interval(self):
        # The conjugate Klyshko branch makes high-sector coefficient pairs large.
        # Enclose the radical before multiplying, then round the final field value.
        guard = DIGITS + 12 + max(0, len(str(abs(self.b.numerator))) - len(str(self.b.denominator)) + 1)
        scale = 10 ** guard
        root = math.isqrt(self.d.numerator * scale * scale // self.d.denominator)
        left = F(root, scale)
        right = left if left * left == self.d else left + F(1, scale)
        lo, hi = self.a + self.b * left, self.a + self.b * right
        return I.outward(min(lo, hi), max(lo, hi))

    def packet(self):
        return {"rational": str(self.a), "radical_coefficient": str(self.b), "radicand": str(self.d)}


def trim(p):
    while len(p) > 1 and p[-1].sign() == 0:
        p.pop()
    return p


def padd(a, b):
    z = Q(0, d=a[0].d)
    return trim([(a[k] if k < len(a) else z) + (b[k] if k < len(b) else z)
                 for k in range(max(len(a), len(b)))])


def pscale(a, x):
    return trim([v * x for v in a])


def pmul(a, b):
    out = [Q(0, d=a[0].d)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = out[i + j] + x * y
    return trim(out)


def ppow(a, n):
    out = [Q(1, d=a[0].d)]
    for _ in range(n):
        out = pmul(out, a)
    return out


def derivative(a):
    return [a[k] * k for k in range(1, len(a))] or [Q(0, d=a[0].d)]


def evaluate(a, x):
    out = a[-1]
    for v in reversed(a[:-1]):
        out = out * x + v
    return out


def polynomial_bounds(a, x):
    out = a[-1].interval()
    for v in reversed(a[:-1]):
        out = out * x + v.interval()
    return out


def bernstein(a, lo, hi):
    n = len(a) - 1
    power = []
    for k in range(n + 1):
        power.append(sum((a[j] * math.comb(j, k) * lo ** (j - k) * (hi - lo) ** k
                          for j in range(k, n + 1)), Q(0, d=a[0].d)))
    return [sum((power[k] * F(math.comb(j, k), math.comb(n, k)) for k in range(j + 1)),
                Q(0, d=a[0].d)) for j in range(n + 1)]


def split_bernstein(a):
    layers = [a]
    while len(layers[-1]) > 1:
        last = layers[-1]
        layers.append([(last[k] + last[k + 1]) / 2 for k in range(len(last) - 1)])
    return [layer[0] for layer in layers], [layer[-1] for layer in reversed(layers)]


def variations(a):
    signs = [x.sign() for x in a if x.sign() != 0]
    return sum(x != y for x, y in zip(signs, signs[1:]))


def trig(deg):
    deg = F(deg)
    deg = (deg + 180) % 360 - 180
    if deg in (0, 90, -90, -180):
        return {F(0): (I(0), I(1)), F(90): (I(1), I(0)), F(-90): (I(-1), I(0)),
                F(-180): (I(0), I(-1))}[deg]
    x = I(PI_LO, PI_HI) * (deg / 180)
    x2 = x.square()
    s, c, st, ct = I(0), I(0), x, I(1)
    for k in range(14):
        s, c = s + st, c + ct
        st = -st * x2 / ((2 * k + 2) * (2 * k + 3))
        ct = -ct * x2 / ((2 * k + 1) * (2 * k + 2))
    bound = max(abs(x.lo), abs(x.hi))
    sr, cr = bound ** 29 / math.factorial(29), bound ** 28 / math.factorial(28)
    return s + I(-sr, sr), c + I(-cr, cr)


def fifth_root(x, digits):
    x, scale = F(x), 10 ** digits
    require(0 <= x <= 1, "invalid_fifth_root_probability")
    target = x.numerator * scale ** 5 // x.denominator
    left, right = 0, scale + 1
    while right - left > 1:
        mid = (left + right) // 2
        if mid ** 5 <= target:
            left = mid
        else:
            right = mid
    value = F(left, scale)
    return I(value, value if value ** 5 == x else value + F(1, scale))


def grid(x, digits):
    scale = 10 ** digits
    def round_half_up(y):
        y = y * scale + F(1, 2)
        return y.numerator // y.denominator
    a, b = round_half_up(x.lo), round_half_up(x.hi)
    require(a == b, "SOURCE_GRID_UNRESOLVED")
    return F(a, scale)


def configuration():
    proof = frozen(HERE / "criterion.md", CONTRACT)
    frozen(HERE / "sources.json", CONTRACT)
    text = (HERE / "criterion.md").read_text()
    blocks = re.findall(r"```json\s*(.*?)\s*```", text, re.S)
    require(len(blocks) == 1, "ambiguous_frame_contract")
    config = json.loads(blocks[0])
    sources = json.loads((HERE / "sources.json").read_text())
    require(config["version"] == sources["version"] == VERSION and
            all(config[k] is False and sources[k] is False for k in FLAGS), "frame_scope_changed")
    bindings = {}
    for row in sources["inputs"]:
        path = (ROOT / row["path"]).resolve()
        require(path.is_relative_to(ROOT) and digest(path) == row["sha256"], "frame_binding_mismatch")
        bindings[row["path"]] = row["sha256"]
    proof["sources_sha256"] = digest(HERE / "sources.json")
    public = json.loads((HERE / config["public_counts"]).resolve().read_text())
    require(public["row_order"] == ["ab", "ab_prime", "a_prime_b", "a_prime_b_prime"] and
            public["outcome_order"] == ["++", "+0", "0+", "00"], "public_count_order_changed")
    confidence = json.loads((HERE / config["public_confidence_report"]).resolve().read_text())["common_mean_confidence"]
    return config, public["counts"], confidence, proof, bindings


def training_view(counts):
    view = []
    for k in (0, 3):
        row = counts[k]
        require(len(row) == 4 and all(type(n) is int and n >= 0 for n in row) and sum(row) > 0,
                "invalid_training_cell")
        view.append((F(row[0] + row[1], sum(row)), F(row[0] + row[2], sum(row))))
    return tuple(view)


def coupled_loss(ka, kb, tc):
    ka, kb, tc = F(ka), F(kb), F(tc)
    delta = (1 + tc) ** 2 - 4 * tc * (ka + kb - ka * kb)
    require(delta > 0 and tc < min(ka, kb) <= max(ka, kb) <= 1, "illegal_coupled_calibration")
    radical = Q(0, 1, delta)
    a = 2 * ka * (1 - tc) / (1 + tc + radical - 2 * ka * tc)
    b = 2 * kb * (1 - tc) / (1 + tc + radical - 2 * kb * tc)
    require(a.sign() >= 0 and (1 - a).sign() >= 0 and b.sign() >= 0 and (1 - b).sign() >= 0,
            "illegal_coupled_transmission")
    n = tc / (1 - tc)
    sa, sb = n * a / (1 + n * a), n * b / (1 + n * b)
    joint = 1 - 1 / (1 + n * a) - 1 / (1 + n * b) + 1 / (1 + n * (a + b - a * b))
    require((joint / sb - ka).sign() == 0 and (joint / sa - kb).sign() == 0,
            "coupled_Klyshko_inverse_not_exact")
    return a, b, {"KA": str(ka), "KB": str(kb), "t_cal": str(tc), "Delta": str(delta),
                  "branch": "vacuum_continuous_small_root", "TA": a.packet(), "TB": b.packet(),
                  "Klyshko_reconstruction_exact": True, "large_root_excluded": True}


def source_from_view(view, ka, kb, config):
    ta, tb, loss = coupled_loss(ka, kb, config["calibration_geometric_ratio"])
    a, b = ta.interval(), tb.interval()
    ba, bb = map(F, config["background_per_pulse"])
    local = [( (1 - ba) / fifth_root(1 - pa, config["root_precision_digits"]) - 1,
               (1 - bb) / fifth_root(1 - pb, config["root_precision_digits"]) - 1)
             for pa, pb in view]
    require(all(x.lo >= 0 for row in local for x in row), "invalid_single_photon_mean")
    cs = [trig(2 * F(angle)) for angle in config["training_signed_A_angles_deg"]]
    u = [(x / a + y / b) / 2 for x, y in local]
    v = [(x / a - y / b) / 2 for x, y in local]
    z = (u[1] - u[0]) / (cs[0][1] - cs[1][1])
    m = u[0] + z * cs[0][1]
    x = -(cs[0][0] * v[0] + cs[1][0] * v[1]) / (cs[0][0].square() + cs[1][0].square())
    mq, zq, xq = [grid(item, config["covariance_grid_digits"]) for item in (m, z, x)]
    radius = zq * zq + xq * xq
    require(mq >= 0 and mq * mq >= radius, "single_map_not_positive_covariance")
    c = I(radius).sqrt()
    nh, nv = mq + c, mq - c
    th, tv = [grid(n / (1 + n), config["source_grid_digits"]) for n in (nh, nv)]
    require(0 <= tv <= th < 1, "illegal_frame_raw_kernel")
    packet = {"geometric_ratio": [str(th), str(tv)], "rotation": {"Z": str(zq), "X": str(xq),
              "radius_squared": str(radius)}, "loss": loss}
    residuals = []
    for i, (ua, ub) in enumerate(local):
        residuals.append({"A": (ua / a - (mq - zq * cs[i][1] - xq * cs[i][0])).packet(),
                          "B": (ub / b - (mq - zq * cs[i][1] + xq * cs[i][0])).packet()})
    reconstruction = {"ungridded_covariance": {"M": m.packet(), "Z": z.packet(), "X": x.packet()},
                      "covariance_grid": {"M": str(mq), "Z": str(zq), "X": str(xq)},
                      "raw_mean_enclosures": [nh.packet(), nv.packet()], "four_scalar_residuals": residuals,
                      "training_view": [[str(x), str(y)] for x, y in view],
                      "joint_statistics_used": False, "heldout_rows_used": False, "confidence_used": False,
                      "documented_r_used": False, "global_N_used": False}
    return packet, ta, tb, reconstruction


def rotation(packet):
    z, x, rad = (F(packet[k]) for k in ("Z", "X", "radius_squared"))
    require(rad == z * z + x * x, "invalid_Jones_direction")
    if rad == 0:
        return ((I(1), I(0)), (I(0), I(1)))
    if x == 0 and z < 0:
        return ((I(0), I(1)), (I(-1), I(0)))
    c = ((1 + z / I(rad).sqrt()) / 2).sqrt()
    s = x / (2 * I(rad).sqrt() * c)
    return ((c, s), (-s, c))


def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)) for i in range(2))


def transpose(a):
    return tuple(tuple(a[j][i] for j in range(2)) for i in range(2))


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def trace(a):
    return a[0][0] + a[1][1]


def complete_homogeneous(trace_value, determinant, cutoff):
    out = [trace_value * 0 + 1]
    if cutoff:
        out.append(trace_value)
    for n in range(2, cutoff + 1):
        out.append(trace_value * out[-1] - determinant * out[-2])
    return out


def source_tail(th, tv, cutoff):
    return 1 - (1 - th) * (1 - tv) * sum(th ** h * tv ** (n - h)
                                       for n in range(cutoff + 1) for h in range(n + 1))


def gamma(matrix, n):
    """Creation-polynomial symmetric tensor in normalized occupation coordinates."""
    out = []
    for row_h in range(n + 1):
        row = []
        for col_h in range(n + 1):
            value = I(0)
            for k in range(max(0, row_h - (n - col_h)), min(row_h, col_h) + 1):
                term = math.comb(col_h, k) * math.comb(n - col_h, row_h - k)
                term = term * I.of(matrix[0][0]).power(k) * I.of(matrix[1][0]).power(col_h - k)
                term = term * I.of(matrix[0][1]).power(row_h - k)
                term = term * I.of(matrix[1][1]).power(n - col_h - row_h + k)
                value += term
            factor = I(F(math.factorial(row_h) * math.factorial(n - row_h),
                         math.factorial(col_h) * math.factorial(n - col_h))).sqrt()
            row.append(value * factor)
        out.append(row)
    return out


def matmul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), I(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def matrix_transpose(a):
    return [list(row) for row in zip(*a)]


def detector(angle, transmission):
    s, c = trig(angle)
    return ((1 - transmission * s.square(), -transmission * s * c),
            (-transmission * s * c, 1 - transmission * c.square()))


def kernel(packet, phase, ratios=None):
    th, tv = tuple(map(F, packet["geometric_ratio"])) if ratios is None else ratios
    r = rotation(packet["rotation"])
    diagonal = ((I.of(th).sqrt(), I(0)), (I(0), phase * I.of(tv).sqrt()))
    return mm(mm(r, diagonal), transpose(r))


def pulse(packet, lam, a, b, cutoff=6, ratios=None):
    th, tv = tuple(map(F, packet["geometric_ratio"])) if ratios is None else ratios
    loss = packet["loss"]
    ta, tb, _ = coupled_loss(loss["KA"], loss["KB"], loss["t_cal"])
    ea, eb = detector(a, ta.interval()), detector(b, tb.interval())
    norm, tail = (1 - th) * (1 - tv), source_tail(th, tv, cutoff)
    tail_upper = tail.hi if isinstance(tail, I) else tail
    require(tail_upper >= 0, "negative_source_tail")
    branches = []
    for phase in (1, -1):
        g = kernel(packet, phase, ratios)
        ga = mm(mm(transpose(g), ea), g)
        gb = mm(mm(transpose(g), g), transpose(eb))
        gab = mm(ga, transpose(eb))
        values = {}
        for name, matrix in (("A", ga), ("B", gb), ("AB", gab)):
            partial = norm * sum(complete_homogeneous(trace(matrix), det(matrix), cutoff), I(0))
            values[name] = partial + I(0, tail_upper)
        branches.append(values)
    return {name: (1 - lam) * branches[0][name] + lam * branches[1][name]
            for name in ("A", "B", "AB")}, tail


def window(no_click, config):
    n = config["window_pulses"]
    ba, bb = map(F, config["background_per_pulse"])
    a, b = ((1 - ba) * no_click["A"]).power(n), ((1 - bb) * no_click["B"]).power(n)
    ab = ((1 - ba) * (1 - bb) * no_click["AB"]).power(n)
    return {"sA": 1 - a, "sB": 1 - b, "j": 1 - a - b + ab}


class Fringe:
    """Finite coherent Gamma trace plus the complete source's exact omitted mass."""
    def __init__(self, packet, ta, tb, basis, config):
        self.basis, self.config = basis, config
        self.ta, self.tb = ta, tb
        t, nmax = F(config["calibration_geometric_ratio"]), config["source_pair_cutoff"]
        self.tail = source_tail(t, t, nmax)
        require(self.tail == t ** (nmax + 1) * (nmax + 2 - (nmax + 1) * t),
                "balanced_tail_not_exact")
        norm = (1 - t) ** 2
        pa = norm * sum((t ** n * h for n, h in enumerate(complete_homogeneous(2 - ta, 1 - ta, nmax))), Q(0, d=ta.d))
        pb = norm * sum((t ** n * h for n, h in enumerate(complete_homogeneous(2 - tb, 1 - tb, nmax))), Q(0, d=ta.d))
        self.base = 1 - self.tail - pa - pb
        z, x, rad = (F(packet["rotation"][k]) for k in ("Z", "X", "radius_squared"))
        if rad == 0:
            z, x, rad = F(1), F(0), F(1)
        cosine_numerators = ([F(1), F(0), F(0)], [z * z / rad, 2 * z * x / rad, x * x / rad])
        if basis == "DA":
            cosine_numerators = ([F(1, 2), F(1), F(1, 2)],
                [(z + x) ** 2 / (2 * rad), -(z + x) * (z - x) / rad, (z - x) ** 2 / (2 * rad)])
        u = [Q(1, d=ta.d), Q(0, d=ta.d), Q(1, d=ta.d)]
        self.denominator_power, self.polynomials = nmax, []
        for co in cosine_numerators:
            trnum = padd(pscale(u, 2 - ta - tb), [ta * tb * value for value in co])
            determinant = (1 - ta) * (1 - tb)
            hn = [[Q(1, d=ta.d)], trnum]
            for n in range(2, nmax + 1):
                hn.append(padd(pmul(trnum, hn[-1]), pscale(pmul(ppow(u, 2), hn[-2]), -determinant)))
            numer = pscale(ppow(u, nmax), self.base)
            for n in range(nmax + 1):
                numer = padd(numer, pscale(pmul(hn[n], ppow(u, nmax - n)), norm * t ** n))
            self.polynomials.append(numer)

    def _profile(self, lam):
        return padd(pscale(self.polynomials[0], 1 - lam), pscale(self.polynomials[1], lam))

    def _curve(self, poly, x):
        return polynomial_bounds(poly, x) / (1 + x.square()).power(self.denominator_power)

    def _extrema(self, poly, tolerance):
        all_points, boxes, coverage = [], [], []
        cap = self.config["fringe_bernstein_split_cap"]
        depth_cap = self.config["fringe_root_refinement_depth_cap"]
        splits = 0
        for chart in ("tan", "cot"):
            chart_poly = poly if chart == "tan" else list(reversed(poly + [Q(0, d=self.ta.d)] *
                (2 * self.denominator_power + 1 - len(poly))))
            u = [Q(1, d=self.ta.d), Q(0, d=self.ta.d), Q(1, d=self.ta.d)]
            deriv = padd(pmul(derivative(chart_poly), u),
                         pscale(pmul(chart_poly, derivative(u)), -self.denominator_power))
            initial = bernstein(deriv, F(-1), F(1))
            pending = [(F(-1), F(1), initial, 0)]
            endpoints = {F(-1), F(1)}
            while pending:
                lo, hi, coefficients, depth = pending.pop()
                variation = variations(coefficients)
                if variation == 0:
                    coverage.append({"chart": chart, "left": str(lo), "right": str(hi), "variation": 0})
                    endpoints.update((lo, hi))
                    continue
                if variation == 1 and evaluate(deriv, lo).sign() * evaluate(deriv, hi).sign() < 0:
                    left, right, bern = lo, hi, coefficients
                    while True:
                        value = self._curve(chart_poly, I(left, right))
                        if value.width <= tolerance:
                            break
                        require(depth < depth_cap and splits < cap, "FRINGE_EXTREMA_UNRESOLVED")
                        middle = (left + right) / 2
                        lb, rb = split_bernstein(bern)
                        signmid = evaluate(deriv, middle).sign()
                        if signmid == 0:
                            left = right = middle
                            value = self._curve(chart_poly, I(middle))
                            break
                        if evaluate(deriv, left).sign() * signmid < 0:
                            right, bern = middle, lb
                        else:
                            left, bern = middle, rb
                        depth, splits = depth + 1, splits + 1
                    boxes.append({"chart": chart, "left": str(left), "right": str(right), "variation": 1,
                                  "value": value.packet()})
                    all_points.append(value)
                    coverage.append({"chart": chart, "left": str(lo), "right": str(hi), "variation": 1})
                    endpoints.update((lo, hi))
                    continue
                require(depth < depth_cap and splits < cap, "FRINGE_EXTREMA_UNRESOLVED")
                middle = (lo + hi) / 2
                lb, rb = split_bernstein(coefficients)
                pending.extend(((middle, hi, rb, depth + 1), (lo, middle, lb, depth + 1)))
                endpoints.add(middle)
                splits += 1
            for point in sorted(endpoints):
                all_points.append(self._curve(chart_poly, I(point)))
        maximum = I(max(x.lo for x in all_points), max(x.hi for x in all_points))
        minimum = I(min(x.lo for x in all_points), min(x.hi for x in all_points))
        return maximum, minimum, {"critical_boxes": boxes, "coverage": coverage,
                                  "splits": splits, "chart_count": 2, "infinity_is_cot_zero": True}

    def bounds(self, lam, requested):
        lam, requested = F(lam), F(requested)
        poly = self._profile(lam)
        tolerance = requested * F(self.config["calibration_geometric_ratio"]) / 16
        maximum, minimum, certificate = self._extrema(poly, tolerance)
        m, s = maximum + I(0, self.tail), minimum + I(0, self.tail)
        require(s.lo >= 0 and m.lo + s.lo > 0, "invalid_calibration_fringe_probability")
        visibility = I.outward((m.lo - s.hi) / (m.lo + s.hi), (m.hi - s.lo) / (m.hi + s.lo))
        certificate.update({"basis": self.basis, "lambda_probe": str(lam),
            "source_tail": str(self.tail), "finite_prefix_renormalized": False,
            "prefix_maximum": maximum.packet(), "prefix_minimum": minimum.packet(),
            "full_visibility": visibility.packet(),
            "polynomial_sha256": hashlib.sha256(json.dumps([x.packet() for x in poly], sort_keys=True).encode()).hexdigest(),
            "Gamma_trace_recurrence": True, "Gaussian_inverse_used": False})
        return visibility, certificate


def lambda_root(packet, ta, tb, target, config):
    curve = Fringe(packet, ta, tb, "DA", config)
    target, width = F(target), F(config["fringe_initial_visibility_width"])
    left, right = F(0), F(1, 2)
    v0, p0 = curve.bounds(left, width)
    v1, p1 = curve.bounds(right, width)
    require(v0.lo > target > v1.hi, "NO_COMPLETE_DA_THRESHOLD_ROOT")
    probes = [p0, p1]
    for _ in range(config["lambda_decision_cap"]):
        if right - left <= F(config["lambda_bracket_width"]):
            break
        mid, requested = (left + right) / 2, width
        while True:
            value, report = curve.bounds(mid, requested)
            if value.lo > target:
                left = mid
                report["decision"] = "above_target"
                break
            if value.hi < target:
                right = mid
                report["decision"] = "below_target"
                break
            requested /= 16
            require(requested >= F(1, 10 ** 29), "LAMBDA_ROOT_UNRESOLVED")
        probes.append(report)
    require(right - left <= F(config["lambda_bracket_width"]), "LAMBDA_ROOT_UNRESOLVED")
    interval = I(left, right)
    lower_v, lower_p = curve.bounds(left, width)
    upper_v, upper_p = curve.bounds(right, width)
    require(upper_v.lo <= target <= lower_v.hi, "DA_root_not_contained")
    hv = Fringe(packet, ta, tb, "HV", config)
    hv_left, hvp_left = hv.bounds(left, width)
    hv_right, hvp_right = hv.bounds(right, width)
    hv_value = I(hv_right.lo, hv_left.hi)
    require(hv_value.contained(*config["visibility_HV_interval"]), "HV_CALIBRATION_OUTSIDE_PUBLIC_INTERVAL")
    return interval, {"representation": "exact_left_threshold_root", "DA_target": str(target),
        "domain": ["0", "1/2"], "bracket": interval.packet(), "midpoint_is_source_weight": False,
        "DA_exact_root_realizes_target": True, "DA_interval": I(upper_v.lo, lower_v.hi).packet(),
        "HV_interval": hv_value.packet(), "probes": probes,
        "final_DA": [lower_p, upper_p], "final_HV": [hvp_left, hvp_right]}


def prepare(view, ka, kb, target, config):
    packet, ta, tb, construction = source_from_view(view, ka, kb, config)
    lam, calibration = lambda_root(packet, ta, tb, target, config)
    packet["phase_root"] = {"DA_target": str(F(target)), "representation": "exact_complete_DA_left_threshold",
                            "bracket": [str(lam.lo), str(lam.hi)]}
    return packet, lam, construction, calibration


def creation_controls(packet, config):
    r = rotation(packet["rotation"])
    records = []
    for phase, a, b, n in itertools.product((1, -1), (F(0), F(21, 5)), (F(0), F(259, 10)), (1, 2, 3)):
        th, tv = map(F, packet["geometric_ratio"])
        losses = packet["loss"]
        ta, tb, _ = coupled_loss(losses["KA"], losses["KB"], losses["t_cal"])
        gr = gamma(r, n)
        diag = [[I(0) for _ in range(n + 1)] for _ in range(n + 1)]
        for h in range(n + 1):
            diag[h][h] = I(th).sqrt().power(h) * (phase * I(tv).sqrt()).power(n - h)
        amplitude = matmul(matmul(gr, diag), matrix_transpose(gr))
        g = kernel(packet, phase)
        generated = gamma(g, n)
        agree = all(amplitude[i][j].lo <= generated[i][j].hi and generated[i][j].lo <= amplitude[i][j].hi
                    for i in range(n + 1) for j in range(n + 1))
        ea, eb = detector(a, ta.interval()), detector(b, tb.interval())
        va, vb = gamma(ea, n), gamma(eb, n)
        left = matmul(matmul(matrix_transpose(amplitude), va), amplitude)
        born = sum((left[i][j] * vb[j][i] for i in range(n + 1) for j in range(n + 1)), I(0))
        matrix = mm(mm(mm(transpose(g), ea), g), transpose(eb))
        native = complete_homogeneous(trace(matrix), det(matrix), n)[n]
        same = born.lo <= native.hi and native.lo <= born.hi
        require(agree and same, "coherent_rotated_source_Gamma_control_failed")
        records.append({"phase": phase, "a": str(a), "b": str(b), "sector": n,
                        "actual_rotated_amplitudes_agree": agree, "Born_trace_recurrence_agrees": same})
    return records


def member():
    config, counts, confidence, freeze, bindings = configuration()
    executable = frozen(__file__)
    view = training_view(counts)
    ka, kb = map(F, config["klyshko_target_center"])
    packet, lam, construction, calibration = prepare(view, ka, kb, config["visibility_DA_center"], config)
    rates, details = [], []
    a0, a1, b0, b1 = map(F, config["angles_deg"])
    for a, b in ((a0, b0), (a0, b1), (a1, b0), (a1, b1)):
        no_click, tail = pulse(packet, lam, a, b, config["source_pair_cutoff"])
        result = window(no_click, config)
        rates.append(result)
        details.append({"angles": [str(a), str(b)], "pulse_no_click": {k: v.packet() for k, v in no_click.items()},
                        "window": {k: v.packet() for k, v in result.items()}, "exact_source_tail": str(tail)})
    groups = {"j": [r["j"] for r in rates], "sA_cell": [r["sA"] for r in rates],
              "sB_cell": [r["sB"] for r in rates]}
    inclusion = {k: [x.contained(ci["exact_lower"], ci["exact_upper"])
                     for x, ci in zip(values, confidence[k])] for k, values in groups.items()}
    controls = creation_controls(packet, config)
    changed = [list(row) for row in counts]
    for k in (0, 3):
        changed[k] = [x + y for x, y in zip(changed[k], (1, -1, -1, 1))]
    alternative, *_ = source_from_view(training_view(changed), ka, kb, config)
    original = {k: v for k, v in packet.items() if k != "phase_root"}
    require(alternative == original, "joint_information_leaked_into_source")
    changed[1], changed[2] = [0, 0, 0, 1], [3, 4, 5, 6]
    alternative, *_ = source_from_view(training_view(changed), ka, kb, config)
    require(alternative == original, "heldout_information_leaked_into_source")
    return {"schema": "p23-frame-window-independent/v1", "version": VERSION,
        "criterion_freeze": freeze, "executable_freeze": executable, "bindings": bindings,
        "source": packet, "single_construction": construction, "calibration": calibration,
        "public_cells": details, "public_probabilities": {k: [x.packet() for x in v] for k, v in groups.items()},
        "confidence_inclusion": inclusion,
        "outcome": "EXHIBITED_FRAME_WINDOW_MEMBER" if all(all(v) for v in inclusion.values()) else "NOT_CERTIFIED_BY_ENCLOSURE",
        "controls": {"actual_R_source_creation_and_Born": controls, "joint_information_flow": True,
                     "heldout_information_flow": True, "two_full_fringe_charts": True,
                     "calibration_tail_paid": True, "source_prefix_renormalized": False,
                     "phase_flip_before_R": True, "primary_code_or_results_read_before_first": False},
        "retrospective": True, "bell_event_files_read": 0, **{k: False for k in FLAGS}}


def json_dump(value):
    return json.dumps(value, ensure_ascii=False, indent=2) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    args = parser.parse_args()
    result = member()
    text = json_dump(result)
    if args.output:
        path = Path(args.output)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
