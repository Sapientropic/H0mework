#!/usr/bin/env python3
"""Single-only Jones source, algebraic calibration fringe and full window law."""
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
ROOT = HERE.parents[6]
VERSION = "p23-frame-window-fw0001"
FLAGS = ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
         "actual_window_model_identified", "calibration_protocol_identified", "noise_channel_identified",
         "source_pair_rate_reference_identified", "common_Jones_map_identified",
         "equal_branch_conversion_identified", "actual_pump_actuator_identified")


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return Path(path).relative_to(ROOT).as_posix()


def committed(path):
    name = relative(path)
    rev = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", name], cwd=ROOT, text=True).strip()
    require(rev and subprocess.check_output(["git", "show", rev+":"+name], cwd=ROOT) == Path(path).read_bytes(),
            "SOURCE_NOT_FROZEN:"+name)
    return {"path": name, "commit": rev, "sha256": digest(path)}


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


def inputs():
    criterion, sources = HERE/"criterion.md", HERE/"sources.json"
    freeze = committed(criterion)
    committed(sources)
    executable = committed(Path(__file__).resolve())
    subprocess.run(["git", "merge-base", "--is-ancestor", freeze["commit"], executable["commit"]],
                   cwd=ROOT, check=True)
    text = criterion.read_text()
    require("unfrozen_draft" not in text and "FW-FROZEN-BEGIN" in text, "UNFROZEN_FRAME_CRITERION")
    blocks = re.findall(r"```json\s*(.*?)\s*```", text, re.S)
    require(len(blocks) == 1, "NONUNIQUE_FRAME_CRITERION")
    config = json.loads(blocks[0])
    manifest = json.loads(sources.read_text())
    require(config["version"] == manifest["version"] == VERSION and
            config["status"] == "frozen_before_execution", "WRONG_FRAME_VERSION_OR_FREEZE_STATUS")
    require(all(config[k] is False and manifest[k] is False for k in FLAGS), "FRAME_IDENTITY_SCOPE_CHANGED")
    public = (HERE.parent/"shalm2015-channel-inputs.txt").read_text()
    rows = re.findall(r"(\d+(?:\.\d+)?)\s+\+-\s+(\d+(?:\.\d+)?)\s*%\s*\((Alice|Bob)\)", public)
    require(len(rows) == 2 and {r[2] for r in rows} == {"Alice", "Bob"}, "AMBIGUOUS_KLYSHKO_SOURCE_TEXT")
    documented = {name: (F(center)/100, F(half)/100) for center, half, name in rows}
    require([documented[p][0] for p in ("Alice", "Bob")] == list(map(F, config["klyshko_target_center"])) and
            all(documented[p][1] == F(config["klyshko_probability_half_width"]) for p in documented),
            "TEXT_MACHINE_KLYSHKO_UNIT_MISMATCH")
    bindings = {}
    for row in manifest["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and digest(path) == row["sha256"], "FRAME_INPUT_BINDING_CHANGED")
        bindings[row["path"]] = row["sha256"]
    gaussian = module("_fw_frozen_gaussian", HERE.parent/"gaussian-window/gaussian.py")
    gaussian.arithmetic.PRECISION = 10**config["primary_precision_digits"]
    gaussian.SCALE = gaussian.arithmetic.PRECISION
    config = {**gaussian.specification(), **config}
    counts = json.loads((HERE/config["public_counts"]).resolve().read_text())["counts"]
    confidence = json.loads((HERE/config["public_confidence_report"]).resolve().read_text())["common_mean_confidence"]
    return config, bindings, counts, confidence, gaussian, freeze, executable


@dataclass(frozen=True)
class Quadratic:
    """An exact real element a+b*sqrt(d), in one source-owned quadratic field."""
    a: F
    b: F
    d: F

    def __post_init__(self):
        for key in ("a", "b", "d"):
            object.__setattr__(self, key, F(getattr(self, key)))
        require(self.d >= 0, "NEGATIVE_CALIBRATION_RADICAND")
        p, q = math.isqrt(self.d.numerator), math.isqrt(self.d.denominator)
        if p*p == self.d.numerator and q*q == self.d.denominator:
            object.__setattr__(self, "a", self.a+self.b*F(p, q))
            object.__setattr__(self, "b", F(0))

    def coerce(self, value):
        if isinstance(value, Quadratic):
            require(value.d == self.d, "DIFFERENT_CALIBRATION_FIELDS")
            return value
        return Quadratic(F(value), F(0), self.d)

    def __add__(self, value):
        value = self.coerce(value)
        return Quadratic(self.a+value.a, self.b+value.b, self.d)

    __radd__ = __add__

    def __neg__(self):
        return Quadratic(-self.a, -self.b, self.d)

    def __sub__(self, value):
        return self+-self.coerce(value)

    def __rsub__(self, value):
        return self.coerce(value)+-self

    def __mul__(self, value):
        value = self.coerce(value)
        return Quadratic(self.a*value.a+self.b*value.b*self.d,
                         self.a*value.b+self.b*value.a, self.d)

    __rmul__ = __mul__

    def sign(self):
        a, b = self.a, self.b
        if b == 0 or self.d == 0:
            return (a > 0)-(a < 0)
        if a == 0:
            return (b > 0)-(b < 0)
        if (a > 0) == (b > 0):
            return (a > 0)-(a < 0)
        difference = a*a-b*b*self.d
        return ((a > 0)-(a < 0))*((difference > 0)-(difference < 0))

    def reciprocal(self):
        require(self.sign() != 0, "ZERO_ALGEBRAIC_DENOMINATOR")
        norm = self.a*self.a-self.b*self.b*self.d
        require(norm != 0, "DEGENERATE_QUADRATIC_FIELD")
        return Quadratic(self.a/norm, -self.b/norm, self.d)

    def __truediv__(self, value):
        return self*self.coerce(value).reciprocal()

    def __rtruediv__(self, value):
        return self.coerce(value)*self.reciprocal()

    def __pow__(self, n):
        require(type(n) is int and n >= 0, "INVALID_ALGEBRAIC_POWER")
        answer, value = self.coerce(1), self
        while n:
            if n & 1:
                answer *= value
            value *= value
            n //= 2
        return answer

    def enclosure(self, gaussian):
        return gaussian.I.point(self.a)+self.b*gaussian.square_root(self.d)

    def receipt(self):
        return {"rational": str(self.a), "sqrt_coefficient": str(self.b), "radicand": str(self.d)}


def zero(c):
    return c.sign() == 0 if isinstance(c, Quadratic) else c == 0


def trim(p):
    p = list(p)
    while len(p) > 1 and zero(p[-1]):
        p.pop()
    return tuple(p)


def p_add(a, b):
    return trim(tuple((a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0)
                      for i in range(max(len(a), len(b)))))


def p_scale(p, c):
    return trim(tuple(c*x for x in p))


def p_sub(a, b):
    return p_add(a, p_scale(b, -1))


def p_mul(a, b):
    result = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return trim(result)


def p_derivative(p):
    return trim(tuple(i*p[i] for i in range(1, len(p))) or (0,))


def p_value(p, x):
    answer = p[-1]
    for c in reversed(p[:-1]):
        answer = answer*x+c
    return answer


def p_div(a, b):
    require(not (len(b) == 1 and zero(b[0])), "ZERO_STURM_DIVISOR")
    r = list(trim(a))
    q = [0]*max(1, len(r)-len(b)+1)
    while not (len(r) == 1 and zero(r[0])) and len(r) >= len(b):
        k, c = len(r)-len(b), r[-1]/b[-1]
        q[k] += c
        for i, v in enumerate(b):
            r[i+k] -= c*v
        r = list(trim(r))
    return trim(q), trim(r)


def primitive(p):
    p = trim(p)
    parts = [y for c in p for y in ((c.a, c.b) if isinstance(c, Quadratic) else (F(c),))]
    denominator = math.lcm(*(v.denominator for v in parts))
    divisor = math.gcd(*(abs(v.numerator*(denominator//v.denominator)) for v in parts))
    return p if divisor == 0 else p_scale(p, F(denominator, divisor))


def square_free(p):
    a, b = primitive(p), primitive(p_derivative(p))
    if len(b) == 1 and zero(b[0]):
        return a
    while not (len(b) == 1 and zero(b[0])):
        _, r = p_div(a, b)
        a, b = b, primitive(r)
    a = p_scale(a, 1/a[-1])
    quotient, remainder = p_div(p, a)
    require(len(remainder) == 1 and zero(remainder[0]), "INVALID_SQUARE_FREE_DIVISION")
    return primitive(quotient)


def sturm(p):
    answer = [primitive(p), primitive(p_derivative(p))]
    if len(answer[-1]) == 1 and zero(answer[-1][0]):
        return answer[:-1]
    while True:
        _, r = p_div(answer[-2], answer[-1])
        r = primitive(p_scale(r, -1))
        if len(r) == 1 and zero(r[0]):
            return answer
        answer.append(r)


def sign(c):
    return c.sign() if isinstance(c, Quadratic) else (c > 0)-(c < 0)


def variations(chain, x):
    signs = [sign(p_value(p, x)) for p in chain]
    signs = [v for v in signs if v]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def coefficient_receipt(p):
    return [c.receipt() if isinstance(c, Quadratic) else str(F(c)) for c in p]


def cauchy_bound(p):
    lead = p[-1]*sign(p[-1])
    def ceiling(value):
        if zero(value):
            return 0
        lo, hi = 0, 1
        while sign(hi-value) < 0:
            hi *= 2
            require(hi.bit_length() <= 256, "FRINGE_ROOT_BOUND_UNRESOLVED")
        while hi-lo > 1:
            mid = (lo+hi)//2
            if sign(mid-value) >= 0:
                hi = mid
            else:
                lo = mid
        return hi
    return 1+max(ceiling(c*sign(c)/lead) for c in p[:-1])


def all_real_roots(p, depth, config):
    p = square_free(p)
    if len(p) == 1:
        return [], {"square_free_polynomial": coefficient_receipt(p), "real_root_count": 0,
                    "chains": [], "deflations": [], "sturm_splits": 0}
    bound = cauchy_bound(p)
    initial = sturm(p)
    expected = variations(initial, -bound)-variations(initial, bound)
    chains, deflations, roots = {}, [], []
    def register(poly, chain):
        coefficients = coefficient_receipt(poly)
        identity = hashlib.sha256(json.dumps(coefficients, sort_keys=True).encode()).hexdigest()
        chains[identity] = {"polynomial": coefficients,
                            "sequence": [coefficient_receipt(s) for s in chain]}
        return identity
    identity = register(p, initial)
    pending = [(p, initial, identity, F(-bound), F(bound), expected, 0)]
    splits = 0
    while pending:
        poly, chain, identity, lo, hi, count, level = pending.pop()
        if not count:
            continue
        require(level <= config["fringe_root_refinement_depth_cap"], "FRINGE_EXTREMA_UNRESOLVED")
        if count == 1 and hi-lo <= F(1, 2**depth):
            roots.append({"lo": lo, "hi": hi, "count": 1, "chain": identity,
                          "variation_lo": variations(chain, lo), "variation_hi": variations(chain, hi),
                          "exact_root": False})
            continue
        splits += 1
        require(splits <= config["fringe_sturm_split_cap"], "FRINGE_EXTREMA_UNRESOLVED")
        mid = (lo+hi)/2
        if zero(p_value(poly, mid)):
            quotient, remainder = p_div(poly, (-mid, F(1)))
            require(len(remainder) == 1 and zero(remainder[0]), "INVALID_RATIONAL_ROOT_DEFLATION")
            roots.append({"lo": mid, "hi": mid, "count": 1, "chain": identity, "exact_root": True})
            reduced = primitive(quotient)
            next_chain = sturm(reduced)
            next_identity = register(reduced, next_chain)
            left = variations(next_chain, lo)-variations(next_chain, mid)
            right = variations(next_chain, mid)-variations(next_chain, hi)
            deflations.append({"parent_chain": identity, "root": mid, "quotient_chain": next_identity,
                               "parent_count": count, "left_count": left, "right_count": right})
            require(left+right+1 == count, "STURM_DEFLATION_COUNT_CHANGED")
            if left:
                pending.append((reduced, next_chain, next_identity, lo, mid, left, level+1))
            if right:
                pending.append((reduced, next_chain, next_identity, mid, hi, right, level+1))
        else:
            left = variations(chain, lo)-variations(chain, mid)
            right = variations(chain, mid)-variations(chain, hi)
            require(left+right == count, "STURM_SUBDIVISION_COUNT_CHANGED")
            if left:
                pending.append((poly, chain, identity, lo, mid, left, level+1))
            if right:
                pending.append((poly, chain, identity, mid, hi, right, level+1))
    require(len(roots) == expected and all(type(r["count"]) is int and r["count"] == 1 for r in roots),
            "INCOMPLETE_REAL_ROOT_INVENTORY")
    roots.sort(key=lambda r: (r["lo"], r["hi"]))
    return roots, {"square_free_polynomial": coefficient_receipt(p), "cauchy_bound": bound,
                   "real_root_count": expected, "variation_minus_bound": variations(initial, -bound),
                   "variation_plus_bound": variations(initial, bound), "chains": chains,
                   "deflations": deflations, "sturm_splits": splits}


def raw_losses(kA, kB, tc, gaussian):
    delta = (1+tc)**2-4*tc*(kA+kB-kA*kB)
    require(delta > 0, "NONPOSITIVE_KLYSHKO_DISCRIMINANT")
    one = Quadratic(1, 0, delta)
    root = Quadratic(0, 1, delta)
    a = 2*kA*(1-tc)/(one+tc+root-2*kA*tc)
    b = 2*kB*(1-tc)/(one+tc+root-2*kB*tc)
    require(a.sign() >= 0 and (1-a).sign() >= 0 and b.sign() >= 0 and (1-b).sign() >= 0,
            "INVALID_KLYSHKO_SOURCE_INVERSE")
    n = tc/(1-tc)
    def matched(x, y):
        return 1-(1-x)*(1+n*y)/((1+n*x)*(1+n*(x+y-x*y)))
    require(zero(matched(a, b)-kA) and zero(matched(b, a)-kB), "KLYSHKO_INVERSE_IDENTITY_FAILED")
    require((one+tc+root-2*kA*tc).sign() > 0 and (one+tc+root-2*kB*tc).sign() > 0,
            "NONPOSITIVE_KLYSHKO_INVERSE_DENOMINATOR")
    return a, b, {"Klyshko_targets": [str(kA), str(kB)], "calibration_geometric_ratio": str(tc),
                  "branch": "vacuum_continuous_small_root",
                  "radicand": str(delta), "raw_transmission_A": a.receipt(),
                  "raw_transmission_B": b.receipt(), "matched_Klyshko_exact": [str(kA), str(kB)]}


def nth_root(value, n, digits, I):
    value = F(value)
    require(0 <= value <= 1, "ROOT_INPUT_NOT_PROBABILITY")
    scale = 10**digits
    target = value.numerator*scale**n//value.denominator
    lo, hi = 0, scale+1
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**n <= target:
            lo = mid
        else:
            hi = mid
    return I(F(lo, scale), F(lo if F(lo, scale)**n == value else lo+1, scale))


def nearest_grid(x, digits):
    scale = 10**digits
    def integer(v):
        v = v*scale+F(1, 2)
        return v.numerator//v.denominator
    lo, hi = integer(x.lo), integer(x.hi)
    require(lo == hi, "SOURCE_GRID_UNRESOLVED")
    return F(lo, scale)


def trig_deg(degrees, config, gaussian):
    a = F(degrees) % 360
    if a > 180:
        a -= 360
    cos_sign = 1
    if a > 90:
        a, cos_sign = 180-a, -1
    elif a < -90:
        a, cos_sign = -180-a, -1
    if a > 45:
        s, c = gaussian.trigonometry(90-a, config)
        return c, cos_sign*s
    if a < -45:
        s, c = gaussian.trigonometry(90+a, config)
        return -c, cos_sign*s
    s, c = gaussian.trigonometry(a, config)
    return s, cos_sign*c


def training_view(counts):
    require(len(counts) == 4, "MISSING_FRAME_SETTING_CELLS")
    result = []
    for index in (0, 3):
        row = counts[index]
        require(len(row) == 4 and all(type(c) is int and c >= 0 for c in row) and sum(row) > 0,
                "INVALID_FRAME_TRAINING_COUNTS")
        result.append({"sA": F(row[0]+row[1], sum(row)), "sB": F(row[0]+row[2], sum(row))})
    return result


def source_from_singles(view, point, config, gaussian):
    I = gaussian.I
    tc = F(config["calibration_geometric_ratio"])
    a, b, loss = raw_losses(point["K_A"], point["K_B"], tc, gaussian)
    eta = [a.enclosure(gaussian), b.enclosure(gaussian)]
    background = list(map(F, config["background_per_pulse"]))
    u, v, means, geometry = [], [], [], []
    for row, angle in zip(view, config["training_signed_A_angles_deg"]):
        s, c = trig_deg(2*F(angle), config, gaussian)
        local = [(1-background[j])/nth_root(1-row[key], config["window_pulses"],
                                           config["root_precision_digits"], I)-1
                 for j, key in enumerate(("sA", "sB"))]
        require(all(x.lo >= 0 for x in local), "INVALID_SINGLE_CALIBRATION_MEAN")
        normalized = [x/e for x, e in zip(local, eta)]
        u.append((normalized[0]+normalized[1])/2)
        v.append((normalized[0]-normalized[1])/2)
        means.append({"A": local[0], "B": local[1], "normalized_A": normalized[0],
                      "normalized_B": normalized[1]})
        geometry.append((s, c))
    (s0, c0), (s1, c1) = geometry
    require((c0-c1).lo > 0 and (s0.square()+s1.square()).lo > 0, "SINGULAR_SINGLE_GEOMETRY")
    Z = (u[1]-u[0])/(c0-c1)
    M = u[0]+Z*c0
    X = -(s0*v[0]+s1*v[1])/(s0.square()+s1.square())
    m, z, x = [nearest_grid(value, config["covariance_grid_digits"]) for value in (M, Z, X)]
    rho = z*z+x*x
    require(m >= 0 and m*m >= rho, "INVALID_SINGLE_COVARIANCE")
    C = gaussian.square_root(rho)
    nh, nv = m+C, m-C
    th, tv = [nearest_grid(n/(1+n), config["source_grid_digits"]) for n in (nh, nv)]
    require(0 <= tv <= th < 1, "INVALID_H_DOMINANT_PAIR_KERNEL")
    packet = {"geometric_ratio": [str(th), str(tv)],
              "rotation": {"Z": str(z), "X": str(x), "C_squared": str(rho)},
              "loss_inverse": loss}
    residuals = []
    for i, (s, c) in enumerate(geometry):
        residuals.append({"A": means[i]["normalized_A"]-(m-z*c-x*s),
                          "B": means[i]["normalized_B"]-(m-z*c+x*s)})
    actual_nh, actual_nv = th/(1-th), tv/(1-tv)
    actual_m, actual_c = (actual_nh+actual_nv)/2, (actual_nh-actual_nv)/2
    actual_z, actual_x = ((actual_c*z/C, actual_c*x/C) if rho else (I.point(0), I.point(0)))
    actual_residuals = [{"A": means[i]["normalized_A"]-(actual_m-actual_z*c-actual_x*s),
                         "B": means[i]["normalized_B"]-(actual_m-actual_z*c+actual_x*s)}
                        for i, (s, c) in enumerate(geometry)]
    return packet, {"training_marginals": view, "single_means": means,
                    "LS_covariance_enclosures": {"M": M, "Z": Z, "X": X},
                    "covariance_grid": {"M": m, "Z": z, "X": x},
                    "native_mean_enclosures": {"H": nh, "V": nv},
                    "LS_reconstruction_residuals": residuals,
                    "actual_covariance": {"M": actual_m, "Z": actual_z, "X": actual_x},
                    "actual_normalized_single_residuals": actual_residuals,
                    "covariance_quantization_errors": {"M": m-M, "Z": z-Z, "X": x-X},
                    "geometric_quantization_mean_errors": {"H": actual_nh-nh, "V": actual_nv-nv},
                    "orientation_identified_from_singles": rho > 0,
                    "independent_joint_statistics_used": False, "heldout_rows_used": False,
                    "global_N_used": False, "documented_optimal_state_used": False, "public_q_used": False}


def packet_losses(packet):
    row = packet["loss_inverse"]
    def value(name):
        item = row[name]
        return Quadratic(F(item["rational"]), F(item["sqrt_coefficient"]), F(item["radicand"]))
    return value("raw_transmission_A"), value("raw_transmission_B")


def rotation(packet, gaussian):
    row = packet["rotation"]
    z, x, rho = F(row["Z"]), F(row["X"]), F(row["C_squared"])
    require(rho == z*z+x*x, "FRAME_DIRECTION_RADICAND_MISMATCH")
    if rho == 0:
        return gaussian.I.point(1), gaussian.I.point(0)
    C = gaussian.square_root(rho)
    if x == 0 and z < 0:
        return gaussian.I.point(0), gaussian.I.point(1)
    c = gaussian.square_root((1+z/C)/2)
    s = gaussian.square_root((1-z/C)/2)
    return c, -s if x < 0 else s


def projected_vector(packet, angle, config, gaussian):
    s, c = trig_deg(angle, config, gaussian)
    cr, sr = rotation(packet, gaussian)
    return s*cr-c*sr, s*sr+c*cr


def mixed_pulse(packet, lam, a, b, config, gaussian):
    th, tv = map(F, packet["geometric_ratio"])
    nh, nv = th/(1-th), tv/(1-tv)
    etaA, etaB = [x.enclosure(gaussian) for x in packet_losses(packet)]
    sa, ca = projected_vector(packet, a, config, gaussian)
    sb, cb = projected_vector(packet, b, config, gaussian)
    muA, muB = etaA*(nh*sa.square()+nv*ca.square()), etaB*(nh*sb.square()+nv*cb.square())
    kh = gaussian.square_root(nh*(1+nh)*etaA*etaB)
    kv = gaussian.square_root(nv*(1+nv)*etaA*etaB)
    branches = []
    for phase in (1, -1):
        kappa = kh*sa*sb+phase*kv*ca*cb
        denominator = (1+muA)*(1+muB)-kappa.square()
        require(denominator.lo > 0, "NONPOSITIVE_ROTATED_VACUUM_DETERMINANT")
        branches.append({"phase": phase, "kappa": kappa, "no_click_AB": 1/denominator})
    return {"no_click_A": 1/(1+muA), "no_click_B": 1/(1+muB),
            "no_click_AB": (1-lam)*branches[0]["no_click_AB"]+lam*branches[1]["no_click_AB"],
            "mean_A": muA, "mean_B": muB, "phase_branches": branches}


def window(pulse, N, background, gaussian):
    ba, bb = map(F, background)
    qa = gaussian.power((1-ba)*pulse["no_click_A"], N)
    qb = gaussian.power((1-bb)*pulse["no_click_B"], N)
    qab = gaussian.power((1-ba)*(1-bb)*pulse["no_click_AB"], N)
    return {"sA": 1-qa, "sB": 1-qb, "j": 1-qa-qb+qab}


def fringe_profile(packet, axis, config):
    a, b = packet_losses(packet)
    tc = F(config["calibration_geometric_ratio"])
    n = tc/(1-tc)
    D, L = (1+n*a)*(1+n*b), n*(1+n)*a*b
    K0 = 1-1/(1+n*a)-1/(1+n*b)
    row = packet["rotation"]
    z, x, rho = F(row["Z"]), F(row["X"]), F(row["C_squared"])
    if rho == 0:
        z, x, rho = F(1), F(0), F(1)
    U = (F(1), F(0), F(1))
    if axis == "HV":
        plus = (F(1), F(0), F(0))
        minus = (z*z/rho, 2*z*x/rho, x*x/rho)
    else:
        require(axis == "DA", "UNKNOWN_CALIBRATION_FRINGE")
        plus = (F(1, 2), F(1), F(1, 2))
        minus = ((z+x)**2/(2*rho), (x*x-z*z)/rho, (z-x)**2/(2*rho))
    A, B = p_sub(p_scale(U, D), p_scale(plus, L)), p_sub(p_scale(U, D), p_scale(minus, L))
    require((D-L).sign() > 0, "FRINGE_POLE_ON_REAL_AXIS")
    return U, A, B, K0


def fringe_extrema(packet, lam, axis, config, gaussian, depth=80):
    U, A, B, K0 = fringe_profile(packet, axis, config)
    left = p_sub(p_mul(p_derivative(U), A), p_mul(U, p_derivative(A)))
    right = p_sub(p_mul(p_derivative(U), B), p_mul(U, p_derivative(B)))
    P = primitive(p_add(p_scale(p_mul(left, p_mul(B, B)), 1-lam),
                        p_scale(p_mul(right, p_mul(A, A)), lam)))
    require(len(P) <= 7, "CALIBRATION_DERIVATIVE_DEGREE_EXCEEDED")
    roots, inventory = all_real_roots(P, depth, config)
    def enclosure(c):
        return c.enclosure(gaussian) if isinstance(c, Quadratic) else gaussian.I.point(c)
    Ai, Bi = tuple(map(enclosure, A)), tuple(map(enclosure, B))
    def value(q):
        av, bv = p_value(Ai, q), p_value(Bi, q)
        require(av.lo > 0 and bv.lo > 0, "FRINGE_ROOT_DENOMINATOR_UNRESOLVED")
        return enclosure(K0)+(1-lam)*(1+q.square())/av+lam*(1+q.square())/bv
    infinity = enclosure(K0)+(1-lam)/enclosure(A[-1])+lam/enclosure(B[-1])
    candidates = [value(gaussian.I(r["lo"], r["hi"])) for r in roots]+[infinity]
    constant = len(P) == 1 and zero(P[0])
    if constant:
        qzero = value(gaussian.I.point(0))
        require(qzero.lo <= infinity.hi and infinity.lo <= qzero.hi, "FALSE_CONSTANT_FRINGE")
        candidates.append(qzero)
    maximum = gaussian.I(max(v.lo for v in candidates), max(v.hi for v in candidates))
    minimum = gaussian.I(min(v.lo for v in candidates), min(v.hi for v in candidates))
    require(minimum.lo >= 0 and (maximum+minimum).lo > 0, "INVALID_CALIBRATION_VISIBILITY_DENOMINATOR")
    visibility = (maximum-minimum)/(maximum+minimum)
    return visibility, {"axis": axis, "lambda": lam, "refinement_depth": depth,
                        "U": coefficient_receipt(U), "A": coefficient_receipt(A), "B": coefficient_receipt(B),
                        "derivative_polynomial": coefficient_receipt(P), "root_inventory": inventory,
                        "root_brackets": roots, "q_infinity": infinity, "candidate_values": candidates,
                        "constant_fringe": constant, "maximum": maximum, "minimum": minimum,
                        "visibility": visibility}


def visibility_probe(packet, lam, target, config, gaussian):
    depth = 64
    while True:
        visibility, receipt = fringe_extrema(packet, lam, "DA", config, gaussian, depth)
        if visibility.lo > target:
            return 1, receipt
        if visibility.hi < target:
            return -1, receipt
        depth *= 2
        require(depth <= config["fringe_root_refinement_depth_cap"], "LAMBDA_ROOT_UNRESOLVED")


def visibility_calibration(packet, target, config, gaussian):
    lo, hi = F(0), F(1, 2)
    left, first = visibility_probe(packet, lo, target, config, gaussian)
    right, last = visibility_probe(packet, hi, target, config, gaussian)
    require(left == 1 and right == -1, "COMPLETE_DA_CALIBRATION_ROOT_NOT_BRACKETED")
    probes = [first, last]
    while hi-lo > F(config["lambda_bracket_width"]):
        require(len(probes)-2 < config["lambda_decision_cap"], "LAMBDA_ROOT_UNRESOLVED")
        mid = (lo+hi)/2
        direction, receipt = visibility_probe(packet, mid, target, config, gaussian)
        receipt["bracket_before"] = [lo, hi]
        probes.append(receipt)
        if direction > 0:
            lo = mid
        else:
            hi = mid
    lam = gaussian.I(lo, hi)
    hvlo, hv_left = fringe_extrema(packet, lo, "HV", config, gaussian, 128)
    hvhi, hv_right = fringe_extrema(packet, hi, "HV", config, gaussian, 128)
    dalo, da_left = fringe_extrema(packet, lo, "DA", config, gaussian, 128)
    dahi, da_right = fringe_extrema(packet, hi, "DA", config, gaussian, 128)
    hv = gaussian.I(hvhi.lo, hvlo.hi)
    da = gaussian.I(dahi.lo, dalo.hi)
    hv_interval, da_interval = list(map(F, config["visibility_HV_interval"])), list(map(F, config["visibility_DA_interval"]))
    require(hv_interval[0] <= hv.lo <= hv.hi <= hv_interval[1] and
            da_interval[0] <= target <= da_interval[1] and da.lo <= target <= da.hi,
            "FRAME_CALIBRATION_OUTSIDE_PUBLIC_INTERVAL")
    error = max(abs(da.lo-target), abs(da.hi-target))
    require(error <= F(config["calibration_center_computational_error"]), "CALIBRATION_CENTER_NUMERICAL_UNRESOLVED")
    descriptor = {"definition": "exact_left_threshold_of_complete_DA_visibility", "target": target,
                  "calibration_geometric_ratio": F(config["calibration_geometric_ratio"]),
                  "profile_rotation": packet["rotation"], "profile_loss_inverse": packet["loss_inverse"],
                  "canonical_isolating_bracket": [lo, hi], "source_value_is_dyadic_midpoint": False,
                  "midpoint_for_float_candidate_only": (lo+hi)/2}
    return lam, {"target": target, "threshold_bracket": [lo, hi], "lambda_root": descriptor,
                 "phase_flip_probability_enclosure": lam,
                 "threshold_probes": probes,
                 "HV_full_fringe": {"left_probe": hv_left, "right_probe": hv_right, "visibility": hv},
                 "DA_full_fringe": {"left_probe": da_left, "right_probe": da_right,
                                    "visibility_enclosure": da, "exact_by_threshold_definition": target},
                 "DA_target_closure_error": error, "calibration_protocol_identified": False}


def points(config):
    center = list(map(F, config["klyshko_target_center"]))
    width = F(config["klyshko_probability_half_width"])
    da = F(config["visibility_DA_center"])
    da_width = (F(config["visibility_DA_interval"][1])-F(config["visibility_DA_interval"][0]))/2
    result = [{"point_id": "center", "K_A": center[0], "K_B": center[1], "DA_target": da}]
    for bits in itertools.product((0, 1), repeat=3):
        sign = [2*b-1 for b in bits]
        result.append({"point_id": "corner_"+"".join(map(str, bits)), "K_A": center[0]+sign[0]*width,
                       "K_B": center[1]+sign[1]*width, "DA_target": da+sign[2]*da_width})
    require(len(result) == 9, "INCOMPLETE_FRAME_CALIBRATION_POINTS")
    return result


def prepare(config, view, point, gaussian):
    packet, construction = source_from_singles(view, point, config, gaussian)
    lam, calibration = visibility_calibration(packet, point["DA_target"], config, gaussian)
    return packet, lam, construction, calibration


def pair_readout(packet, gaussian):
    th, tv = map(F, packet["geometric_ratio"])
    return {"pair_at_least_one": th+tv-th*tv, "pair_exactly_one": (1-th)*(1-tv)*(th+tv),
            "mean_pair_number": th/(1-th)+tv/(1-tv),
            "one_pair_conditional_amplitude_ratio": gaussian.square_root(tv/th) if th else None,
            "documented_pair_probability": "1/2000", "documented_amplitude_ratio": "276/961",
            "public_q_uncertainty_bound_identified": False, "used_to_construct_source": False}


def source_tail(packet, cutoff):
    th, tv = map(F, packet["geometric_ratio"])
    return 1-(1-th)*(1-tv)*sum((th**h*tv**(n-h) for n in range(cutoff+1) for h in range(n+1)), F(0))


def source_controls(counts, packet, point, config, gaussian):
    source_packet = {key: packet[key] for key in ("geometric_ratio", "rotation", "loss_inverse")}
    altered = [list(row) for row in counts]
    for index in (0, 3):
        altered[index] = [c+d for c, d in zip(altered[index], (1, -1, -1, 1))]
    joint, _ = source_from_singles(training_view(altered), point, config, gaussian)
    for index in (1, 2):
        altered[index] = [c+(j+1)*17 for j, c in enumerate(altered[index])]
    held, _ = source_from_singles(training_view(altered), point, config, gaussian)
    require(joint == source_packet and held == source_packet, "JOINT_OR_HELDOUT_INPUT_LEAKED_INTO_FRAME_SOURCE")
    return {"joint_change_preserving_marginals_preserves_source": joint == source_packet,
            "whole_heldout_rows_preserve_source": held == source_packet}


def serial(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, Quadratic):
        return value.receipt()
    if hasattr(value, "receipt"):
        return value.receipt()
    if isinstance(value, dict):
        return {k: serial(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [serial(v) for v in value]
    return value


def generate():
    config, bindings, counts, confidence, gaussian, freeze, executable = inputs()
    view, rows = training_view(counts), []
    for point in points(config):
        try:
            packet, lam, construction, calibration = prepare(config, view, point, gaussian)
        except ValueError as error:
            rows.append({"point": point, "outcome": "FRAME_SOURCE_OR_CALIBRATION_NOT_REALIZED",
                         "failure_reason": str(error), "partial_point_discarded": False})
            continue
        cells = [window(mixed_pulse(packet, lam, config["angles_deg"][x], config["angles_deg"][2+y],
                                    config, gaussian), config["window_pulses"], config["background_per_pulse"], gaussian)
                 for x in range(2) for y in range(2)]
        probabilities = {key: [r[field] for r in cells] for key, field in
                         (("j", "j"), ("sA_cell", "sA"), ("sB_cell", "sB"))}
        inclusion = {key: [F(c["exact_lower"]) <= v.lo <= v.hi <= F(c["exact_upper"])
                           for c, v in zip(confidence[key], values)] for key, values in probabilities.items()}
        actual_residuals = [{key: cells[index][key]-view[k][key] for key in ("sA", "sB")}
                            for k, index in enumerate((0, 3))]
        packet["lambda_root"] = calibration["lambda_root"]
        rows.append({"point": point, "source_parameters": packet, "phase_flip_probability_enclosure": lam,
                     "source_construction": construction, "calibration_readouts": calibration,
                     "public_cells": cells, "public_probabilities": probabilities, "confidence_inclusion": inclusion,
                     "actual_single_probability_residuals": actual_residuals,
                     "source_diagnostics": pair_readout(packet, gaussian),
                     "source_pair_tail": source_tail(packet, config["source_pair_cutoff"]),
                     "controls": source_controls(counts, packet, point, config, gaussian),
                     "outcome": "EXHIBITED_FRAME_WINDOW_MEMBER" if all(all(v) for v in inclusion.values())
                     else "NOT_CERTIFIED_BY_ENCLOSURE"})
    return serial({"schema": "p23-frame-window-primary/v1", "version": VERSION,
                   "criterion_freeze": freeze, "executable_freeze": executable, "bindings": bindings,
                   "points": rows, "point_count": len(rows), "bell_event_files_read": 0, "retrospective": True,
                   "independent_joint_statistics_used_to_construct_source": False,
                   "other_implementation_output_used_as_input": False, **{k: False for k in FLAGS}})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = generate()
    text = json.dumps(result, indent=2, allow_nan=False)+"\n"
    if not args.check_only:
        (HERE/"forward.json").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
