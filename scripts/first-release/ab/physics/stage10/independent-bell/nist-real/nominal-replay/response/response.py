#!/usr/bin/env python3
"""Exact rational enclosures of the frozen, source-generated M3 response."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
import math
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
FREEZE = "b818e92fbdeca40d4a34c26e4bbf5ad90a0a4f80"
PRECISION = 10 ** 36


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def down(x):
    return F(x.numerator * PRECISION // x.denominator, PRECISION)


def up(x):
    return -down(-x)


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __post_init__(self):
        object.__setattr__(self, "lo", F(self.lo))
        object.__setattr__(self, "hi", F(self.hi))
        require(self.lo <= self.hi, "reversed_interval")

    @classmethod
    def point(cls, x):
        return cls(F(x), F(x))

    def __add__(self, other):
        other = as_interval(other)
        return Interval(down(self.lo + other.lo), up(self.hi + other.hi))

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -as_interval(other)

    def __rsub__(self, other):
        return as_interval(other) + -self

    def __mul__(self, other):
        other = as_interval(other)
        products = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(down(min(products)), up(max(products)))

    __rmul__ = __mul__

    def reciprocal(self):
        require(not self.lo <= 0 <= self.hi, "interval_division_by_zero")
        return Interval(down(1 / self.hi), up(1 / self.lo))

    def __truediv__(self, other):
        return self * as_interval(other).reciprocal()

    def __rtruediv__(self, other):
        return as_interval(other) / self

    def square(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo ** 2, self.hi ** 2)
        return Interval(down(F(low)), up(max(self.lo ** 2, self.hi ** 2)))

    def max_abs(self):
        return max(abs(self.lo), abs(self.hi))

    def midpoint(self):
        return (self.lo + self.hi) / 2

    def radius(self):
        return (self.hi - self.lo) / 2

    def contains(self, x):
        return self.lo <= F(x) <= self.hi

    def receipt(self):
        return {"exact_lower": str(self.lo), "exact_upper": str(self.hi),
                "lower": float(self.lo), "upper": float(self.hi)}


def as_interval(x):
    return x if isinstance(x, Interval) else Interval.point(x)


@lru_cache(maxsize=512)
def trig(x, terms, cosine=False):
    """Horner Taylor polynomial plus the Lagrange remainder, |x| <= 1."""
    require(x.max_abs() <= 1, "trig_domain_not_certified")
    offset = 0 if cosine else 1
    coefficients = [F((-1) ** k, math.factorial(2 * k + offset)) for k in range(terms)]
    polynomial = Interval.point(coefficients[-1])
    for coefficient in reversed(coefficients[:-1]):
        polynomial = polynomial * x.square() + coefficient
    if not cosine:
        polynomial = polynomial * x
    power = 2 * terms + offset
    remainder = x.max_abs() ** power / math.factorial(power)
    return polynomial + Interval(-remainder, remainder)


@dataclass
class Jet:
    value: Interval
    gradient: dict

    @classmethod
    def variable(cls, name, value):
        return cls(value, {name: Interval.point(1)})

    def __add__(self, other):
        other = as_jet(other)
        keys = self.gradient.keys() | other.gradient.keys()
        return Jet(self.value + other.value, {k: self.gradient.get(k, Interval.point(0)) +
                   other.gradient.get(k, Interval.point(0)) for k in keys})

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.value, {k: -v for k, v in self.gradient.items()})

    def __sub__(self, other):
        return self + -as_jet(other)

    def __rsub__(self, other):
        return as_jet(other) + -self

    def __mul__(self, other):
        other = as_jet(other)
        keys = self.gradient.keys() | other.gradient.keys()
        return Jet(self.value * other.value, {k:
                   self.gradient.get(k, Interval.point(0)) * other.value +
                   other.gradient.get(k, Interval.point(0)) * self.value for k in keys})

    __rmul__ = __mul__

    def reciprocal(self):
        inverse = self.value.reciprocal()
        return Jet(inverse, {k: -v * inverse.square() for k, v in self.gradient.items()})

    def __truediv__(self, other):
        return self * as_jet(other).reciprocal()

    def __rtruediv__(self, other):
        return as_jet(other) / self


def as_jet(x):
    return x if isinstance(x, Jet) else Jet(as_interval(x), {})


def sin_cos(angle, pi, terms):
    radians = angle * (2 * pi / 180)
    if isinstance(radians, Jet):
        s = trig(radians.value, terms)
        c = trig(radians.value, terms, True)
        return (Jet(s, {k: c * v for k, v in radians.gradient.items()}),
                Jet(c, {k: -s * v for k, v in radians.gradient.items()}))
    return trig(radians, terms), trig(radians, terms, True)


def load_frozen():
    text = (HERE / "criterion.md").read_text()
    matches = re.findall(r"<!-- FROZEN-RESPONSE-BEGIN -->\s*```json\s*(.*?)\s*```\s*"
                         r"<!-- FROZEN-RESPONSE-END -->", text, flags=re.S)
    require(len(matches) == 1, "nonunique_response_contract")
    config = json.loads(matches[0])
    require(config["source_mapping_identified"] is False and config["production_admitted"] is False
            and config["rounding"]["original_gate_tolerances_modified"] is False,
            "conditional_response_cannot_admit_apparatus")
    for side in ("A", "B"):
        require(F(config["channel"]["eta_" + side]["half_width"]) == F("0.3") / 100,
                "efficiency_percent_unit_mismatch")
    sources = json.loads((HERE / "sources.json").read_text())
    for row in sources["inputs"]:
        require(digest(ROOT / row["path"]) == row["sha256"], "source_binding_mismatch:" + row["path"])
    criterion_freeze()
    return config


def criterion_freeze():
    for name in ("criterion.md", "sources.json"):
        path = str((HERE / name).relative_to(ROOT))
        frozen = subprocess.check_output(["git", "show", FREEZE + ":" + path], cwd=ROOT)
        require(frozen == (HERE / name).read_bytes(), "criterion_not_frozen:" + name)
    return {"commit": FREEZE, "criterion_sha256": digest(HERE / "criterion.md"),
            "sources_sha256": digest(HERE / "sources.json")}


def read_inputs(config):
    instrument = json.loads((ROOT / config["target_instrument"]).read_text())
    amplitudes = instrument["preparation"]["amplitudes"]
    half = F(config["rounding"]["amplitude_half_width"])
    h, v = F(amplitudes["HH"]), F(amplitudes["VV"])
    require(h > half and v > half, "nonpositive_preparation_amplitude")
    box = {"r": Interval((v - half) / (h + half), (v + half) / (h - half))}
    angle_half = F(config["rounding"]["angle_half_width_deg"])
    controls = instrument["controls"]["alice"] + instrument["controls"]["bob"]
    for key, value in zip(("a0", "a1", "b0", "b1"), controls):
        box[key] = Interval(F(value) - angle_half, F(value) + angle_half)
    for side in ("A", "B"):
        entry = config["channel"]["eta_" + side]
        c, w = F(entry["center"]), F(entry["half_width"])
        box["eta_" + side] = Interval(c - w, c + w)
    box["q"] = Interval(*map(F, config["channel"]["pair_probability"]))
    return instrument, box


def response_interval(box, side, pi, terms):
    """Consume the generated harmonic theorem, then factor its derivative."""
    r = box["r"]
    delta = (r.square() - 1) / (1 + r.square())
    chi = 2 * r / (1 + r.square())
    own, other = ("a", "b") if side == "alice" else ("b", "a")
    s, c = sin_cos(box[own + "1"], pi, terms)
    s0, c0 = sin_cos(box[other + "0"], pi, terms)
    s1, c1 = sin_cos(box[other + "1"], pi, terms)
    required = (1 + box["q"] * delta.square()) / chi * s * (c0 - c1) / (c * (s0 - s1))
    allowed = box["xi"] / box["zeta"]
    normalized = box["zeta"] * chi * c * (s0 - s1) * (allowed - required)
    physical = box["q"] * box["eta_A"] * box["eta_B"] / 2 * normalized
    sign = "negative" if physical.hi < 0 else "positive" if physical.lo > 0 else "not_certified"
    return {"required_xi_over_zeta": required, "allowed_xi_over_zeta": allowed,
            "normalized": normalized, "physical": physical, "sign": sign,
            "stationarity_excluded": physical.hi < 0 or physical.lo > 0}


def source_probabilities(parameters, axes):
    """Contract (r VV + HH) with the tensor effects, then average Pauli signs.

    The diagonal and cross terms below are the two-amplitude Born contraction.
    Only the first moments of each local Pauli sign enter these XZ effects.
    """
    r, m_a, m_b, xi, zeta = (parameters[k] for k in ("r", "mA", "mB", "xi", "zeta"))
    ax, az, bx, bz = axes
    norm = 1 + r * r
    joint = (r * r * (1 + m_a * az + m_b * bz + zeta * az * bz) +
             (1 - m_a * az - m_b * bz + zeta * az * bz) + 2 * r * xi * ax * bx) / (4 * norm)
    single_a = (r * r * (1 + m_a * az) + (1 - m_a * az)) / (2 * norm)
    single_b = (r * r * (1 + m_b * bz) + (1 - m_b * bz)) / (2 * norm)
    return joint, single_a, single_b


def source_ch(parameters, config, pi, terms):
    axes = {k: sin_cos(parameters[k], pi, terms) for k in ("a0", "a1", "b0", "b1")}
    q, ea, eb = (parameters[k] for k in ("q", "eta_A", "eta_B"))
    ba = F(config["channel"]["background_A_per_trial"])
    bb = F(config["channel"]["background_B_per_trial"])
    score = 0
    for a, b, sign in (("a0", "b0", 1), ("a0", "b1", 1),
                       ("a1", "b0", 1), ("a1", "b1", -1)):
        joint, pa, pb = source_probabilities(parameters, (*axes[a], *axes[b]))
        score += sign * (q * ea * eb * joint + (q * ea * pa + ba) * (q * eb * pb + bb))
    _, pa, pb = source_probabilities(parameters, (*axes["a0"], *axes["b0"]))
    return score - (q * ea * pa + ba) - (q * eb * pb + bb)


def grouped_ch(parameters, config, pi, terms):
    """Collect the source contraction's q and q² terms before enclosing it."""
    r, q, ea, eb, ma, mb, xi, zeta = (parameters[k] for k in
                                      ("r", "q", "eta_A", "eta_B", "mA", "mB", "xi", "zeta"))
    delta = (r * r - 1) / (1 + r * r)
    chi = 2 * r / (1 + r * r)
    sa0, ca0 = sin_cos(parameters["a0"], pi, terms)
    sa1, ca1 = sin_cos(parameters["a1"], pi, terms)
    sb0, cb0 = sin_cos(parameters["b0"], pi, terms)
    sb1, cb1 = sin_cos(parameters["b1"], pi, terms)
    kz = ca0 * cb0 + ca0 * cb1 + ca1 * cb0 - ca1 * cb1
    kx = sa0 * sb0 + sa0 * sb1 + sa1 * sb0 - sa1 * sb1
    ba = F(config["channel"]["background_A_per_trial"])
    bb = F(config["channel"]["background_B_per_trial"])
    linear = (ea * eb / 2 - ea / 2 - eb / 2 + ea * bb + eb * ba +
              delta * ma * ca0 * ea * ((eb - 1) / 2 + bb) +
              delta * mb * cb0 * eb * ((ea - 1) / 2 + ba) +
              ea * eb * zeta * kz / 4 + ea * eb * xi * chi * kx / 4)
    quadratic = ea * eb / 4 * (2 + 2 * delta * ma * ca0 + 2 * delta * mb * cb0 +
                              delta * delta * zeta * kz)
    return -ba - bb + 2 * ba * bb + q * linear + q * q * quadratic


def orientation_parameters(box, use_jets):
    extended = {**box, "orientation_fiber": Interval(0, 1)}
    p = {key: Jet.variable(key, value) if use_jets else value for key, value in extended.items()}
    p["mA"] = p["zeta"] + p["orientation_fiber"] * (1 - p["zeta"])
    p["mB"] = p["zeta"] / p["mA"]
    return p, extended


def mean_value_ch_at_eta(box, config, pi, terms):
    """A centered mean-value enclosure, using exact interval derivatives."""
    p, domain = orientation_parameters(box, True)
    jet = grouped_ch(p, config, pi, terms)
    center_box = {key: Interval.point(value.midpoint()) for key, value in box.items()}
    center, _ = orientation_parameters(center_box, False)
    center["orientation_fiber"] = Interval.point(F(1, 2))
    center["mA"] = center["zeta"] + center["orientation_fiber"] * (1 - center["zeta"])
    center["mB"] = center["zeta"] / center["mA"]
    center_ch = source_ch(center, config, pi, terms)
    error = sum((jet.gradient[key].max_abs() * value.radius() for key, value in domain.items()), F(0))
    enclosure = Interval(down(center_ch.lo - error), up(center_ch.hi + error))
    return {"CH": enclosure.receipt(), "certified_positive": enclosure.lo > 0,
            "method": "centered_mean_value_with_interval_automatic_derivatives",
            "center_CH": center_ch.receipt(), "radius_error": str(error),
            "gradient_bounds": {key: value.receipt() for key, value in jet.gradient.items()},
            "restriction": config["robust_positive_branch"]["restriction"]}


def mean_value_ch(box, config, pi, terms):
    # The source rates make CH affine in either eta with the other held fixed.
    # Its value on the eta rectangle is a convex combination of four corners.
    corners = []
    for ea in (box["eta_A"].lo, box["eta_A"].hi):
        for eb in (box["eta_B"].lo, box["eta_B"].hi):
            domain = {**box, "eta_A": Interval.point(ea), "eta_B": Interval.point(eb)}
            corners.append(mean_value_ch_at_eta(domain, config, pi, terms))
    lower = min(F(c["CH"]["exact_lower"]) for c in corners)
    upper = max(F(c["CH"]["exact_upper"]) for c in corners)
    return {"CH": Interval(lower, upper).receipt(), "certified_positive": lower > 0,
            "center_CH": Interval(min(F(c["center_CH"]["exact_lower"]) for c in corners),
                                  max(F(c["center_CH"]["exact_upper"]) for c in corners)).receipt(),
            "method": "bilinear_eta_corner_hull_of_centered_mean_value_bounds",
            "restriction": config["robust_positive_branch"]["restriction"]}


def positive_branch(box, config, pi, terms):
    """Refine only the enclosure, in the frozen split order and budget."""
    first = mean_value_ch(box, config, pi, terms)
    order = config["interval"]["split_order"]
    max_depth = config["interval"]["max_depth"]
    max_leaves = config["interval"]["max_leaves"]
    pending = [(box, "", first)]
    leaves = []
    while pending:
        domain, address, result = pending.pop()
        if result is None:
            result = mean_value_ch(domain, config, pi, terms)
        if result["certified_positive"] or len(address) >= max_depth or len(leaves) + len(pending) + 2 > max_leaves:
            leaves.append({"address": address, "CH": result["CH"],
                           "certified_positive": result["certified_positive"]})
            continue
        key = order[len(address) % len(order)]
        original = domain[key]
        mid = original.midpoint()
        for bit, interval in reversed(list(enumerate((Interval(original.lo, mid), Interval(mid, original.hi))))):
            pending.append(({**domain, key: interval}, address + str(bit), None))
    lower = min(F(leaf["CH"]["exact_lower"]) for leaf in leaves)
    upper = max(F(leaf["CH"]["exact_upper"]) for leaf in leaves)
    return {"CH": Interval(lower, upper).receipt(),
            "certified_positive": all(leaf["certified_positive"] for leaf in leaves),
            "method": "bilinear_eta_corners_centered_mean_value_and_frozen_binary_refinement",
            "center_CH": first["center_CH"], "restriction": first["restriction"],
            "split_order": order, "leaf_count": len(leaves),
            "max_depth_used": max(len(leaf["address"]) for leaf in leaves), "leaves": leaves}


def serialize_response(response):
    return {key: value.receipt() if isinstance(value, Interval) else value
            for key, value in response.items()}


def fixed_update(box, update, pi, terms):
    path = dict(box)
    for key in ("a1", "b1"):
        step = F(update[key])
        path[key] = Interval(box[key].lo + min(step, 0), box[key].hi + max(step, 0))
    derivatives = {side: response_interval(path, side, pi, terms) for side in ("alice", "bob")}
    lower = F(0)
    certified = True
    for key, side in (("a1", "alice"), ("b1", "bob")):
        step = F(update[key])
        d = derivatives[side]["physical"]
        if step == 0:
            continue
        product = Interval.point(step) * d * pi / 180
        lower += product.lo
        certified = certified and product.lo > 0
    return {"step_deg": update, "path_box": {key: value.receipt() for key, value in path.items()},
            "path_responses": {side: serialize_response(v) for side, v in derivatives.items()},
            "improvement": {"exact_lower": str(lower), "lower": float(lower)},
            "certified_improvement": certified}


def bindings():
    sources = json.loads((HERE / "sources.json").read_text())
    answer = {row["path"]: digest(ROOT / row["path"]) for row in sources["inputs"]}
    for name in ("criterion.md", "sources.json", "response.py", "Response.lean"):
        answer[str((HERE / name).relative_to(ROOT))] = digest(HERE / name)
    return answer


def compute():
    config = load_frozen()
    instrument, base = read_inputs(config)
    pi = Interval(*map(F, config["interval"]["pi"]))
    terms = config["interval"]["primary_trig_terms"]
    cases = []
    for name, calibration in config["cases"].items():
        box = {**base, **{key: Interval(*map(F, calibration[key])) for key in ("xi", "zeta")}}
        responses = {side: response_interval(box, side, pi, terms) for side in ("alice", "bob")}
        updates = {label: fixed_update(box, step, pi, terms)
                   for label, step in config["fixed_updates_deg"].items()}
        positive = positive_branch(box, config, pi, terms)
        response_certified = responses["alice"]["sign"] == "negative" and responses["bob"]["sign"] == "positive"
        update_certified = all(value["certified_improvement"] for value in updates.values())
        cases.append({"case": name, "status": "CERTIFIED" if response_certified and update_certified else "NOT_CERTIFIED",
                      "box": {key: value.receipt() for key, value in box.items()},
                      "responses": {side: serialize_response(v) for side, v in responses.items()},
                      "fixed_updates": updates, "orientation_preserving_positive_branch": positive})
    return {"schema": "nist-response-primary/v1", "criterion_version": config["criterion_version"],
            "criterion_freeze": criterion_freeze(), "bindings": bindings(),
            "source_mapping_identified": False, "production_admitted": False,
            "status": "CERTIFIED" if all(row["status"] == "CERTIFIED" for row in cases) else "NOT_CERTIFIED",
            "primitive": "same two-amplitude tensor Born contraction and Pauli sign moments; Response.lean harmonic",
            "arithmetic": "Fraction intervals; every operation rounds outward to 36 rational decimal places",
            "pi": pi.receipt(), "trig_terms": terms, "cases": cases,
            "bell_event_files_read": 0, "other_implementation_output_used_as_input": False,
            "access_disclosure": "Primary construction received the independent result summary after criterion freeze; "
                                 "no independent code or output was read or used for inputs or enclosure computation."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = compute()
    if not args.check_only:
        (HERE / "response.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "cases": [
        {"case": c["case"], "response_status": c["status"],
         "conditional_CH": c["orientation_preserving_positive_branch"]["CH"],
         "updates": {k: v["improvement"] for k, v in c["fixed_updates"].items()}} for c in result["cases"]]}, indent=2))
    return 0 if result["status"] == "CERTIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
