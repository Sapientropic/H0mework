#!/usr/bin/env python3
"""Vacuum-eliminated numerical form of the fixed-environment threshold law."""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
import itertools
import json
import math
from pathlib import Path
import subprocess
import hashlib

HERE = Path(__file__).resolve().parent
TOL = 1e-12


def require(value, reason):
    if not value:
        raise ValueError(reason)


@dataclass(frozen=True)
class Source:
    tH: float
    tV: float
    transmission_a: tuple[float, float]
    transmission_b: tuple[float, float]
    u_a: float
    u_b: float
    coherence: float
    background: tuple[float, float] = (0.0, 0.0)

    def __post_init__(self):
        require(len(self.transmission_a) == len(self.transmission_b) == len(self.background) == 2,
                "two_physical_polarizations_required")
        values = (self.tH, self.tV, *self.transmission_a, *self.transmission_b,
                  self.u_a, self.u_b, self.coherence, *self.background)
        require(all(math.isfinite(x) for x in values), "nonfinite_source")
        require(0 <= self.tH < 1 and 0 <= self.tV < 1, "geometric_ratio_out_of_domain")
        require(all(0 <= x <= 1 for x in (*self.transmission_a, *self.transmission_b,
                                         self.u_a, self.u_b, *self.background)), "physical_parameter_out_of_domain")
        require(self.coherence ** 2 <= self.u_a * self.u_b + 2e-15 and abs(self.coherence) <= 1,
                "coherence_not_generated_by_legal_environment")

    def pulse(self, angle_a, angle_b):
        a, b = math.radians(angle_a), math.radians(angle_b)
        sa, ca, sb, cb = math.sin(a), math.cos(a), math.sin(b), math.cos(b)
        th, tv = self.tH, self.tV
        ah, av = self.transmission_a
        bh, bv = self.transmission_b
        ha, hb = sa * ca, sb * cb
        z = (1 - th) * (1 - tv)
        la = th * ah * sa * sa * (1 - tv) + tv * av * ca * ca * (1 - th)
        la += th * tv * ah * av * (1 - self.u_a) * ha * ha
        lb = th * bh * sb * sb * (1 - tv) + tv * bv * cb * cb * (1 - th)
        lb += th * tv * bh * bv * (1 - self.u_b) * hb * hb
        pa = ah * sa * sa + av * ca * ca - ah * av * (1 - self.u_a) * ha * ha
        pb = bh * sb * sb + bv * cb * cb - bh * bv * (1 - self.u_b) * hb * hb
        h = math.sqrt(th * ah * bh) * sa * sb
        v = math.sqrt(tv * av * bv) * ca * cb
        c = self.coherence
        # The signed square preserves destructive interference without subtracting two large terms.
        paired = abs(c) * (h + math.copysign(1.0, c) * v) ** 2
        paired += (1 - abs(c)) * (h * h + v * v)
        delta = paired - th * tv * pa * pb
        lab = la + lb - delta
        qa, qb, qab = z + la, z + lb, z + lab
        require(min(qa, qb, qab) > 0, "nonpositive_generated_denominator")
        signal_a, signal_b = la / qa, lb / qb
        joint = ((2 * z + lab) * la * lb + z * z * delta) / (qa * qb * qab)
        ba, bb = self.background
        observed_a = signal_a + ba * (1 - signal_a)
        observed_b = signal_b + bb * (1 - signal_b)
        observed_joint = ((1 - ba) * (1 - bb) * joint +
                          (1 - ba) * bb * signal_a + (1 - bb) * ba * signal_b + ba * bb)
        return observed_a, observed_b, observed_joint

    def probabilities(self, angle_a, angle_b, pulses=1):
        require(type(pulses) is int and pulses in (1, 5), "unregistered_pulse_count")
        a, b, joint = self.pulse(angle_a, angle_b)
        if pulses == 5:
            event = a + b - joint
            # Finite inclusion expansion is the same local any-click law; it retains the linear joint term.
            window_joint = pulses * joint + sum(
                (-1) ** k * math.comb(pulses, k) * (event ** k - a ** k - b ** k)
                for k in range(2, pulses + 1))
            single_a = 1.0 if a == 1.0 else -math.expm1(pulses * math.log1p(-a))
            single_b = 1.0 if b == 1.0 else -math.expm1(pulses * math.log1p(-b))
            a, b, joint = single_a, single_b, window_joint
        outcomes = {"++": joint, "+0": a - joint, "0+": b - joint, "00": 1 - a - b + joint}
        require(all(-TOL <= p <= 1 + TOL for p in outcomes.values()), "generated_outcome_out_of_range")
        return {"sA": a, "sB": b, "j": joint, "outcomes": outcomes}


def from_fixture(raw, background=(0.0, 0.0)):
    def real(value):
        require(type(value) in (str, int, F), "nonliteral_fixture_number")
        return float(F(value))
    def complex_value(value):
        require(type(value) is list and len(value) == 2, "two_complex_coordinates_required")
        return complex(*map(real, value))
    phase, xa, xb = (complex_value(raw[key]) for key in ("phase", "xiA", "xiB"))
    require(abs(abs(phase) ** 2 - 1) <= 2e-15, "nonunit_source_phase")
    return Source(real(raw["tH"]), real(raw["tV"]), tuple(map(real, raw["TA"])),
                  tuple(map(real, raw["TB"])), abs(xa) ** 2, abs(xb) ** 2,
                  (phase * xa * xb).real, tuple(background))


def nominal(gain, transmission_a, transmission_b, coherence, beta, *, allocation="symmetric", background=(0.0, 0.0)):
    require(math.isfinite(gain) and gain >= 0 and 0 <= beta <= 45, "nominal_gain_or_pump_out_of_domain")
    require(0 <= coherence <= 1, "nominal_real_coherence_out_of_domain")
    if allocation == "symmetric":
        ua, ub = coherence, coherence
    elif allocation == "Alice_rank_one":
        ua, ub = 1.0, coherence ** 2
    elif allocation == "Bob_rank_one":
        ua, ub = coherence ** 2, 1.0
    else:
        raise ValueError("unregistered_environment_allocation")
    beta = math.radians(beta)
    return Source(math.tanh(gain * math.cos(beta)) ** 2, math.tanh(gain * math.sin(beta)) ** 2,
                  (transmission_a, transmission_a), (transmission_b, transmission_b),
                  ua, ub, coherence, tuple(background))


def raw_ch(source, angles, pulses=1):
    a0, a1, b0, b1 = angles
    cells = [source.probabilities(a, b, pulses) for a, b in itertools.product((a0, a1), (b0, b1))]
    return cells[0]["j"] + cells[1]["j"] + cells[2]["j"] - cells[3]["j"] - cells[0]["sA"] - cells[0]["sB"]


def cross_controls():
    root = HERE.parents[7]
    bindings = {}
    for path in (Path(__file__), HERE / "counts-primary.json", HERE / "counts-independent.json"):
        name = path.resolve().relative_to(root).as_posix()
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", name],
                                         cwd=root, text=True).strip()
        require(bool(commit), "unfrozen_count_source")
        require(subprocess.check_output(["git", "show", commit + ":" + name], cwd=root) == path.read_bytes(),
                "count_source_differs_from_freeze")
        bindings[name] = {"commit": commit, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    primary = json.loads((HERE / "counts-primary.json").read_text())
    independent = json.loads((HERE / "counts-independent.json").read_text())
    rows = []
    for raw in independent["rows"]:
        name = raw["fixture_id"]
        source = from_fixture(raw["source_parameters"])
        angles = tuple(float(F(x)) for x in raw["source_parameters"]["angles"])
        largest = 0.0
        for window in raw["windows"]:
            pulses = window["pulses"]
            result = source.probabilities(*angles, pulses)
            for key, value in result["outcomes"].items():
                for packet in (primary["fixtures"][name]["windows"][str(pulses)][key],
                               window["observed"]["outcomes"][key]):
                    lo, hi = float(F(packet["exact_lower"])), float(F(packet["exact_upper"]))
                    largest = max(largest, lo - value, value - hi)
        require(largest <= TOL, "stable_native_Fock_disagreement:" + name)
        rows.append({"fixture": name, "max_distance_from_actual_enclosures": largest})
    return {"schema": "p23-stable-environment-count-control/v1", "status": "passed", "rows": rows,
            "source_bindings": bindings,
            "readout_tolerance": TOL, "arithmetic_probability_clipping_used": False,
            "new_Born_or_stable_formula_kernel_claim": False, "CH_optimization_executed": False}


if __name__ == "__main__":
    print(json.dumps(cross_controls(), indent=2, sort_keys=True))
