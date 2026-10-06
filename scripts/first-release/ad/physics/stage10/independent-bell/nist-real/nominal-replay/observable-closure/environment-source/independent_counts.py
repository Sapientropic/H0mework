#!/usr/bin/env python3
"""Environment-resolved occupation Born readout with an unnormalized pair tail."""
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
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[7]
FREEZE = "75ecac81d9d21ce6112217a72a4368ac85513511"
VERSION = "p23-environment-count-evg0001"
SCHEMA = "p23-environment-count-independent/v1"
DIGITS = 40
SCALE = 10 ** DIGITS
PI = (F("3.14159265358979323846"), F("3.14159265358979323847"))
TOLERANCE = F("1e-12")
FLAGS = ("source_mapping_identified", "new_full_Born_or_Gaussian_determinant_kernel_claim",
         "full_fringe_extrema_certified", "apparatus_optimum_verified", "controller_advance")


def require(value, reason):
    if not value:
        raise ValueError(reason)


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frozen(path, commit=None):
    path = Path(path).resolve()
    rel = str(path.relative_to(ROOT))
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", rel],
                                         cwd=ROOT, text=True).strip()
    require(bool(commit), "uncommitted_source:" + rel)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    blob = subprocess.check_output(["git", "show", commit + ":" + rel], cwd=ROOT)
    require(blob == path.read_bytes(), "source_not_frozen:" + rel)
    return {"path": rel, "commit": commit, "sha256": sha256(path)}


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
    def of(x):
        return x if isinstance(x, I) else I(x)

    @staticmethod
    def outward(lo, hi):
        lo, hi = F(lo) * SCALE, F(hi) * SCALE
        return I(F(lo.numerator // lo.denominator, SCALE),
                 F(-((-hi).numerator // (-hi).denominator), SCALE))

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
        xs = (self.lo * b.lo, self.lo * b.hi, self.hi * b.lo, self.hi * b.hi)
        return I.outward(min(xs), max(xs))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = I.of(other)
        require(not b.lo <= 0 <= b.hi, "zero_interval_denominator")
        xs = (1 / b.lo, 1 / b.hi)
        return self * I.outward(min(xs), max(xs))

    def __rtruediv__(self, other):
        return I.of(other) / self

    def square(self):
        return I.outward(0 if self.lo <= 0 <= self.hi else min(self.lo ** 2, self.hi ** 2),
                         max(self.lo ** 2, self.hi ** 2))

    def __pow__(self, n):
        require(isinstance(n, int) and n >= 0, "invalid_interval_power")
        if n == 0:
            return I(1)
        if n % 2 == 0:
            return self.square() ** (n // 2)
        return self * (self ** (n - 1))

    def sqrt(self):
        require(self.lo >= 0, "negative_square_root")
        left = math.isqrt(self.lo.numerator * SCALE * SCALE // self.lo.denominator)
        right = math.isqrt(self.hi.numerator * SCALE * SCALE // self.hi.denominator)
        upper = F(right, SCALE)
        if upper * upper < self.hi:
            upper += F(1, SCALE)
        return I(F(left, SCALE), upper)

    def contains(self, x):
        return self.lo <= F(x) <= self.hi

    def midpoint(self):
        return (self.lo + self.hi) / 2

    @property
    def width(self):
        return self.hi - self.lo

    def packet(self):
        return {"exact_lower": str(self.lo), "exact_upper": str(self.hi),
                "lower": float(self.lo), "upper": float(self.hi)}


@dataclass(frozen=True)
class C:
    re: I
    im: I

    def __init__(self, re=0, im=0):
        object.__setattr__(self, "re", I.of(re))
        object.__setattr__(self, "im", I.of(im))

    @staticmethod
    def of(x):
        return x if isinstance(x, C) else C(x)

    def __add__(self, other):
        b = C.of(other)
        return C(self.re + b.re, self.im + b.im)

    __radd__ = __add__

    def __neg__(self):
        return C(-self.re, -self.im)

    def __sub__(self, other):
        return self + (-C.of(other))

    def __rsub__(self, other):
        return C.of(other) - self

    def __mul__(self, other):
        b = C.of(other)
        return C(self.re * b.re - self.im * b.im,
                 self.re * b.im + self.im * b.re)

    __rmul__ = __mul__

    def __pow__(self, n):
        require(isinstance(n, int) and n >= 0, "invalid_complex_power")
        out = C(1)
        for _ in range(n):
            out = out * self
        return out

    def conjugate(self):
        return C(self.re, -self.im)

    def packet(self):
        return {"re": self.re.packet(), "im": self.im.packet()}


def trig(degrees):
    degrees = (F(degrees) + 180) % 360 - 180
    if degrees in (0, 90, -90, -180):
        return {F(0): (I(0), I(1)), F(90): (I(1), I(0)),
                F(-90): (I(-1), I(0)), F(-180): (I(0), I(-1))}[degrees]
    x = I(*PI) * (degrees / 180)
    x2 = x.square()
    sine, cosine, sn, cs = I(0), I(0), x, I(1)
    for k in range(14):
        sine, cosine = sine + sn, cosine + cs
        sn = -sn * x2 / ((2 * k + 2) * (2 * k + 3))
        cs = -cs * x2 / ((2 * k + 1) * (2 * k + 2))
    radius = max(abs(x.lo), abs(x.hi))
    rs = radius ** 29 / math.factorial(29)
    rc = radius ** 28 / math.factorial(28)
    return sine + I(-rs, rs), cosine + I(-rc, rc)


def mm(a, b):
    require(a and b and len(a[0]) == len(b), "matrix_dimensions")
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), C())
             for j in range(len(b[0]))] for i in range(len(a))]


def transpose(a):
    return [[a[i][j] for i in range(len(a))] for j in range(len(a[0]))]


def adjoint(a):
    return [[a[i][j].conjugate() for i in range(len(a))] for j in range(len(a[0]))]


def identity(n):
    return [[C(int(i == j)) for j in range(n)] for i in range(n)]


def matrix_subtract(a, b):
    return [[x - y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def matrix_packet(a):
    return [[x.packet() for x in row] for row in a]


def zero_enclosed(x, tolerance=TOLERANCE):
    x = C.of(x)
    return (x.re.contains(0) and x.im.contains(0) and
            max(abs(x.re.lo), abs(x.re.hi), abs(x.im.lo), abs(x.im.hi)) <= tolerance)


def same_matrices(a, b):
    return len(a) == len(b) and len(a[0]) == len(b[0]) and all(
        zero_enclosed(a[i][j] - b[i][j]) for i in range(len(a)) for j in range(len(a[0])))


def real_enclosure(x, label):
    require(x.im.contains(0), "nonreal_Born_value:" + label)
    require(max(abs(x.im.lo), abs(x.im.hi)) <= TOLERANCE, "complex_precision:" + label)
    return x.re


def physical_interval(x, upper, label):
    require(x.lo >= -TOLERANCE and x.hi <= F(upper) + TOLERANCE,
            "Born_range_violation:" + label)
    return I(max(F(0), x.lo), min(F(upper), x.hi))


def intersect(a, b, label):
    lo, hi = max(a.lo, b.lo), min(a.hi, b.hi)
    require(lo <= hi, "inconsistent_enclosures:" + label)
    return I(lo, hi)


def environment_effect(transmissions, xi_pair, angle):
    """Keep both environment modes through the actual polarization projector."""
    transmission = [F(x) for x in transmissions]
    xr, xi = [F(x) for x in xi_pair]
    require(all(0 <= t <= 1 for t in transmission) and xr * xr + xi * xi <= 1,
            "invalid_environment_primitive")
    complement = I(1 - xr * xr - xi * xi).sqrt()
    # Coordinate order is (H,e0),(H,e1),(V,e0),(V,e1).
    embedding = [[C(1), C()], [C(), C()], [C(), C(xr, xi)], [C(), C(complement)]]
    lost = [[C(1 - transmission[p] if p == q else 0) for q in range(2)] for p in range(2)]
    roots = [I(t).sqrt() for t in transmission]
    transmitted = [[row[p] * roots[p] for p in range(2)] for row in embedding]
    sine, cosine = trig(angle)
    v = [sine, cosine]
    projection = [[C(v[p] * v[q] if e == f else 0)
                   for q in range(2) for f in range(2)]
                  for p in range(2) for e in range(2)]
    perpendicular = matrix_subtract(identity(4), projection)
    click = mm(adjoint(transmitted), mm(projection, transmitted))
    # The loss and the retained orthogonal polarization live in separate output spaces.
    no_click = mm(adjoint(transmitted), mm(perpendicular, transmitted))
    no_click = [[no_click[p][q] + lost[p][q] for q in range(2)] for p in range(2)]
    require(same_matrices(mm(adjoint(embedding), embedding), identity(2)), "embedding_not_isometric")
    require(same_matrices(no_click, matrix_subtract(identity(2), click)), "projector_loss_closure")
    return {"embedding": embedding, "projection": projection, "click": click,
            "no_click": no_click, "isometry": True, "projector_loss_closure": True}


def occupation_polynomial(effect, n):
    """Apply each creation column before normalizing occupation monomials."""
    out = [[C() for _ in range(n + 1)] for _ in range(n + 1)]
    for source_h in range(n + 1):
        polynomial = [C(1)]
        for column in [0] * source_h + [1] * (n - source_h):
            expanded = [C() for _ in range(len(polynomial) + 1)]
            for target_h, coefficient in enumerate(polynomial):
                expanded[target_h] = expanded[target_h] + coefficient * effect[1][column]
                expanded[target_h + 1] = expanded[target_h + 1] + coefficient * effect[0][column]
            polynomial = expanded
        source_factorial = math.factorial(source_h) * math.factorial(n - source_h)
        for target_h, coefficient in enumerate(polynomial):
            normalizer = I(F(math.factorial(target_h) * math.factorial(n - target_h),
                             source_factorial)).sqrt()
            out[target_h][source_h] = coefficient * normalizer
    require(same_matrices(out, adjoint(out)), "occupation_effect_not_Hermitian")
    return out


def sector_amplitudes(fixture, n):
    t_h, t_v = F(fixture["tH"]), F(fixture["tV"])
    phase = C(*[F(x) for x in fixture["phase"]])
    require(sum(F(x) ** 2 for x in fixture["phase"]) == 1, "nonunit_source_phase")
    require(0 <= t_h < 1 and 0 <= t_v < 1, "invalid_geometric_source")
    z = (1 - t_h) * (1 - t_v)
    root_h, root_v, root_z = I(t_h).sqrt(), I(t_v).sqrt(), I(z).sqrt()
    return [C(root_z * root_h ** h * root_v ** (n - h)) * phase ** (n - h)
            for h in range(n + 1)]


def contraction(amplitudes, a, b):
    n = len(amplitudes)
    return sum((amplitudes[h].conjugate() * amplitudes[k] * a[h][k] * b[h][k]
                for h in range(n) for k in range(n)), C())


def sector_readout(fixture, n, gamma_a, gamma_b, wrong_bob_adjoint=False):
    amplitudes = sector_amplitudes(fixture, n)
    unit = identity(n + 1)
    bob = transpose(gamma_b) if wrong_bob_adjoint else gamma_b
    a_click, b_click = matrix_subtract(unit, gamma_a), matrix_subtract(unit, bob)
    return {"no_click_A": contraction(amplitudes, gamma_a, unit),
            "no_click_B": contraction(amplitudes, unit, bob),
            "no_click_AB": contraction(amplitudes, gamma_a, bob),
            "outcomes": {"++": contraction(amplitudes, a_click, b_click),
                         "+0": contraction(amplitudes, a_click, bob),
                         "0+": contraction(amplitudes, gamma_a, b_click),
                         "00": contraction(amplitudes, gamma_a, bob)}}


def mass(fixture, cutoff):
    t_h, t_v = F(fixture["tH"]), F(fixture["tV"])
    z = (1 - t_h) * (1 - t_v)
    sectors = [z * sum(t_h ** h * t_v ** (n - h) for h in range(n + 1))
               for n in range(cutoff + 1)]
    prefix = sum(sectors)
    return sectors, prefix, 1 - prefix


def outcomes_from_no_click(no_click):
    a, b, ab = no_click
    return {"++": 1 - a - b + ab, "+0": b - ab, "0+": a - ab, "00": ab}


def windows(no_click, pulses, background):
    a, b, ab = no_click
    ba, bb = [F(x) for x in background]
    require(pulses >= 1 and all(0 <= x <= 1 for x in (ba, bb)), "invalid_window")
    signal = [a ** pulses, b ** pulses, ab ** pulses]
    observed = [(a * (1 - ba)) ** pulses, (b * (1 - bb)) ** pulses,
                (ab * (1 - ba) * (1 - bb)) ** pulses]
    return signal, observed


def single_pair_click(fixture, click_a, click_b, wrong_bob_adjoint=False):
    t_h, t_v = F(fixture["tH"]), F(fixture["tV"])
    require(t_h + t_v > 0, "vacuum_has_no_normalized_pair")
    phase = C(*[F(x) for x in fixture["phase"]])
    amplitudes = [phase * I(t_v / (t_h + t_v)).sqrt(), C(I(t_h / (t_h + t_v)).sqrt())]
    # Γ1 coordinates are (V,H), while the native projector coordinates are (H,V).
    a = [[click_a[1 - i][1 - j] for j in range(2)] for i in range(2)]
    b = [[click_b[1 - i][1 - j] for j in range(2)] for i in range(2)]
    if wrong_bob_adjoint:
        b = transpose(b)
    return real_enclosure(contraction(amplitudes, a, b), "normalized_pair")


def primary_born(fixture, cutoff):
    sites = [environment_effect(fixture["T" + side], fixture["xi" + side], fixture["angles"][i])
             for i, side in enumerate(("A", "B"))]
    blocks = [[occupation_polynomial(site["no_click"], n) for n in range(cutoff + 1)]
              for site in sites]
    sectors, prefix_mass, tail = mass(fixture, cutoff)
    totals = {key: C() for key in ("no_click_A", "no_click_B", "no_click_AB")}
    outcome_totals = {key: C() for key in ("++", "+0", "0+", "00")}
    sector_rows = []
    for n in range(cutoff + 1):
        row = sector_readout(fixture, n, blocks[0][n], blocks[1][n])
        for key in totals:
            totals[key] = totals[key] + row[key]
        for key in outcome_totals:
            outcome_totals[key] = outcome_totals[key] + row["outcomes"][key]
        for key in totals:
            physical_interval(real_enclosure(row[key], key), sectors[n], key)
        for key in outcome_totals:
            physical_interval(real_enclosure(row["outcomes"][key], key), sectors[n], key)
        require(zero_enclosed(sum(row["outcomes"].values(), C()) - sectors[n]), "sector_mass_readback")
        sector_rows.append({"total_pairs": n, "source_mass": str(sectors[n]),
                            "no_click": [row[k].packet() for k in totals],
                            "outcomes": {k: v.packet() for k, v in row["outcomes"].items()}})
    raw_prefix = [real_enclosure(totals[key], key) for key in totals]
    prefix = [physical_interval(x, prefix_mass, "prefix") for x in raw_prefix]
    full = [physical_interval(x + I(0, tail), 1, "full_no_click") for x in prefix]
    direct_outcomes = {k: physical_interval(real_enclosure(v, k), prefix_mass, k) + I(0, tail)
                       for k, v in outcome_totals.items()}
    derived_outcomes = outcomes_from_no_click(full)
    direct = {k: intersect(physical_interval(direct_outcomes[k], 1, k),
                           physical_interval(derived_outcomes[k], 1, k), "full_" + k)
              for k in direct_outcomes}
    require(all(zero_enclosed(outcome_totals[k] - C(outcomes_from_no_click(raw_prefix)[k] -
                                                   (1 - prefix_mass if k == "++" else 0)))
                for k in outcome_totals), "direct_Born_no_click_identity")
    require(all(same_matrices(block[0], [[C(1)]]) and
                same_matrices(block[1], [[sites[i]["no_click"][1 - h][1 - k]
                                         for k in range(2)] for h in range(2)])
                for i, block in enumerate(blocks)), "Gamma_zero_one_readback")
    return {"sites": sites, "blocks": blocks, "sectors": sector_rows,
            "source_mass": prefix_mass, "tail": tail, "prefix": prefix,
            "raw_prefix": raw_prefix, "no_click": full, "outcomes": direct}


def wrong_bob_born(fixture, born, cutoff):
    totals = [C(), C(), C()]
    for n in range(cutoff + 1):
        row = sector_readout(fixture, n, born["blocks"][0][n], born["blocks"][1][n], True)
        for i, key in enumerate(("no_click_A", "no_click_B", "no_click_AB")):
            totals[i] = totals[i] + row[key]
    full = [physical_interval(real_enclosure(x, "wrong_Bob_prefix"), born["source_mass"], "wrong_Bob") +
            I(0, born["tail"]) for x in totals]
    return physical_interval(outcomes_from_no_click(full)["++"], 1, "wrong_Bob_full_joint")


def determinant_2(a):
    require(len(a) == len(a[0]) == 2, "determinant_dimensions")
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def secondary_determinant(fixture, born):
    """A separately labelled algebraic check; it never produces primary enclosures."""
    d = [[C(I(F(fixture["tH"])).sqrt()), C()],
         [C(), C(*[F(x) for x in fixture["phase"]]) * I(F(fixture["tV"])).sqrt()]]
    a, b = [site["no_click"] for site in born["sites"]]
    dd = mm(adjoint(d), d)
    matrices = (mm(adjoint(d), mm(a, d)), mm(dd, transpose(b)),
                mm(mm(adjoint(d), mm(a, d)), transpose(b)))
    z = (1 - F(fixture["tH"])) * (1 - F(fixture["tV"]))
    result = []
    for matrix in matrices:
        denominator = real_enclosure(determinant_2(matrix_subtract(identity(2), matrix)), "secondary_det")
        require(denominator.lo > 0, "secondary_nonpositive_denominator")
        result.append(physical_interval(z / denominator, 1, "secondary_probability"))
    return result


def configuration():
    bindings = {"criterion": frozen(HERE / "numeric-criterion.md", FREEZE),
                "sources": frozen(HERE / "numeric-sources.json", FREEZE),
                "program": frozen(Path(__file__))}
    text = (HERE / "numeric-criterion.md").read_text()
    blocks = re.findall(r"<!-- EVG-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- EVG-FROZEN-END -->", text, re.S)
    require(len(blocks) == 1, "ambiguous_numeric_contract")
    spec = json.loads(blocks[0])
    sources = json.loads((HERE / "numeric-sources.json").read_text())
    require(spec["version"] == sources["version"] == VERSION, "numeric_version_changed")
    require(spec["precision_digits"] == DIGITS and F(spec["implementation_tolerance"]) == TOLERANCE and
            spec["total_pair_prefix"] == 6 and spec["prefix_renormalized"] is False,
            "numeric_method_changed")
    require(all(spec[k] is False for k in FLAGS) and spec["retrospective"] is True and
            spec["event_files_read"] == 0 and sources["actual_source_or_hardware_identity_verified"] is False and
            sources["new_full_Born_or_Gaussian_determinant_kernel_claim"] is False, "numeric_authority_changed")
    require(len(spec["fixtures"]) == 8 and len({x["id"] for x in spec["fixtures"]}) == 8 and
            spec["window_pulse_probes"] == [1, 5] and spec["background_per_pulse"] == ["0", "0"],
            "fixture_inventory_changed")
    inputs = []
    for row in sources["inputs"]:
        path = (ROOT / row["path"]).resolve()
        binding = frozen(path, FREEZE)
        require(binding["sha256"] == row["sha256"], "input_source_digest_changed:" + row["path"])
        inputs.append(binding)
    bindings["input_sources"] = inputs
    return spec, bindings


def control_results(spec, borns):
    by_id = {x["id"]: x for x in spec["fixtures"]}
    complex_fixture = by_id["complex_transpose"]
    complex_born = borns["complex_transpose"]
    correct_pair = single_pair_click(complex_fixture, *[s["click"] for s in complex_born["sites"]])
    wrong_pair = single_pair_click(complex_fixture, *[s["click"] for s in complex_born["sites"]], True)
    wrong_full = wrong_bob_born(complex_fixture, complex_born, spec["total_pair_prefix"])
    correct_full = complex_born["outcomes"]["++"]
    one, split = (borns[x] for x in ("same_product_one_side", "same_product_split"))
    pair_one = single_pair_click(by_id["same_product_one_side"], *[s["click"] for s in one["sites"]])
    pair_split = single_pair_click(by_id["same_product_split"], *[s["click"] for s in split["sites"]])
    second_order = []
    for born in (one, split):
        second_order.append(real_enclosure(sum((born["blocks"][0][2][h][h] for h in range(3)), C()),
                                            "second_order_local_A"))
    delta = second_order[0] - second_order[1]
    rank = borns["rank_one"]
    rank_limit = True
    for side, site in enumerate(rank["sites"]):
        fixture = by_id["rank_one"]
        sine, cosine = trig(fixture["angles"][side])
        t_h, t_v = [F(x) for x in fixture["T" + ("A" if side == 0 else "B")]]
        amplitude = [I(t_h).sqrt() * sine, I(t_v).sqrt() * cosine]
        rank_limit = rank_limit and same_matrices(site["click"],
                         [[C(amplitude[i] * amplitude[j]) for j in range(2)] for i in range(2)])
    phase_fixture = by_id["unequal_polarization_losses"]
    phase_born = borns["unequal_polarization_losses"]
    real_phase = dict(phase_fixture, phase=["1", "0"])
    alternate_joint = C()
    for n in range(spec["total_pair_prefix"] + 1):
        row = sector_readout(real_phase, n, phase_born["blocks"][0][n], phase_born["blocks"][1][n])
        alternate_joint = alternate_joint + row["outcomes"]["++"]
    phase_difference = phase_born["outcomes"]["++"] - (
        physical_interval(real_enclosure(alternate_joint, "alternate_phase"), phase_born["source_mass"], "phase") +
        I(0, phase_born["tail"]))
    secondary_rows = []
    for fixture in spec["fixtures"]:
        born = borns[fixture["id"]]
        secondary = secondary_determinant(fixture, born)
        included = [born["no_click"][i].lo <= secondary[i].lo and
                    secondary[i].hi <= born["no_click"][i].hi for i in range(3)]
        secondary_rows.append({"fixture_id": fixture["id"],
                               "no_click": [x.packet() for x in secondary],
                               "contained_in_primary_Born": included})
    checks = {
        "eight_exact_fixtures": len(borns) == 8,
        "environment_embedding_isometric": all(s["isometry"] for b in borns.values() for s in b["sites"]),
        "native_projector_loss_closure": all(s["projector_loss_closure"] for b in borns.values() for s in b["sites"]),
        "all_Gamma_sectors_Hermitian": all(same_matrices(g, adjoint(g)) for b in borns.values() for site in b["blocks"] for g in site),
        "total_pair_triangle_not_rectangle": all(sum(len(g) for g in b["blocks"][0]) == 28 for b in borns.values()),
        "source_mass_plus_tail_exactly_one": all(b["source_mass"] + b["tail"] == 1 for b in borns.values()),
        "prefix_not_renormalized": rank["source_mass"] < 1 and F(rank["sectors"][0]["source_mass"]) ==
            (1 - F(by_id["rank_one"]["tH"])) * (1 - F(by_id["rank_one"]["tV"])),
        "Gamma_zero_and_one_native_readback": all(same_matrices(b["blocks"][i][0], [[C(1)]]) and
            same_matrices(b["blocks"][i][1], [[s["no_click"][1 - h][1 - k] for k in range(2)] for h in range(2)])
            for b in borns.values() for i, s in enumerate(b["sites"])),
        "complex_transpose_pair_zero": correct_pair.contains(0) and correct_pair.width <= TOLERANCE,
        "wrong_Bob_adjoint_pair_half": wrong_pair.contains(F(1, 2)) and wrong_pair.width <= TOLERANCE,
        "complex_transpose_full_joint_t_squared": correct_full.contains(F(1, 10000)),
        "wrong_Bob_adjoint_full_joint_t": wrong_full.contains(F(1, 100)),
        "wrong_Bob_adjoint_separated": wrong_full.lo > correct_full.hi and wrong_pair.lo > correct_pair.hi,
        "same_product_single_pair_joint_equal": zero_enclosed(C(pair_one - pair_split)),
        "same_product_local_second_order_distinct": not delta.contains(0),
        "xi_one_rank_one_native_limit": rank_limit,
        "two_environment_modes_actual_projector": all(real_enclosure(determinant_2(s["click"]), "two_env_rank").lo > 0
            for s in borns["vacuum"]["sites"]),
        "source_phase_i_not_erased": not phase_difference.contains(0),
        "vacuum_and_all_lost_no_click_one": all(x.contains(1) for key in ("vacuum", "all_lost") for x in borns[key]["no_click"]),
        "vacuum_and_all_lost_joint_zero": all(borns[key]["outcomes"]["++"].contains(0) for key in ("vacuum", "all_lost")),
        "secondary_Gaussian_contained_in_Born": all(all(x["contained_in_primary_Born"]) for x in secondary_rows),
    }
    return {"checks": checks, "passed": all(checks.values()),
            "complex_transpose": {"normalized_pair_joint": correct_pair.packet(),
                                  "wrong_Bob_adjoint_normalized_pair_joint": wrong_pair.packet(),
                                  "full_joint": correct_full.packet(), "wrong_Bob_adjoint_full_joint": wrong_full.packet()},
            "same_product": {"normalized_pair_joint": [pair_one.packet(), pair_split.packet()],
                             "local_A_second_order_coefficient": [x.packet() for x in second_order],
                             "coefficient_difference": delta.packet()},
            "source_phase_i_joint_difference": phase_difference.packet(),
            "secondary_determinant": {"role": "secondary_only_after_occupation_Born",
                                      "primary_enclosures_generated_by_this_path": False, "rows": secondary_rows}}


def compute(progress=True):
    spec, bindings = configuration()
    borns, rows = {}, []
    for fixture in spec["fixtures"]:
        born = primary_born(fixture, spec["total_pair_prefix"])
        borns[fixture["id"]] = born
        window_rows = []
        for pulses in spec["window_pulse_probes"]:
            signal, observed = windows(born["no_click"], pulses, spec["background_per_pulse"])
            signal_outcomes = {k: physical_interval(x, 1, k) for k, x in outcomes_from_no_click(signal).items()}
            observed_outcomes = {k: physical_interval(x, 1, k) for k, x in outcomes_from_no_click(observed).items()}
            if pulses == 1:
                signal_outcomes = {k: intersect(v, born["outcomes"][k], "window_one_" + k)
                                   for k, v in signal_outcomes.items()}
                observed_outcomes = {k: intersect(v, born["outcomes"][k], "window_observed_one_" + k)
                                     for k, v in observed_outcomes.items()}
            require(sum(signal_outcomes.values(), I(0)).contains(1) and
                    sum(observed_outcomes.values(), I(0)).contains(1), "window_outcomes_not_normalized")
            window_rows.append({"pulses": pulses, "background_per_pulse": spec["background_per_pulse"],
                                "signal": {"no_click": [x.packet() for x in signal],
                                           "sA": (1 - signal[0]).packet(), "sB": (1 - signal[1]).packet(),
                                           "j": signal_outcomes["++"].packet(),
                                           "outcomes": {k: x.packet() for k, x in signal_outcomes.items()}},
                                "observed": {"no_click": [x.packet() for x in observed],
                                             "sA": (1 - observed[0]).packet(), "sB": (1 - observed[1]).packet(),
                                             "j": observed_outcomes["++"].packet(),
                                             "outcomes": {k: x.packet() for k, x in observed_outcomes.items()}}})
        rows.append({"fixture_id": fixture["id"], "source_parameters": fixture,
                     "environment_embedding": [matrix_packet(s["embedding"]) for s in born["sites"]],
                     "analysis_projector": [matrix_packet(s["projection"]) for s in born["sites"]],
                     "click_effect": [matrix_packet(s["click"]) for s in born["sites"]],
                     "no_click_effect": [matrix_packet(s["no_click"]) for s in born["sites"]],
                     "Gamma_n": [[matrix_packet(g) for g in side] for side in born["blocks"]],
                     "total_pair_prefix": spec["total_pair_prefix"], "prefix_renormalized": False,
                     "mass": str(born["source_mass"]), "tail": str(born["tail"]),
                     "sector_readout": born["sectors"],
                     "raw_prefix_no_click": [x.packet() for x in born["raw_prefix"]],
                     "prefix_no_click": [x.packet() for x in born["prefix"]],
                     "full_no_click": [x.packet() for x in born["no_click"]],
                     "full_direct_outcomes": {k: x.packet() for k, x in born["outcomes"].items()},
                     "windows": window_rows})
        if progress:
            print("occupation-Born " + fixture["id"] + " complete", file=sys.stderr, flush=True)
    controls = control_results(spec, borns)
    return {"schema": SCHEMA, "version": VERSION, "criterion_freeze": FREEZE,
            "bindings": bindings, "precision_digits": DIGITS, "pi_interval": [str(x) for x in PI],
            "trig_terms": 14, "implementation_tolerance": str(TOLERANCE),
            "primary_method": "Pol_tensor_Env_native_projector_then_normalized_creation_polynomial_Gamma_and_coherent_pair_Born",
            "tail_method": "exact_total_pair_mass_complement_added_once_without_renormalization",
            "rows": rows, "controls": controls,
            "outcome": "FINITE_BORN_AND_ENVIRONMENT_CONTROLS_VERIFIED" if controls["passed"] else "UNRESOLVED",
            **{k: False for k in FLAGS}, "actual_source_or_hardware_identity_verified": False,
            "retrospective": True, "event_files_read": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "counts-independent.json")
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    require(args.check_only or not args.output.exists(), "independent_first_receipt_already_exists")
    report = compute()
    raw = (json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()
    if args.check_only:
        sys.stdout.buffer.write(raw)
    else:
        args.output.write_bytes(raw)
        print(json.dumps({"path": str(args.output), "sha256": hashlib.sha256(raw).hexdigest(),
                          "outcome": report["outcome"], "checks_passed": report["controls"]["passed"]}), flush=True)
    return 0 if report["controls"]["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
