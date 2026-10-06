#!/usr/bin/env python3
"""Source-polytope cover, common phase slabs, and positive occupation Born readout."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[7]
FREEZE = "ac14d39d3b"
VERSION = "p23-full-statistical-fiber-ef0003"
SCHEMA = "p23-full-statistical-fiber-independent/v1"
SCALE = 10**50
AXES = ("m", "z", "x", "r", "e")
FIELDS = (("sA_cell", 0), ("sB_cell", 0), ("sA_cell", 3), ("sB_cell", 3), ("j", 0), ("j", 3))
SCOPE = {"new_full_Born_kernel_claim": False, "new_statistical_coverage_kernel_claim": False,
         "source_mapping_identified": False, "publication_configuration_identified": False,
         "actual_epoch_identified": False, "apparatus_optimum_verified": False,
         "controller_advance": False, "bell_event_files_read": 0, "retrospective": True}


def require(value, reason):
    if not value:
        raise ValueError(reason)


def canonical(value):
    return json.dumps(serial(value), sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def sha(value):
    return hashlib.sha256(value).hexdigest()


def frozen(path, commit=None):
    path = Path(path).resolve()
    require(path.is_relative_to(ROOT), "foreign_source_path")
    rel = path.relative_to(ROOT).as_posix()
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", rel], cwd=ROOT, text=True).strip()
    require(bool(commit), "uncommitted_independent_fiber:"+rel)
    require(subprocess.check_output(["git", "show", commit+":"+rel], cwd=ROOT) == path.read_bytes(),
            "unfrozen_independent_fiber:"+rel)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    return {"path": rel, "commit": commit, "sha256": sha(path.read_bytes())}


def ceiling(n, d):
    return -((-n)//d)


@dataclass(frozen=True)
class I:
    """Directed integer arithmetic on a fixed 50-place grid."""
    lo: int
    hi: int

    def __init__(self, lower=0, upper=None):
        lower, upper = F(lower), F(lower if upper is None else upper)
        require(lower <= upper, "reversed_interval")
        object.__setattr__(self, "lo", lower.numerator*SCALE//lower.denominator)
        object.__setattr__(self, "hi", ceiling(upper.numerator*SCALE, upper.denominator))

    @classmethod
    def raw(cls, lo, hi):
        require(lo <= hi, "reversed_raw_interval")
        out = object.__new__(cls)
        object.__setattr__(out, "lo", lo)
        object.__setattr__(out, "hi", hi)
        return out

    @classmethod
    def of(cls, value):
        return value if isinstance(value, I) else I(value)

    def __add__(self, value):
        b = I.of(value)
        return I.raw(self.lo+b.lo, self.hi+b.hi)

    __radd__ = __add__

    def __neg__(self):
        return I.raw(-self.hi, -self.lo)

    def __sub__(self, value):
        return self+-I.of(value)

    def __rsub__(self, value):
        return I.of(value)+-self

    def __mul__(self, value):
        b = I.of(value)
        values = (self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi)
        return I.raw(min(values)//SCALE, ceiling(max(values), SCALE))

    __rmul__ = __mul__

    def __truediv__(self, value):
        b = I.of(value)
        require(not b.lo <= 0 <= b.hi, "division_through_zero")
        reciprocal = I.raw(SCALE*SCALE//b.hi, ceiling(SCALE*SCALE, b.lo))
        return self*reciprocal

    def __rtruediv__(self, value):
        return I.of(value)/self

    def square(self):
        lower = 0 if self.lo <= 0 <= self.hi else min(self.lo*self.lo, self.hi*self.hi)
        return I.raw(lower//SCALE, ceiling(max(self.lo*self.lo, self.hi*self.hi), SCALE))

    def power(self, n):
        require(type(n) is int and n >= 0, "invalid_interval_power")
        if n == 0:
            return I(1)
        if n % 2 == 0:
            return self.square().power(n//2)
        return self*self.power(n-1)

    __pow__ = power

    def sqrt(self):
        require(self.lo >= 0, "negative_square_root")
        lower, upper = math.isqrt(self.lo*SCALE), math.isqrt(self.hi*SCALE)
        return I.raw(lower, upper+(upper*upper < self.hi*SCALE))

    @property
    def width(self):
        return self.hi-self.lo

    def midpoint(self):
        return F(self.lo+self.hi, 2*SCALE)

    def intersect(self, value):
        b = I.of(value)
        lo, hi = max(self.lo, b.lo), min(self.hi, b.hi)
        return None if lo > hi else I.raw(lo, hi)

    def contains(self, value):
        value = F(value)*SCALE
        return self.lo <= value <= self.hi

    def contained(self, value):
        b = I.of(value)
        return b.lo <= self.lo and self.hi <= b.hi

    def within_exact(self, packet):
        return F(packet["exact_lower"])*SCALE <= self.lo and self.hi <= F(packet["exact_upper"])*SCALE

    def disjoint_exact(self, packet):
        return self.hi < F(packet["exact_lower"])*SCALE or F(packet["exact_upper"])*SCALE < self.lo

    def packet(self):
        return {"exact_lower": str(F(self.lo, SCALE)), "exact_upper": str(F(self.hi, SCALE)),
                "lower": self.lo/SCALE, "upper": self.hi/SCALE}


def serial(value):
    if isinstance(value, I):
        return value.packet()
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {key: serial(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [serial(item) for item in value]
    return value


def unpack(value):
    return I(value["exact_lower"], value["exact_upper"])


def fifth_root_delta(value, config):
    """(1+x)^(1/5)-1, with the full binomial tail enclosed."""
    value = I.of(value)
    radius = max(abs(value.lo), abs(value.hi))
    require(radius <= I(config["binomial_input_abs_max"]).hi, "binomial_input_outside_frozen_domain")
    coefficient, result = F(1), I(0)
    terms = config["binomial_terms"]
    for n in range(1, terms+1):
        coefficient *= (F(1, 5)-(n-1))/n
        result += coefficient*value.power(n)
    next_coefficient = coefficient*(F(1, 5)-terms)/(terms+1)
    rad = I.raw(radius, radius)
    remainder = abs(next_coefficient)*rad.power(terms+1)/(1-rad)
    return result+I.raw(-remainder.hi, remainder.hi)


@lru_cache(maxsize=64)
def trig(degrees, terms=14):
    degrees = F(degrees)
    reduced = (degrees+180)%360-180
    if reduced in (0, 90, -90, -180):
        return {F(0):(I(0), I(1)), F(90):(I(1), I(0)),
                F(-90):(I(-1), I(0)), F(-180):(I(0), I(-1))}[reduced]
    x = reduced*I("3.14159265358979323846", "3.14159265358979323847")/180
    sine = sum(((-1)**n*x.power(2*n+1)/math.factorial(2*n+1) for n in range(terms)), I(0))
    cosine = sum(((-1)**n*x.power(2*n)/math.factorial(2*n) for n in range(terms)), I(0))
    radius = I.raw(max(abs(x.lo), abs(x.hi)), max(abs(x.lo), abs(x.hi)))
    sr = radius.power(2*terms+1)/math.factorial(2*terms+1)
    cr = radius.power(2*terms)/math.factorial(2*terms)
    return sine+I.raw(-sr.hi, sr.hi), cosine+I.raw(-cr.hi, cr.hi)


def constants(config):
    angles = tuple(map(F, config["angles_deg"]))
    singles = [trig(2*angle, config["independent_trig_terms"]) for angle in angles]
    cells = []
    for x, y in itertools.product(range(2), repeat=2):
        a, b = angles[x], angles[2+y]
        _, d = trig(a-b, config["independent_trig_terms"])
        ss, cc = trig(a+b, config["independent_trig_terms"])
        cells.append({"x":x, "y":y, "d":d, "sum_sin":ss, "sum_cos":cc})
    return {"angles":angles, "singles":singles, "cells":cells,
            "background":tuple(map(F, config["background_per_pulse"]))}


def closing(text, start):
    stack, quoted, escaped = [], False, False
    for pos in range(start, len(text)):
        char = text[pos]
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
            continue
        if char == '"':
            quoted = True
        elif char in "[{":
            stack.append(char)
        elif char in "]}":
            require(stack and (stack[-1], char) in (("[", "]"), ("{", "}")), "unbalanced_json")
            stack.pop()
            if not stack:
                return pos+1
    raise ValueError("unterminated_json")


def field_container(text, name, opener):
    matches = list(re.finditer('"'+re.escape(name)+r'"\s*:\s*'+re.escape(opener), text))
    require(len(matches) == 1, "nonunique_json_field:"+name)
    start = matches[0].end()-1
    return text[start:closing(text, start)]


def selected_objects(text, indices):
    selected, pos, index = {}, 1, 0
    while pos < len(text):
        if text[pos] in " \r\n\t,":
            pos += 1
            continue
        if text[pos] == "]":
            break
        require(text[pos] == "{", "unexpected_confidence_packet")
        end = closing(text, pos)
        if index in indices:
            selected[index] = json.loads(text[pos:end])
        pos, index = end, index+1
    require(index == 4 and set(selected) == set(indices), "missing_confidence_packet")
    return selected


def parse_training(text):
    common = field_container(text, "common_mean_confidence", "{")
    result = {}
    for name in ("sA_cell", "sB_cell", "j"):
        packets = selected_objects(field_container(common, name, "["), (0, 3))
        for row, packet in packets.items():
            lo, hi = F(packet["exact_lower"]), F(packet["exact_upper"])
            require(0 <= lo <= hi < 1, "invalid_training_confidence")
            result[name+"["+str(row)+"]"] = {"exact_lower":str(lo), "exact_upper":str(hi)}
    return result


def configuration():
    freeze = frozen(HERE/"criterion.md", FREEZE)
    frozen(HERE/"sources.json", FREEZE)
    matches = re.findall(r"<!-- FULL-FIBER-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- FULL-FIBER-FROZEN-END -->",
                         (HERE/"criterion.md").read_text(), re.S)
    require(len(matches) == 1, "nonunique_full_fiber_contract")
    config = json.loads(matches[0])
    manifest = json.loads((HERE/"sources.json").read_text())
    require(config["version"] == manifest["version"] == VERSION and
            config["status"] == manifest["status"] == "frozen_before_execution" and
            config["training_rows"] == [0, 3] and config["held_out_rows"] == [1, 2] and
            config["all_training_intervals_used"] is True and config["base_cover_dimensions"] == 5 and
            config["precision_digits"] == 50 and config["source_pair_cutoff"] == 6 and
            config["independent_trig_terms"] == 14 and config["binomial_terms"] == 14 and
            config["window_pulses"] == 5 and config["independent_split_cap"] == 24576 and
            config["max_depth"] == 48 and config["normalized_width_stop"] == "1/128" and
            config["witness_axis_fractions"] == ["1/2", "1/4", "3/4", "0", "1"] and
            config["witness_loss_denominator"] == 64 and config["member_limit"] == 256 and
            all(config[key] == value for key, value in SCOPE.items()), "full_fiber_contract_changed")
    bindings = {}
    for row in manifest["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and sha(path.read_bytes()) == row["sha256"], "full_fiber_input_changed")
        require(row["path"] not in bindings, "duplicate_full_fiber_input")
        bindings[row["path"]] = row["sha256"]
    freeze["sources_sha256"] = sha((HERE/"sources.json").read_bytes())
    return config, freeze, bindings


def training_means(training, config):
    ba, bb = map(F, config["background_per_pulse"])
    out = {"alpha":[], "beta":[], "joint":[]}
    for row in (0, 3):
        for key, field, background in (("alpha", "sA_cell", ba), ("beta", "sB_cell", bb)):
            value = unpack(training[field+"["+str(row)+"]"])
            root = 1+fifth_root_delta(-value, config)
            mean = (1-background)/root-1
            require(mean.lo > 0, "nonpositive_training_mean")
            out[key].append(mean)
        out["joint"].append(unpack(training["j["+str(row)+"]"]))
    return out


def initial_box(means, const):
    a0, a1 = means["alpha"]
    b0, b1 = means["beta"]
    s0, c0 = const["singles"][0]
    s1, c1 = const["singles"][1]
    require(s0.lo > 0 and s1.hi < 0 and (c0-c1).lo > 0, "single_axis_chart_not_certified")
    require(a1.lo > a0.hi and b1.lo > b0.hi, "source_axis_separation_not_certified")
    r = ((-s1)*a0+s0*a1)/((-s1)*b0+s0*b1)
    require(r.lo > 0, "loss_ratio_not_positive")
    z = ((a1-a0)+r*(b1-b0))/(2*(c0-c1))
    require(z.lo > 0, "source_z_not_positive")
    m = (a0+r*b0)/2+z*c0
    x = -(a0-r*b0)/(2*s0)
    axis_sum = (c0+c1).square()+(s0+s1).square()
    lower_eigenvalue = 2-axis_sum.sqrt()
    require(lower_eigenvalue.lo > 0, "nonparallel_direction_bound_unresolved")
    psd_m_upper = (a0+a1)/lower_eigenvalue
    m = I.raw(max(0, m.lo), min(m.hi, psd_m_upper.hi))
    e = I.raw(0, min(SCALE, r.hi))
    return [m, z, x, r, e], {"ratio_formula":"positive_weighted_four_single_ratio",
                            "source_axis_z_strictly_positive":True,
                            "PSD_two_nonparallel_directions_m_upper":psd_m_upper,
                            "loss_zero_only_outer_closure":True}


def linear_constraints(means, const):
    rows = []
    for index in range(2):
        s, c = const["singles"][index]
        rows.append({"name":"Alice"+str(index), "coefficients":[I(1), -c, -s, I(0), I(0)],
                     "lower":means["alpha"][index].lo, "upper":means["alpha"][index].hi})
        s, c = const["singles"][2+index]
        rows.extend((
            {"name":"Bob"+str(index)+"_lower", "coefficients":[I(1), -c, -s, -I.raw(means["beta"][index].lo, means["beta"][index].lo), I(0)],
             "lower":0, "upper":None},
            {"name":"Bob"+str(index)+"_upper", "coefficients":[I(1), -c, -s, -I.raw(means["beta"][index].hi, means["beta"][index].hi), I(0)],
             "lower":None, "upper":0}))
    return rows


def linear_contract(box, constraints):
    box, operations, sweeps = list(box), [], 0
    for sweep in range(8):
        changed = False
        sweeps = sweep+1
        for row_index, row in enumerate(constraints):
            coefficients = row["coefficients"]
            total = sum((a*b for a, b in zip(coefficients, box)), I(0))
            if ((row["lower"] is not None and total.hi < row["lower"]) or
                    (row["upper"] is not None and total.lo > row["upper"])):
                return None, {"reason":"strict_single_halfspace_violation", "constraint":row["name"],
                              "range":total, "sweeps":sweeps, "operations_sha256":sha(canonical(operations))}
            for axis, coefficient in enumerate(coefficients):
                if coefficient.lo <= 0 <= coefficient.hi:
                    continue
                rest = sum((coefficients[j]*box[j] for j in range(5) if j != axis), I(0))
                old = box[axis]
                lo, hi = old.lo, old.hi
                if row["lower"] is not None:
                    bound = I.raw(row["lower"]-rest.hi, row["lower"]-rest.hi)/coefficient
                    if coefficient.lo > 0:
                        lo = max(lo, bound.lo)
                    else:
                        hi = min(hi, bound.hi)
                if row["upper"] is not None:
                    bound = I.raw(row["upper"]-rest.lo, row["upper"]-rest.lo)/coefficient
                    if coefficient.lo > 0:
                        hi = min(hi, bound.hi)
                    else:
                        lo = max(lo, bound.lo)
                if lo > hi:
                    return None, {"reason":"empty_single_halfspace_projection", "constraint":row["name"],
                                  "axis":AXES[axis], "sweeps":sweeps, "operations_sha256":sha(canonical(operations))}
                if (lo, hi) != (old.lo, old.hi):
                    operations.append([row_index, axis, old.lo, old.hi, lo, hi])
                    box[axis] = I.raw(lo, hi)
                    changed = True
        m, z, x, r, e = box
        lo, hi = max(0, e.lo), min(e.hi, SCALE, r.hi)
        if lo > hi:
            return None, {"reason":"empty_physical_loss_projection", "sweeps":sweeps,
                          "operations_sha256":sha(canonical(operations))}
        if (lo, hi) != (e.lo, e.hi):
            operations.append(["physical_loss", 4, e.lo, e.hi, lo, hi])
            box[4] = I.raw(lo, hi)
            changed = True
        if r.lo < box[4].lo:
            operations.append(["loss_ratio", 3, r.lo, r.hi, box[4].lo, r.hi])
            box[3] = I.raw(box[4].lo, r.hi)
            changed = True
        if not changed:
            break
    return box, {"method":"directed_single_halfspace_and_physical_loss_projection",
                 "sweeps":sweeps, "update_count":len(operations), "operations_sha256":sha(canonical(operations))}


def population(box):
    m, z, x, _, e = box
    radius2 = z.square()+x.square()
    product = m.square()-radius2
    shifted = (m+e).square()-radius2
    if product.hi < 0 or shifted.hi < 0 or m.hi < 0:
        return None
    product = I.raw(max(0, product.lo), product.hi)
    shifted = I.raw(max(0, shifted.lo), shifted.hi)
    return {"R2":radius2, "T2":product*shifted, "population_product":product}


def clipped(value, lower, upper):
    out = value.intersect(I.raw(lower, upper))
    require(out is not None, "empty_legal_readout_outer")
    return out


def geometry(box, pop, const, cell_index, means=None):
    m, z, x, r, e = box
    cell = const["cells"][cell_index]
    ai, bi = cell["x"], cell["y"]
    sa, ca = const["singles"][ai]
    sb, cb = const["singles"][2+bi]
    alpha = m-z*ca-x*sa
    beta = (m-z*cb-x*sb)/r
    if means is not None:
        alpha = alpha.intersect(means["alpha"][ai])
        beta = beta.intersect(means["beta"][bi])
        require(alpha is not None and beta is not None, "single_range_outside_training")
    alpha = I.raw(max(0, alpha.lo), alpha.hi)
    beta = I.raw(max(0, beta.lo), beta.hi)
    radius2 = pop["R2"]
    require(radius2.lo > 0, "zero_source_axis_preserved_outer")
    d, Y = cell["d"], z*cell["sum_cos"]+x*cell["sum_sin"]
    A = m.square()+radius2+e*m
    Ccorr = (A*(radius2*d.square()+Y.square())-2*radius2*(2*m+e)*d*Y)/(2*r*radius2)
    require(Ccorr.hi >= 0, "negative_pair_correlation_outer")
    Ccorr = I.raw(max(0, Ccorr.lo), Ccorr.hi)
    g = (radius2*d.square()-Y.square())/(2*r*radius2)
    D = (1+alpha)*(1+beta)
    L = D-Ccorr
    require(L.hi >= SCALE, "Cauchy_phase_denominator_violation")
    L = I.raw(max(SCALE, L.lo), L.hi)
    E = L.square()-g.square()*pop["T2"]
    require(E.hi >= SCALE, "Cauchy_product_denominator_violation")
    E = I.raw(max(SCALE, E.lo), E.hi)
    ba, bb = const["background"]
    pa, pb = (alpha+ba)/(1+alpha), (beta+bb)/(1+beta)
    SA, SB = single_window(pa), single_window(pb)
    return {"alpha":alpha, "beta":beta, "D":D, "Ccorr":Ccorr, "L":L, "g":g,
            "E":E, "T2":pop["T2"], "pulse_A":pa, "pulse_B":pb, "SA":SA, "SB":SB}


def single_window(probability):
    return sum(((-1)**(k+1)*math.comb(5, k)*probability.power(k) for k in range(1, 6)), I(0))


def phase_slabs(box, pop, const, means, config):
    radius = pop["T2"].sqrt().hi
    common = I.raw(-radius, radius)
    slabs = []
    for index, target in zip((0, 3), means["joint"]):
        geo = geometry(box, pop, const, index, means)
        denominator = (1-geo["SA"])*(1-geo["SB"])
        rho = (target-geo["SA"]*geo["SB"])/denominator
        omega = fifth_root_delta(rho, config)
        rhs = (omega*geo["E"]-geo["Ccorr"]*geo["L"]-geo["g"].square()*pop["T2"])/geo["D"]
        product_range = geo["g"]*common
        if product_range.intersect(rhs) is None:
            return None, slabs+[{"cell":index, "g":geo["g"], "rhs":rhs,
                                 "reason":"strict_common_phase_slab_violation"}]
        if not geo["g"].lo <= 0 <= geo["g"].hi:
            inverse = rhs/geo["g"]
            updated = common.intersect(inverse)
            if updated is None:
                return None, slabs+[{"cell":index, "g":geo["g"], "rhs":rhs,
                                     "inverse":inverse, "reason":"empty_shared_phase_interval"}]
            common = updated
            mode = "directed_nonzero_coupling_inverse"
        else:
            mode = "zero_or_crossing_coupling_preserved_without_division"
        slabs.append({"cell":index, "g":geo["g"], "rhs":rhs, "common_k_after_slab":common, "mode":mode})
    return common, slabs


def padd(a, b):
    return [(a[j] if j < len(a) else I(0))+(b[j] if j < len(b) else I(0)) for j in range(max(len(a), len(b)))]


def pmul(a, b):
    out = [I(0) for _ in range(len(a)+len(b)-1)]
    for j, av in enumerate(a):
        for k, bv in enumerate(b):
            out[j+k] += av*bv
    return out


def pscale(a, factor):
    return [factor*value for value in a]


def pvalue(a, value):
    result = I(0)
    for coefficient in reversed(a):
        result = result*value+coefficient
    return result


def window_joint_coefficients(pa, pb, pulse_joint):
    result = pscale(pulse_joint, 5)
    base = padd([pa+pb], pscale(pulse_joint, -1))
    power = base
    for n in range(2, 6):
        power = pmul(power, base)
        term = padd(power, [-pa.power(n)-pb.power(n)])
        result = padd(result, pscale(term, (-1)**n*math.comb(5, n)))
    return result


def cell_readout(geo, k, const):
    a, b = geo["alpha"], geo["beta"]
    ba, bb = const["background"]
    background_factor = (1-ba)*(1-bb)
    raw_base = a*b/geo["D"]+(geo["Ccorr"]*geo["L"]+geo["g"].square()*geo["T2"])/(geo["E"]*geo["D"])
    pulse = [background_factor*raw_base+ba*(1-bb)*b/(1+b)+bb*(1-ba)*a/(1+a)+ba*bb,
             background_factor*geo["g"]/geo["E"]]
    coefficients = window_joint_coefficients(geo["pulse_A"], geo["pulse_B"], pulse)
    SA, SB = clipped(geo["SA"], 0, SCALE), clipped(geo["SB"], 0, SCALE)
    joint = clipped(pvalue(coefficients, k), 0, min(SA.hi, SB.hi))
    outcomes = [joint, clipped(SA-joint, 0, SCALE), clipped(SB-joint, 0, SCALE), clipped(1-SA-SB+joint, 0, SCALE)]
    return {"sA":SA, "sB":SB, "j":joint, "outcomes":outcomes,
            "pulse_joint_polynomial_in_common_k":pulse,
            "joint_polynomial_in_common_k":coefficients}


def unconstrained_cells():
    return [{"sA":I(0, 1), "sB":I(0, 1), "j":I(0, 1), "outcomes":[I(0, 1)]*4} for _ in range(4)]


def paired_readout(box, common, pop, const, means):
    cells = [cell_readout(geometry(box, pop, const, index, means), common, const) for index in range(4)]
    sum_coeff = padd(cells[1]["joint_polynomial_in_common_k"], cells[2]["joint_polynomial_in_common_k"])
    difference_coeff = padd(cells[1]["joint_polynomial_in_common_k"], pscale(cells[2]["joint_polynomial_in_common_k"], -1))
    ch_coeff = padd(padd(cells[0]["joint_polynomial_in_common_k"], sum_coeff), pscale(cells[3]["joint_polynomial_in_common_k"], -1))
    ch_coeff = padd(ch_coeff, [-cells[0]["sA"]-cells[0]["sB"]])
    return {"cells":cells, "joint_sum":clipped(pvalue(sum_coeff, common), 0, 2*SCALE),
            "joint_difference":clipped(pvalue(difference_coeff, common), -SCALE, SCALE),
            "CH_N5":clipped(pvalue(ch_coeff, common), -2*SCALE, 2*SCALE),
            "shared_phase_parameter":"same_k_in_all_cell_and_contrast_polynomials",
            "no_signaling_exact":{"A01_equals_A00":True, "A10_equals_A11":True,
                                    "B10_equals_B00":True, "B01_equals_B11":True}}


def cover(source_box, means, const, config):
    constraints = linear_constraints(means, const)
    widths = [value.width for value in source_box]
    require(all(width > 0 for width in widths), "zero_width_initial_source_box")
    stop = F(config["normalized_width_stop"])
    cap = config["independent_split_cap"]
    nodes, regions, pending, splits = [], [], [(0, None, source_box, 0)], 0
    next_id = 1
    while pending:
        node_id, parent, raw_box, depth = pending.pop()
        contracted, certificate = linear_contract(raw_box, constraints)
        node = {"id":node_id, "parent":parent, "depth":depth, "input_box":raw_box,
                "contracted_box":contracted, "contraction":certificate}
        nodes.append(node)
        if contracted is None:
            node.update(status="excluded", exclusion=certificate)
            continue
        pop = population(contracted)
        if pop is None:
            node.update(status="excluded", exclusion={"reason":"strict_PSD_population_violation"})
            continue
        try:
            common, slabs = phase_slabs(contracted, pop, const, means, config)
            node["phase_slabs"] = slabs
            if common is None:
                node.update(status="excluded", exclusion={"reason":"strict_training_joint_or_shared_phase_violation"})
                continue
            node["common_k"] = common
            phase_unresolved = None
        except (ValueError, ArithmeticError) as error:
            common = I.raw(-pop["T2"].sqrt().hi, pop["T2"].sqrt().hi)
            phase_unresolved = str(error)
            node.update(common_k=common, phase_unresolved=phase_unresolved)
        relative = [F(value.width, width) for value, width in zip(contracted, widths)]
        axis = max(range(5), key=lambda index:(relative[index], -index))
        if relative[axis] > stop and depth < config["max_depth"] and splits < cap:
            midpoint = (contracted[axis].lo+contracted[axis].hi)//2
            if contracted[axis].lo < midpoint < contracted[axis].hi:
                left, right = list(contracted), list(contracted)
                left[axis] = I.raw(contracted[axis].lo, midpoint)
                right[axis] = I.raw(midpoint, contracted[axis].hi)
                children = [next_id, next_id+1]
                next_id += 2
                splits += 1
                node.update(status="split", split_axis=AXES[axis], split_at=F(midpoint, SCALE), children=children)
                pending.append((children[1], node_id, right, depth+1))
                pending.append((children[0], node_id, left, depth+1))
                continue
        reason = ("normalized_width_reached" if relative[axis] <= stop else
                  "resource_split_cap_preserved" if splits >= cap else "depth_cap_preserved")
        node.update(status="retained_boundary", terminal_reason=reason, maximum_normalized_width=relative[axis])
        try:
            projection = paired_readout(contracted, common, pop, const, means)
        except (ValueError, ArithmeticError) as error:
            projection = {"cells":unconstrained_cells(), "joint_sum":I(0, 2), "joint_difference":I(-1, 1),
                          "CH_N5":I(-2, 2), "unresolved":str(error),
                          "shared_phase_parameter":"same_source_outer_preserved_without_projection"}
        regions.append({"node_id":node_id, "source_box":contracted, "common_k":common,
                        "T2":pop["T2"], "reason":reason, "projection":projection})
    nodes.sort(key=lambda item:item["id"])
    terminal = [node for node in nodes if node["status"] != "split"]
    summary = {"split_count":splits, "node_count":len(nodes), "terminal_leaf_count":len(terminal),
               "excluded_leaf_count":sum(node["status"] == "excluded" for node in terminal),
               "retained_leaf_count":len(regions),
               "cap_leaf_count":sum(node.get("terminal_reason") != "normalized_width_reached" for node in terminal if node["status"] != "excluded"),
               "resource_cap_triggered":any(node.get("terminal_reason") != "normalized_width_reached" for node in terminal if node["status"] != "excluded"),
               "base_dimensions":5, "phase_dimensions_enumerated":0,
               "all_boundary_and_cap_leaves_preserved":True, "complete_tree_verified":False}
    verify_tree(nodes, source_box, regions)
    summary["complete_tree_verified"] = True
    return nodes, regions, summary


def verify_tree(nodes, source_box, regions):
    by_id = {node["id"]:node for node in nodes}
    require(len(by_id) == len(nodes) and 0 in by_id, "duplicate_or_missing_cover_node")
    require(by_id[0]["parent"] is None and by_id[0]["input_box"] == source_box, "changed_cover_root")
    seen = set()
    stack = [0]
    retained = set()
    while stack:
        index = stack.pop()
        require(index not in seen and index in by_id, "duplicate_or_missing_cover_child")
        seen.add(index)
        node = by_id[index]
        status = node["status"]
        require(status in ("split", "excluded", "retained_boundary"), "unknown_cover_classification")
        if node["contracted_box"] is not None:
            require(all(new.contained(old) for new, old in zip(node["contracted_box"], node["input_box"])), "contractor_enlarged_box")
        if status == "split":
            require(len(node["children"]) == 2 and len(set(node["children"])) == 2, "invalid_cover_children")
            left, right = [by_id.get(child) for child in node["children"]]
            require(left is not None and right is not None, "missing_cover_child")
            axis = AXES.index(node["split_axis"])
            before = node["contracted_box"]
            require(left["parent"] == right["parent"] == index and left["depth"] == right["depth"] == node["depth"]+1,
                    "incorrect_cover_parent_or_depth")
            for j in range(5):
                if j == axis:
                    require(left["input_box"][j].lo == before[j].lo and right["input_box"][j].hi == before[j].hi and
                            left["input_box"][j].hi == right["input_box"][j].lo and
                            left["input_box"][j].width > 0 and right["input_box"][j].width > 0,
                            "cover_split_gap_or_overlap")
                else:
                    require(left["input_box"][j] == right["input_box"][j] == before[j], "changed_nonsplit_axis")
            stack.extend(node["children"])
        elif status == "retained_boundary":
            retained.add(index)
    require(seen == set(by_id), "unreachable_cover_node")
    ids = [region["node_id"] for region in regions]
    require(len(ids) == len(set(ids)) and set(ids) == retained, "missing_or_duplicate_retained_projection")
    return True


def member_shape(raw_probabilities, config, const):
    ba, bb = const["background"]
    alpha, beta = [], []
    for index in range(2):
        alpha.append((1-ba)/(1+fifth_root_delta(-I(raw_probabilities[2*index]), config))-1)
        beta.append((1-bb)/(1+fifth_root_delta(-I(raw_probabilities[2*index+1]), config))-1)
    ar, br = alpha[1]/alpha[0], beta[1]/beta[0]
    s0, c0 = const["singles"][0]
    s1, c1 = const["singles"][1]
    matrix = ((ar*c0-c1, ar*s0-s1), (br*c0-c1, s1-br*s0))
    rhs = (ar-1, br-1)
    det = matrix[0][0]*matrix[1][1]-matrix[0][1]*matrix[1][0]
    require(not det.lo <= 0 <= det.hi, "member_ratio_determinant_unresolved")
    Z = (rhs[0]*matrix[1][1]-matrix[0][1]*rhs[1])/det
    X = (matrix[0][0]*rhs[1]-rhs[0]*matrix[1][0])/det
    m = alpha[0]/(1-Z*c0-X*s0)
    r = m*(1-Z*c0+X*s0)/beta[0]
    return [m, m*Z, m*X, r], {"normalized_axis":(Z, X), "ratio_determinant":det,
                            "coordinate_space":"original_single_probability_CI",
                            "four_single_coordinates":raw_probabilities}


def mm(a, b):
    return tuple(tuple(sum((a[i][k]*b[k][j] for k in range(2)), I(0)) for j in range(2)) for i in range(2))


def transpose(a):
    return tuple(tuple(a[j][i] for j in range(2)) for i in range(2))


@lru_cache(maxsize=256)
def occupation_factor(n, row, col):
    return I(F(math.factorial(row)*math.factorial(n-row), math.factorial(col)*math.factorial(n-col))).sqrt()


def gamma(matrix, n):
    powers = {(i, j):[matrix[i][j].power(k) for k in range(n+1)] for i in range(2) for j in range(2)}
    result = []
    for row in range(n+1):
        cells = []
        for col in range(n+1):
            value = I(0)
            for k in range(max(0, row-(n-col)), min(row, col)+1):
                value += (math.comb(col, k)*math.comb(n-col, row-k)*
                          powers[0, 0][k]*powers[1, 0][col-k]*
                          powers[0, 1][row-k]*powers[1, 1][n-col-row+k])
            cells.append(value*occupation_factor(n, row, col))
        result.append(cells)
    return result


def physical_source(box, k):
    m, z, x, r, e = box
    require(e.lo > 0 and e.hi <= SCALE and r.lo >= e.hi, "member_loss_not_legal")
    C = (z.square()+x.square()).sqrt()
    h, v = m+C, m-C
    require(h.lo > 0 and v.lo >= 0 and C.lo > 0, "member_population_or_axis_not_legal")
    T = (h*v*(h+e)*(v+e)).sqrt()
    if T.hi == 0:
        require(k.lo == k.hi == 0, "pure_mode_nonzero_k")
        coherence = I(-1, 1)
    else:
        require(T.lo > 0, "member_T_boundary_unresolved")
        coherence = k/T
        require(coherence.lo >= -SCALE and coherence.hi <= SCALE, "member_phase_not_legal")
    cos2, sin2 = z/C, x/C
    cr = ((1+cos2)/2).sqrt()
    require(cr.lo > 0, "member_half_angle_boundary")
    sr = sin2/(2*cr)
    return {"tH":h/(h+e), "tV":v/(v+e), "etaA":e, "etaB":e/r,
            "R":((cr, sr), (-sr, cr)), "coherence":coherence, "lambda":(1-coherence)/2,
            "h":h, "v":v, "r":r, "e":e, "common_k":k, "T":T,
            "pure_mode_phase_equivalence":T.hi == 0}


def fock_readout(source, const, cutoff=6, phase_after_window=False, renormalize=False):
    th, tv = source["tH"], source["tV"]
    Z = (1-th)*(1-tv)
    tail = th.power(cutoff+1)+(1-th)*sum((th.power(h)*tv.power(cutoff+1-h) for h in range(cutoff+1)), I(0))
    require(0 <= tail.lo <= tail.hi < SCALE, "invalid_original_source_tail")
    ta, tb = source["etaA"], source["etaB"]
    wa = [I(0)]+[1-(1-ta).power(n) for n in range(1, cutoff+1)]
    wb = [I(0)]+[1-(1-tb).power(n) for n in range(1, cutoff+1)]
    ba, bb = const["background"]
    cells = []
    for x, y in itertools.product(range(2), repeat=2):
        sa, ca = trig(const["angles"][x])
        sb, cb = trig(const["angles"][2+y])
        OA, OB = ((sa, ca), (ca, -sa)), ((sb, cb), (cb, -sb))
        branches = []
        for phase in (1, -1):
            diagonal = ((th.sqrt(), I(0)), (I(0), phase*tv.sqrt()))
            G = mm(mm(source["R"], diagonal), transpose(source["R"]))
            receiver_kernel = mm(mm(OA, G), transpose(OB))
            prefix = {"A":I(0), "B":I(0), "J":I(0)}
            for n in range(1, cutoff+1):
                amplitudes = gamma(receiver_kernel, n)
                for k in range(n+1):
                    for l in range(n+1):
                        mass = Z*amplitudes[k][l].square()
                        prefix["A"] += mass*wa[k]
                        prefix["B"] += mass*wb[l]
                        prefix["J"] += mass*wa[k]*wb[l]
            if renormalize:
                prefix = {key:value/(1-tail) for key, value in prefix.items()}
            values = {key:value+I.raw(0, tail.hi) for key, value in prefix.items()}
            branches.append(values)
        mixed = {key:(branches[0][key]+branches[1][key])/2+
                 source["coherence"]*(branches[0][key]-branches[1][key])/2 for key in ("A", "B", "J")}
        def full_window(physical):
            pa, pb = ba+(1-ba)*physical["A"], bb+(1-bb)*physical["B"]
            joint = ((1-ba)*(1-bb)*physical["J"]+ba*(1-bb)*physical["B"]+
                     bb*(1-ba)*physical["A"]+ba*bb)
            SA, SB = single_window(pa), single_window(pb)
            J = pvalue(window_joint_coefficients(pa, pb, [joint]), I(0))
            return {"sA":SA, "sB":SB, "j":J, "outcomes":[J, SA-J, SB-J, 1-SA-SB+J]}
        if phase_after_window:
            windows = list(map(full_window, branches))
            row = {key:(windows[0][key]+windows[1][key])/2+source["coherence"]*(windows[0][key]-windows[1][key])/2
                   for key in ("sA", "sB", "j")}
            row["outcomes"] = [row["j"], row["sA"]-row["j"], row["sB"]-row["j"], 1-row["sA"]-row["sB"]+row["j"]]
        else:
            row = full_window(mixed)
        row.update(setting=[x, y], pulse_positive_Born=mixed)
        cells.append(row)
    return {"cells":cells, "source_omitted_mass":tail, "cutoff":cutoff, "vacuum_clicked_Born_exactly_zero":True,
            "normalized_occupation_amplitudes":True, "finite_prefix_renormalized":renormalize,
            "phase_mixture_before_window":not phase_after_window, "tail_is_original_numberMass":True}


def legal_member(training, means, raw_points, fractions, shape, loss, phase_recipe, k, const, config):
    box = shape+[I(loss)]
    source = physical_source(box, I(k))
    pop = population(box)
    require(pop is not None, "member_PSD_not_legal")
    gaussian = paired_readout(box, I(k), pop, const, means)
    born = fock_readout(source, const, config["source_pair_cutoff"])
    checks = []
    for field, row in FIELDS:
        name = {"sA_cell":"sA", "sB_cell":"sB", "j":"j"}[field]
        target_packet = training[field+"["+str(row)+"]"]
        actual = born["cells"][row][name]
        require(actual.within_exact(target_packet), "member_actual_Born_training_CI_not_contained")
        checks.append({"field":field+"["+str(row)+"]", "probability":actual, "CI":target_packet, "contained":True})
    cross = []
    tolerance = F(config["comparison_tolerance"])*SCALE
    for row in range(4):
        for field in ("sA", "sB", "j"):
            left, right = gaussian["cells"][row][field], born["cells"][row][field]
            require(left.intersect(right) is not None and right.width <= tolerance,
                    "member_Gaussian_positive_Born_cross_unresolved")
            cross.append({"row":row, "field":field, "Gaussian":left, "positive_Born":right, "intersects":True})
    return {"recipe":{"coordinate_space":"original_single_probability_CI", "axis_fractions":fractions,
                      "single_probability_coordinates":raw_points, "loss":loss, "phase_recipe":phase_recipe,
                      "rational_common_k":k},
            "source":source, "source_box":box, "physical_legal":True,
            "all_six_training_CI_contained":True, "training_checks":checks,
            "paired_Gaussian_readout":gaussian, "actual_positive_Fock_readout":born,
            "Gaussian_positive_Fock_cross":cross, "heldout_used_for_selection":False}


def generate_members(training, means, const, config):
    fractions = tuple(map(F, config["witness_axis_fractions"]))
    probability_boxes = [(F(training[field+"["+str(row)+"]"]["exact_lower"]),
                          F(training[field+"["+str(row)+"]"]["exact_upper"])) for field, row in FIELDS[:4]]
    members, rejection_counts, digest = [], {}, hashlib.sha256()
    attempted, reached_limit = 0, False
    for fs in itertools.product(fractions, repeat=4):
        raw_points = [lo+fraction*(hi-lo) for (lo, hi), fraction in zip(probability_boxes, fs)]
        try:
            shape, reconstruction = member_shape(raw_points, config, const)
        except (ValueError, ArithmeticError) as error:
            rejection_counts[str(error)] = rejection_counts.get(str(error), 0)+1
            digest.update(canonical({"fractions":fs, "reason":str(error)}))
            continue
        for j in range(1, config["witness_loss_denominator"]+1):
            loss = F(j, config["witness_loss_denominator"])
            box = shape+[I(loss)]
            try:
                require(box[3].lo >= box[4].hi, "candidate_loss_above_ratio")
                pop = population(box)
                require(pop is not None, "candidate_non_PSD_source")
                common, _ = phase_slabs(box, pop, const, means, config)
                require(common is not None, "candidate_empty_joint_phase_intersection")
            except (ValueError, ArithmeticError) as error:
                rejection_counts[str(error)] = rejection_counts.get(str(error), 0)+1
                digest.update(canonical({"fractions":fs, "loss":loss, "reason":str(error)}))
                continue
            phase_values = (("midpoint", common.midpoint()), ("lower", F(common.lo, SCALE)), ("upper", F(common.hi, SCALE)))
            for phase_recipe, k in phase_values:
                attempted += 1
                try:
                    member = legal_member(training, means, raw_points, fs, shape, loss, phase_recipe, k, const, config)
                    member["id"] = len(members)
                    member["single_reconstruction"] = reconstruction
                    members.append(member)
                    digest.update(canonical({"recipe":member["recipe"], "qualified":True}))
                except (ValueError, ArithmeticError) as error:
                    rejection_counts[str(error)] = rejection_counts.get(str(error), 0)+1
                    digest.update(canonical({"fractions":fs, "loss":loss, "phase":phase_recipe, "k":k, "reason":str(error)}))
                if len(members) >= config["member_limit"]:
                    reached_limit = True
                    break
            if reached_limit:
                break
        if reached_limit:
            break
    return members, {"coordinate_space":"original_single_probability_CI", "axis_order":[field+"["+str(row)+"]" for field, row in FIELDS[:4]],
                     "axis_fractions":fractions, "loss_denominator":config["witness_loss_denominator"],
                     "phase_order":["midpoint", "lower", "upper"], "member_count":len(members),
                     "member_limit_reached":reached_limit, "phase_candidates_attempted":attempted,
                     "rejection_counts":rejection_counts, "selection_trace_sha256":digest.hexdigest(),
                     "heldout_accessed_in_selection":False}


def hull(values):
    return None if not values else I.raw(min(value.lo for value in values), max(value.hi for value in values))


def projection_summary(regions):
    cells = [{name:hull([region["projection"]["cells"][row][name] for region in regions]) for name in ("sA", "sB", "j")}
             for row in range(4)]
    return {"cell_component_hulls":cells,
            **{name:hull([region["projection"][name] for region in regions]) for name in ("joint_sum", "joint_difference", "CH_N5")},
            "component_hulls_are_not_joint_feasibility_certificates":True}


def source_stage(training, config):
    const = constants(config)
    means = training_means(training, config)
    initial, initial_evidence = initial_box(means, const)
    tree, regions, coverage = cover(initial, means, const, config)
    members, member_search = generate_members(training, means, const, config)
    return {"training_view":training, "design_exposure":{"common_N":177358351, "alpha":config["alpha"],
             "features_in_global_union":config["features_in_global_union"], "fixed_bets":config["fixed_bets"],
             "runs_covered":config["runs_covered"], "pulse_subsets_covered":config["pulse_subsets_covered"]},
            "source_chart":"m_z_x_r_e_with_complete_common_k_slab", "axes":AXES,
            "training_means":means, "initial_source_box":initial, "initial_box_evidence":initial_evidence,
            "linear_single_constraints":linear_constraints(means, const), "cover_tree":tree,
            "coverage":coverage, "paired_regions":regions, "projection_summary":projection_summary(regions),
            "members":members, "member_search":member_search,
            "nonempty_training_fiber_certified":bool(members),
            "full_statistical_fiber_outer_coverage_certified":coverage["complete_tree_verified"],
            "conditional_source_law":config["conditional_source_law"],
            "source_and_predictions_formed_before_heldout_decode":True,
            "no_signaling_exact":{"A01_equals_A00":True, "A10_equals_A11":True,
                                    "B10_equals_B00":True, "B01_equals_B11":True}}


def compare(source, report_text):
    confidence = json.loads(report_text)["common_mean_confidence"]
    comparisons, counterexamples, all_ci_ids = [], [], []
    for row in (1, 2):
        hulls = source["projection_summary"]["cell_component_hulls"][row]
        for field, name in (("sA_cell", "sA"), ("sB_cell", "sB"), ("j", "j")):
            ci = confidence[field][row]
            target = I(ci["exact_lower"], ci["exact_upper"])
            envelope = hulls[name]
            comparisons.append({"row":row, "field":field, "prediction_hull":envelope, "original_CI":target,
                                "uniform_outer_contained":envelope is not None and envelope.within_exact(ci)})
    for member in source["members"]:
        all_inside = True
        for row in range(4):
            for field, name in (("sA_cell", "sA"), ("sB_cell", "sB"), ("j", "j")):
                ci = confidence[field][row]
                target = I(ci["exact_lower"], ci["exact_upper"])
                value = member["actual_positive_Fock_readout"]["cells"][row][name]
                if not value.within_exact(ci):
                    all_inside = False
                if row in (1, 2) and value.disjoint_exact(ci):
                    counterexamples.append({"member_id":member["id"], "row":row, "field":field,
                                            "probability":value, "original_CI":target,
                                            "all_six_training_CI_contained":True})
        if all_inside:
            all_ci_ids.append(member["id"])
    uniform = bool(source["paired_regions"]) and all(row["uniform_outer_contained"] for row in comparisons)
    verdict = ("FULL_TRAINING_FIBER_PREDICTION_OUTER_CONTAINED" if uniform else
               "TRAINING_LEGAL_MEMBER_OUTSIDE_HELDOUT_CI" if counterexamples else "FULL_FIBER_OUTER_NOT_DECISIVE")
    return {"status":verdict, "uniform_heldout_contained":uniform,
            "heldout_comparisons":comparisons, "training_legal_heldout_counterexamples":counterexamples,
            "retrospective_all_CI_member_ids":all_ci_ids,
            "retrospective_all_CI_filter_is_not_new_heldout_prediction":True,
            "heldout_source_domain_feedback":False}


def science():
    executable = frozen(__file__)
    config, freeze, bindings = configuration()
    report_path = HERE.parent.parent/"observable-prediction/public-comparison-po0003.json"
    text = report_path.read_text()
    training = parse_training(text)
    stage = source_stage(training, config)
    stage_hash = sha(canonical(stage))
    comparison = compare(stage, text)
    return serial({"schema":SCHEMA, "version":VERSION, "criterion_freeze":freeze,
                   "executable_freeze":executable, "bindings":bindings, "source_stage_sha256":stage_hash,
                   "source_stage":stage, "comparison":comparison,
                   "primary_new_code_or_outputs_read_before_first":False,
                   "foreign_source_fields_used_as_forward_inputs":False,
                   "statistical_independence_claimed":False, **SCOPE})


def save_first(result, output):
    logical = (json.dumps(result, sort_keys=True, indent=2, allow_nan=False)+"\n").encode()
    compressed = gzip.compress(logical, compresslevel=9, mtime=0)
    require(not output.exists(), "refusing_to_overwrite_frozen_independent_first")
    output.write_bytes(compressed)
    storage = output.with_name(output.name[:-8]+"-storage.json") if output.name.endswith(".json.gz") else output.with_suffix(".storage.json")
    require(not storage.exists(), "refusing_to_overwrite_independent_storage_receipt")
    metadata = {"schema":"p23-lossless-first-storage/v1", "version":VERSION, "path":output.name,
                "logical_bytes":len(logical), "logical_json_sha256":sha(logical),
                "gzip_bytes":len(compressed), "gzip_sha256":sha(compressed),
                "source_stage_sha256":result["source_stage_sha256"], "gzip_mtime":0,
                "lossless_json_bytes":True, "first_science_outcome":result["comparison"]["status"]}
    storage.write_text(json.dumps(metadata, sort_keys=True, indent=2)+"\n")
    return metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = science()
    print(json.dumps(save_first(result, args.output), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
