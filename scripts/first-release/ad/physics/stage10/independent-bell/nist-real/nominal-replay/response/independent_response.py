"""Independent density-matrix response and exact rational interval certificate."""
from __future__ import annotations

import functools
import argparse
import ast
import hashlib
import importlib.util
import itertools
import json
import math
import re
import subprocess
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
CRITERION = HERE / "criterion.md"
OUTPUT = HERE / "independent_response.json"
FROZEN_COMMIT = "b818e92fbdeca40d4a34c26e4bbf5ad90a0a4f80"
FROZEN_SHA256 = "63dd1df90a93c4a7a9b127514e63da5bfa1de1f0c57784f16f50ee85149f5bfc"
COMPUTATION_AST_SHA256 = "3e5c13e701ebf742c6872e991d9e96699ada4bfea65b43071c14ac57cf2210d0"
COMPUTATION_NAMES = {
    "criterion_freeze", "load_frozen", "Interval", "taylor_endpoint", "sin_interval", "cos_interval",
    "trig_degrees", "Polynomial", "kronecker", "trace_product", "partial_matrices", "generated_source",
    "generated_responses", "symbolic_projector", "generated_score", "score_factorization", "MatrixModel",
    "source_parameters", "response_interval", "path_improvement", "read_inputs", "robust_score_interval",
    "positive_branch", "point_environment", "matrix_controls", "case_result", "center_controls"
}


def criterion_freeze():
    if FROZEN_COMMIT is None:
        raise ValueError("the owning thread has not announced the response freeze")
    path = str(CRITERION.relative_to(ROOT))
    committed = subprocess.check_output(["git", "show", f"{FROZEN_COMMIT}:{path}"], cwd=ROOT)
    if committed != CRITERION.read_bytes():
        raise ValueError("response criterion differs from its frozen commit")
    digest = hashlib.sha256(committed).hexdigest()
    if digest != FROZEN_SHA256:
        raise ValueError("criterion digest differs from the announced scientific freeze")
    return {"commit": FROZEN_COMMIT, "sha256": digest, "path": path}


def load_frozen():
    criterion_freeze()
    text = CRITERION.read_text()
    blocks = re.findall(r"```json\s*(.*?)\s*```", text, re.S)
    if len(blocks) != 1:
        raise ValueError("one machine-readable criterion block is required")
    return json.loads(blocks[0])


class Interval:
    def __init__(self, lower, upper=None):
        self.lower = F(lower)
        self.upper = self.lower if upper is None else F(upper)
        if self.lower > self.upper:
            raise ValueError("reversed interval")

    @staticmethod
    def cast(value):
        return value if isinstance(value, Interval) else Interval(value)

    def __add__(self, other):
        other = self.cast(other)
        return Interval(self.lower + other.lower, self.upper + other.upper)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.upper, -self.lower)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) - self

    def __mul__(self, other):
        other = self.cast(other)
        values = [a*b for a in (self.lower, self.upper) for b in (other.lower, other.upper)]
        return Interval(min(values), max(values))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.lower <= 0 <= self.upper:
            raise ValueError("interval division crosses zero")
        return Interval(1/self.upper, 1/self.lower)

    def __truediv__(self, other):
        return self * self.cast(other).reciprocal()

    def __pow__(self, exponent):
        if exponent < 0:
            return self.reciprocal() ** (-exponent)
        if exponent == 0:
            return Interval(1)
        if exponent % 2 == 0:
            upper = max(abs(self.lower), abs(self.upper)) ** exponent
            lower = 0 if self.lower <= 0 <= self.upper else min(abs(self.lower), abs(self.upper)) ** exponent
            return Interval(lower, upper)
        return Interval(self.lower ** exponent, self.upper ** exponent)

    def shifted_path(self, displacement):
        return Interval(self.lower + min(F(displacement), 0), self.upper + max(F(displacement), 0))

    def json(self, digits=18):
        scale = 10**digits
        lo = (self.lower.numerator*scale) // self.lower.denominator
        hi = -((-self.upper.numerator*scale) // self.upper.denominator)

        def decimal(integer):
            sign = "-" if integer < 0 else ""
            whole, fraction = divmod(abs(integer), scale)
            return f"{sign}{whole}.{fraction:0{digits}d}"

        # These decimal strings are exact rational endpoints rounded outwards.
        return {"lower": decimal(lo), "upper": decimal(hi),
                "exact_lower": str(self.lower), "exact_upper": str(self.upper)}


@functools.lru_cache(maxsize=256)
def taylor_endpoint(kind, x, terms=14):
    x = F(x)
    if kind == "sin":
        value = sum(((-1)**k * x**(2*k+1) / math.factorial(2*k+1) for k in range(terms)), F(0))
        degree = 2*terms-1
    elif kind == "cos":
        value = sum(((-1)**k * x**(2*k) / math.factorial(2*k) for k in range(terms)), F(0))
        degree = 2*terms-2
    else:
        raise ValueError("unsupported Taylor function")
    remainder = abs(x)**(degree+1) / math.factorial(degree+1)
    return Interval(value-remainder, value+remainder)


def sin_interval(x, pi):
    if x.lower < -pi.lower/2 or x.upper > pi.lower/2:
        raise ValueError("sine monotonicity domain not covered")
    return Interval(taylor_endpoint("sin", x.lower).lower,
                    taylor_endpoint("sin", x.upper).upper)


def cos_interval(x, pi):
    maximum = max(abs(x.lower), abs(x.upper))
    if maximum > pi.lower:
        raise ValueError("cosine monotonicity domain not covered")
    minimum = 0 if x.lower <= 0 <= x.upper else min(abs(x.lower), abs(x.upper))
    return Interval(taylor_endpoint("cos", maximum).lower,
                    1 if minimum == 0 else taylor_endpoint("cos", minimum).upper)


def trig_degrees(degrees, pi, multiplier=2):
    radians = degrees * pi * F(multiplier, 180)
    return sin_interval(radians, pi), cos_interval(radians, pi)


class Polynomial:
    def __init__(self, value=0, *, coefficients=None):
        self.coefficients = {(): F(value)} if coefficients is None else dict(coefficients)
        self.coefficients = {m: c for m, c in self.coefficients.items() if c}

    @staticmethod
    def variable(name):
        return Polynomial(coefficients={((name, 1),): F(1)})

    @staticmethod
    def cast(value):
        return value if isinstance(value, Polynomial) else Polynomial(value)

    def __add__(self, other):
        values = dict(self.coefficients)
        for monomial, coefficient in self.cast(other).coefficients.items():
            values[monomial] = values.get(monomial, F(0)) + coefficient
        return Polynomial(coefficients=values)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial(coefficients={m: -c for m, c in self.coefficients.items()})

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) - self

    def __mul__(self, other):
        values = {}
        for m, coefficient in self.coefficients.items():
            for n, other_coefficient in self.cast(other).coefficients.items():
                powers = dict(m)
                for variable, exponent in n:
                    powers[variable] = powers.get(variable, 0) + exponent
                monomial = tuple(sorted(powers.items()))
                values[monomial] = values.get(monomial, F(0)) + coefficient*other_coefficient
        return Polynomial(coefficients=values)

    __rmul__ = __mul__

    def __truediv__(self, value):
        return self * (1/F(value))

    def evaluate_combined(self, environment):
        result = Interval(0)
        for monomial, coefficient in self.coefficients.items():
            powers = dict(monomial)
            if powers.get("ax", 0) != powers.get("bx", 0) or powers.get("az", 0) != powers.get("bz", 0):
                raise ValueError("Pauli placement did not cancel in the generated response")
            term = Interval(coefficient)
            term *= environment["xi"] ** powers.pop("ax", 0)
            powers.pop("bx", None)
            term *= environment["zeta"] ** powers.pop("az", 0)
            powers.pop("bz", None)
            for variable, exponent in powers.items():
                term *= environment[variable] ** exponent
            result += term
        return result

    def evaluate_scalar(self, environment):
        return sum(float(coefficient)*math.prod(environment[name]**exponent for name, exponent in monomial)
                   for monomial, coefficient in self.coefficients.items())

    def json(self):
        return [{"coefficient": str(c), "powers": dict(m)}
                for m, c in sorted(self.coefficients.items())]


def kronecker(a, b):
    return [[a[i//len(b)][j//len(b)] * b[i % len(b)][j % len(b)]
             for j in range(len(a)*len(b))] for i in range(len(a)*len(b))]


def trace_product(a, b):
    return sum((a[i][j]*b[j][i] for i in range(len(a)) for j in range(len(a))), Polynomial(0))


def partial_matrices(rho):
    alice = [[rho[2*i][2*j]+rho[2*i+1][2*j+1] for j in range(2)] for i in range(2)]
    bob = [[rho[i][j]+rho[2+i][2+j] for j in range(2)] for i in range(2)]
    return alice, bob


@functools.lru_cache(maxsize=1)
def generated_source():
    variable = Polynomial.variable
    delta, coherence = variable("delta"), variable("chi")
    # Exact outer-product entries of (r|VV>+|HH>)/sqrt(1+r²).
    pure = [[Polynomial(0) for _ in range(4)] for _ in range(4)]
    pure[0][0], pure[3][3] = (1+delta)/2, (1-delta)/2
    pure[0][3] = pure[3][0] = coherence/2
    rho = [[Polynomial(0) for _ in range(4)] for _ in range(4)]
    for za, xa, zb, xb in itertools.product((0, 1), repeat=4):
        weight = ((1+(-1)**za*variable("ax")) * (1+(-1)**xa*variable("az")) *
                  (1+(-1)**zb*variable("bx")) * (1+(-1)**xb*variable("bz"))) / 16
        for i in range(4):
            for j in range(4):
                source_i = 2*((i//2)^xa) + ((i % 2)^xb)
                source_j = 2*((j//2)^xa) + ((j % 2)^xb)
                sign = (-1)**(za*(i//2+j//2)+zb*(i % 2+j % 2))
                rho[i][j] += weight*sign*pure[source_i][source_j]
    alice, bob = partial_matrices(rho)
    return rho, alice, bob


@functools.lru_cache(maxsize=1)
def generated_responses():
    variable = Polynomial.variable
    rho, alice, bob = generated_source()
    s, c, dc, ds = (variable(name) for name in ("s", "c", "dc", "ds"))
    derivative = [[-s, c], [c, s]]
    difference = [[dc/2, ds/2], [ds/2, -dc/2]]
    q = variable("q")
    response_a = trace_product(rho, kronecker(derivative, difference)) + q*trace_product(alice, derivative)*trace_product(bob, difference)
    response_b = trace_product(rho, kronecker(difference, derivative)) + q*trace_product(bob, derivative)*trace_product(alice, difference)
    return response_a, response_b


def symbolic_projector(cosine, sine):
    return [[(1+cosine)/2, sine/2], [sine/2, (1-cosine)/2]]


@functools.lru_cache(maxsize=1)
def generated_score():
    variable = Polynomial.variable
    rho, alice, bob = generated_source()
    ea, eb, q, ba, bb = (variable(name) for name in ("ea", "eb", "q", "ba", "bb"))
    projectors_a = [symbolic_projector(variable("ca"+str(i)), variable("sa"+str(i))) for i in (0, 1)]
    projectors_b = [symbolic_projector(variable("cb"+str(i)), variable("sb"+str(i))) for i in (0, 1)]
    pa = [trace_product(alice, p) for p in projectors_a]
    pb = [trace_product(bob, p) for p in projectors_b]
    sa = [q*ea*p+ba for p in pa]
    sb = [q*eb*p+bb for p in pb]
    result = -sa[0]-sb[0]
    for i, j in itertools.product((0, 1), repeat=2):
        sign = -1 if i == j == 1 else 1
        result += sign*(q*ea*eb*trace_product(rho, kronecker(projectors_a[i], projectors_b[j]))+sa[i]*sb[j])
    if any(dict(m).get("ea", 0) > 1 or dict(m).get("eb", 0) > 1 for m in result.coefficients):
        raise ValueError("source-contracted CH is not bilinear in detector efficiencies")
    return result


@functools.lru_cache(maxsize=1)
def score_factorization():
    v = Polynomial.variable
    ea, eb, q, ba, bb, d, ch, az, bz, ax, bx = (v(name) for name in
                                             ("ea", "eb", "q", "ba", "bb", "delta", "chi", "az", "bz", "ax", "bx"))
    ca0, ca1, cb0, cb1, sa0, sa1, sb0, sb1 = (v(name) for name in
                                             ("ca0", "ca1", "cb0", "cb1", "sa0", "sa1", "sb0", "sb1"))
    zz = ca0*(cb0+cb1)+ca1*(cb0-cb1)
    xx = sa0*(sb0+sb1)+sa1*(sb0-sb1)
    linear = ((ea*eb-ea-eb)/2 + d*az*ca0*ea*(eb-1+2*bb)/2 +
              d*bz*cb0*eb*(ea-1+2*ba)/2 + ea*eb*(az*bz*zz+ax*bx*ch*xx)/4+ea*bb+eb*ba)
    quadratic = ea*eb*(2+2*d*(az*ca0+bz*cb0)+d*d*az*bz*zz)/4
    constant = 2*ba*bb-ba-bb
    if (generated_score()-(q*linear+q*q*quadratic+constant)).coefficients:
        raise ValueError("factorization differs from the generated density-matrix contraction")
    return linear, quadratic, constant


class MatrixModel:
    def __init__(self, r, ax, az, bx, bz, eta_a, eta_b, q, background_a, background_b):
        criterion_freeze()
        import numpy as np
        self.np = np
        self.eta_a, self.eta_b, self.q = eta_a, eta_b, q
        self.background_a, self.background_b = background_a, background_b
        vector = np.array([r, 0, 0, 1], dtype=complex) / math.sqrt(1+r*r)
        pure = np.outer(vector, vector.conj())
        identity = np.eye(2, dtype=complex)
        x = np.array([[0, 1], [1, 0]], dtype=complex)
        z = np.diag([1, -1]).astype(complex)
        self.rho = np.zeros((4, 4), dtype=complex)
        for za, xa, zb, xb in itertools.product((0, 1), repeat=4):
            weight = ((1+(-1)**za*ax)*(1+(-1)**xa*az)*
                      (1+(-1)**zb*bx)*(1+(-1)**xb*bz)) / 16
            ua = (z if za else identity) @ (x if xa else identity)
            ub = (z if zb else identity) @ (x if xb else identity)
            operator = np.kron(ua, ub)
            self.rho += weight*(operator @ pure @ operator.conj().T)
        tensor = self.rho.reshape(2, 2, 2, 2)
        self.alice = np.trace(tensor, axis1=1, axis2=3)
        self.bob = np.trace(tensor, axis1=0, axis2=2)

    def projector(self, degrees, derivative=False):
        t = math.radians(degrees)
        v = self.np.array([math.cos(t), math.sin(t)])
        if derivative:
            dv = self.np.array([-math.sin(t), math.cos(t)])
            return self.np.outer(dv, v)+self.np.outer(v, dv)
        return self.np.outer(v, v)

    def probabilities(self, a, b):
        pa, pb = self.projector(a), self.projector(b)
        joint = float(self.np.trace(self.rho @ self.np.kron(pa, pb)).real)
        alice = float(self.np.trace(self.alice @ pa).real)
        bob = float(self.np.trace(self.bob @ pb).real)
        return joint, alice, bob

    def measured(self, a, b):
        joint, alice, bob = self.probabilities(a, b)
        sa = self.q*self.eta_a*alice+self.background_a
        sb = self.q*self.eta_b*bob+self.background_b
        return self.q*self.eta_a*self.eta_b*joint+sa*sb, sa, sb

    def score(self, angles):
        a0, a1, b0, b1 = angles
        j00, sa, sb = self.measured(a0, b0)
        return j00+self.measured(a0, b1)[0]+self.measured(a1, b0)[0]-self.measured(a1, b1)[0]-sa-sb

    def primed_derivative(self, angles, side):
        a0, a1, b0, b1 = angles
        if side == "alice":
            dp = self.projector(a1, True)
            diff = self.projector(b0)-self.projector(b1)
            pair = self.np.trace(self.rho @ self.np.kron(dp, diff)).real
            extra = self.np.trace(self.alice @ dp).real*self.np.trace(self.bob @ diff).real
        elif side == "bob":
            dp = self.projector(b1, True)
            diff = self.projector(a0)-self.projector(a1)
            pair = self.np.trace(self.rho @ self.np.kron(diff, dp)).real
            extra = self.np.trace(self.bob @ dp).real*self.np.trace(self.alice @ diff).real
        else:
            raise ValueError("side must be alice or bob")
        return float(self.q*self.eta_a*self.eta_b*(pair+self.q*extra))


def source_parameters(r):
    if not 0 <= r.lower <= r.upper <= 1:
        raise ValueError("monotone preparation coordinate domain not covered")

    def delta(x):
        return (x*x-1)/(1+x*x)

    def chi(x):
        return 2*x/(1+x*x)

    return Interval(delta(r.lower), delta(r.upper)), Interval(chi(r.lower), chi(r.upper))


def response_interval(box, side, pi):
    delta, chi = source_parameters(box["r"])
    if side == "alice":
        angle, partner0, partner1, polynomial = box["a1_deg"], box["b0_deg"], box["b1_deg"], generated_responses()[0]
    elif side == "bob":
        angle, partner0, partner1, polynomial = box["b1_deg"], box["a0_deg"], box["a1_deg"], generated_responses()[1]
    else:
        raise ValueError("side must be alice or bob")
    s, c = trig_degrees(angle, pi)
    s0, c0 = trig_degrees(partner0, pi)
    s1, c1 = trig_degrees(partner1, pi)
    env = {"delta": delta, "chi": chi, "xi": box["xi"], "zeta": box["zeta"],
           "q": box["q"], "s": s, "c": c, "dc": c0-c1, "ds": s0-s1}
    normalized = polynomial.evaluate_combined(env)
    physical = box["q"]*box["eta_A"]*box["eta_B"]*normalized
    ratio = (1+box["q"]*delta**2)*s*(c0-c1)/(chi*c*(s0-s1))
    return {"normalized": normalized, "physical": physical, "required_xi_over_zeta": ratio}


def path_improvement(box, update, displacement, pi):
    along = dict(box)
    if update in ("alice_only", "paired"):
        along["a1_deg"] = box["a1_deg"].shifted_path(-displacement)
    if update in ("bob_only", "paired"):
        along["b1_deg"] = box["b1_deg"].shifted_path(displacement)
    slope = Interval(0)
    if update in ("alice_only", "paired"):
        slope -= response_interval(along, "alice", pi)["physical"]
    if update in ("bob_only", "paired"):
        slope += response_interval(along, "bob", pi)["physical"]
    improvement = Interval(displacement)*pi/180*slope
    return {"path_slope_per_radian": slope.json(), "improvement": improvement.json(),
            "strict_improvement_certified": improvement.lower > 0}


def read_inputs(config):
    instrument = json.loads((ROOT/config["target_instrument"]).read_text())
    amplitudes = instrument["preparation"]["amplitudes"]
    h, v = F(amplitudes["HH"]), F(amplitudes["VV"])
    width = F(config["rounding"]["amplitude_half_width"])
    if h-width <= 0 or v-width <= 0:
        raise ValueError("amplitude rounding leaves the positive coordinate chart")
    box = {"r": Interval((v-width)/(h+width), (v+width)/(h-width)),
           "q": Interval(*config["channel"]["pair_probability"])}
    angle_width = F(config["rounding"]["angle_half_width_deg"])
    angles = instrument["controls"]["alice"]+instrument["controls"]["bob"]
    for name, value in zip(("a0_deg", "a1_deg", "b0_deg", "b1_deg"), angles):
        center = F(value)
        box[name] = Interval(center-angle_width, center+angle_width)
    for name in ("eta_A", "eta_B"):
        declared = config["channel"][name]
        center, half_width = F(declared["center"]), F(declared["half_width"])
        if half_width != F(3, 1000):
            raise ValueError("detector efficiency percentage mapping is not ±0.3%")
        box[name] = Interval(center-half_width, center+half_width)
    return instrument, box


def verify_bindings():
    source_path = HERE/"sources.json"
    relative = str(source_path.relative_to(ROOT))
    committed = subprocess.check_output(["git", "show", f"{FROZEN_COMMIT}:{relative}"], cwd=ROOT)
    if committed != source_path.read_bytes():
        raise ValueError("response source packet differs from scientific freeze")
    sources = json.loads(committed)
    bindings = {}
    for binding in sources["inputs"]:
        path = ROOT/binding["path"]
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if digest != binding["sha256"]:
            raise ValueError("source binding changed: "+binding["path"])
        bindings[binding["path"]] = digest
    for path in (CRITERION, source_path, Path(__file__)):
        bindings[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return bindings


def robust_score_interval(box, eta_a, eta_b, background_a, background_b, pi):
    # The equality to the full source contraction is checked symbolically first.
    score_factorization()
    delta, chi = source_parameters(box["r"])
    sa0, ca0 = trig_degrees(box["a0_deg"], pi)
    sa1, ca1 = trig_degrees(box["a1_deg"], pi)
    sb0, cb0 = trig_degrees(box["b0_deg"], pi)
    sb1, cb1 = trig_degrees(box["b1_deg"], pi)
    zz = ca0*(cb0+cb1)+ca1*(cb0-cb1)
    xx = sa0*(sb0+sb1)+sa1*(sb0-sb1)
    # Every nonnegative placement has mA,mB in [zeta,1], with product zeta.
    # This larger square encloses the exact fiber; joint terms keep the product.
    ma = mb = Interval(box["zeta"].lower, 1)
    ea, eb, ba, bb = F(eta_a), F(eta_b), F(background_a), F(background_b)
    linear = (Interval((ea*eb-ea-eb)/2) +
              delta*ma*ca0*ea*(eb-1+2*bb)/2 +
              delta*mb*cb0*eb*(ea-1+2*ba)/2 +
              ea*eb*(box["zeta"]*zz+box["xi"]*chi*xx)/4+ea*bb+eb*ba)
    quadratic = ea*eb*(2+2*delta*(ma*ca0+mb*cb0)+delta**2*box["zeta"]*zz)/4
    return box["q"]*linear+box["q"]**2*quadratic+2*ba*bb-ba-bb


def positive_branch(box, config, pi):
    ba, bb = (F(config["channel"][key]) for key in ("background_A_per_trial", "background_B_per_trial"))
    corners = []
    for ea, eb in itertools.product((box["eta_A"].lower, box["eta_A"].upper),
                                    (box["eta_B"].lower, box["eta_B"].upper)):
        interval = robust_score_interval(box, ea, eb, ba, bb, pi)
        corners.append({"eta_A": str(ea), "eta_B": str(eb), "CH": interval.json()})
    lower = min(F(item["CH"]["exact_lower"]) for item in corners)
    upper = max(F(item["CH"]["exact_upper"]) for item in corners)
    result = Interval(lower, upper)
    return {"restriction": config["robust_positive_branch"]["restriction"],
            "claim_is_conditional": True,
            "method": "symbolically generated CH is bilinear in eta_A,eta_B; all four corner enclosures cover the efficiency rectangle",
            "corners": corners, "CH": result.json(), "positive_certified": result.lower > 0}


def point_environment(r, retention, angles, side, q):
    if side == "alice":
        angle, p0, p1 = angles[1], angles[2], angles[3]
    elif side == "bob":
        angle, p0, p1 = angles[3], angles[0], angles[1]
    else:
        raise ValueError("unknown side")
    trig = lambda x: (math.sin(2*math.radians(x)), math.cos(2*math.radians(x)))
    s, c = trig(angle)
    s0, c0 = trig(p0)
    s1, c1 = trig(p1)
    return {"delta": (r*r-1)/(1+r*r), "chi": 2*r/(1+r*r), "q": q,
            "ax": retention[0], "az": retention[1], "bx": retention[2], "bz": retention[3],
            "s": s, "c": c, "dc": c0-c1, "ds": s0-s1}


def matrix_controls(config, instrument):
    control = config["matrix_controls"]
    xi, zeta = float(F(control["xi"])), float(F(control["zeta"]))
    placements = {"left": (xi, zeta, 1, 1), "right": (1, 1, xi, zeta),
                  "balanced": (math.sqrt(xi), math.sqrt(zeta), math.sqrt(xi), math.sqrt(zeta)),
                  "both-flipped-z": (math.sqrt(xi), -math.sqrt(zeta), math.sqrt(xi), -math.sqrt(zeta))}
    if set(placements) != set(control["placements"]):
        raise ValueError("matrix-control placements changed")
    ea, eb = (float(F(config["channel"][name]["center"])) for name in ("eta_A", "eta_B"))
    q = sum(map(F, config["channel"]["pair_probability"]))/2
    ba, bb = (float(F(config["channel"][name])) for name in ("background_A_per_trial", "background_B_per_trial"))
    angles = list(map(float, instrument["controls"]["alice"]+instrument["controls"]["bob"]))
    h = float(F(control["finite_difference_step_radians"]))
    tolerance = float(F(control["derivative_absolute_tolerance"]))
    probability_tolerance = float(F(control["probability_tolerance"]))
    results, max_rhos, nonmax_singles = [], [], {}
    worst_fd, worst_polynomial, worst_norm, lowest_eigenvalue = 0., 0., 0., 1.
    for r_string in control["r"]:
        r = float(F(r_string))
        for placement in control["placements"]:
            retention = placements[placement]
            model = MatrixModel(r, *retention, ea, eb, float(q), ba, bb)
            worst_norm = max(worst_norm, abs(float(model.np.trace(model.rho).real)-1))
            lowest_eigenvalue = min(lowest_eigenvalue, float(model.np.linalg.eigvalsh(model.rho).min()))
            if r == 1:
                max_rhos.append(model.rho)
            joint, pa0, pb0 = model.probabilities(angles[0], angles[2])
            if r != 1:
                nonmax_singles[placement] = {"alice_unprimed": pa0, "bob_unprimed": pb0}
            derivatives = {}
            for side, index in (("alice", 1), ("bob", 3)):
                matrix = model.primed_derivative(angles, side)
                minus, plus = list(angles), list(angles)
                minus[index] -= math.degrees(h)
                plus[index] += math.degrees(h)
                finite_difference = (model.score(plus)-model.score(minus))/(2*h)
                generated = float(q)*ea*eb*generated_responses()[0 if side == "alice" else 1].evaluate_scalar(
                    point_environment(r, retention, angles, side, float(q)))
                error, generated_error = abs(matrix-finite_difference), abs(matrix-generated)
                worst_fd = max(worst_fd, error)
                worst_polynomial = max(worst_polynomial, generated_error)
                derivatives[side] = {"matrix": matrix, "finite_difference": finite_difference,
                                     "generated_polynomial": generated, "finite_difference_absolute_error": error,
                                     "generated_absolute_error": generated_error, "passed": error <= tolerance and generated_error <= tolerance}
            results.append({"r": r_string, "placement": placement,
                            "retention": dict(zip(("ax", "az", "bx", "bz"), retention)),
                            "probabilities": {"joint_unprimed": joint, "alice_unprimed": pa0, "bob_unprimed": pb0},
                            "CH": model.score(angles), "derivatives": derivatives})
    max_preparation_error = max(float(abs(rho-max_rhos[0]).max()) for rho in max_rhos)
    nonmax_difference = max(abs(nonmax_singles[a][side]-nonmax_singles[b][side])
                            for a, b in itertools.combinations(nonmax_singles, 2)
                            for side in ("alice_unprimed", "bob_unprimed"))
    passed = (worst_fd <= tolerance and worst_polynomial <= tolerance and
              max_preparation_error <= probability_tolerance and worst_norm <= probability_tolerance and
              lowest_eigenvalue >= -probability_tolerance and nonmax_difference > probability_tolerance)
    return {"passed": passed, "results": results, "worst_finite_difference_error": worst_fd,
            "worst_generated_derivative_error": worst_polynomial, "worst_source_norm_error": worst_norm,
            "minimum_density_eigenvalue": lowest_eigenvalue,
            "maximum_preparation_full_matrix_agreement_error": max_preparation_error,
            "nonmaximum_preparation_margin_difference": nonmax_difference,
            "lookalike_scope": "both-flipped-z preserves the maximum-preparation calibration but reverses local Z orientation; it is not identified as the experimental channel"}


def case_result(name, limits, base_box, config, pi):
    box = dict(base_box)
    box.update({key: Interval(*limits[key]) for key in ("xi", "zeta")})
    responses = {side: response_interval(box, side, pi) for side in ("alice", "bob")}
    allowed = box["xi"]/box["zeta"]
    derivatives = {}
    for side, response in responses.items():
        expected_sign = response["physical"].upper < 0 if side == "alice" else response["physical"].lower > 0
        derivatives[side] = {key: value.json() for key, value in response.items()}
        derivatives[side]["sign"] = "negative" if response["physical"].upper < 0 else "positive" if response["physical"].lower > 0 else "unresolved"
        derivatives[side]["stationarity_excluded"] = expected_sign
        derivatives[side]["necessary_ratio_disjoint_from_allowed"] = (
            response["required_xi_over_zeta"].upper < allowed.lower or
            response["required_xi_over_zeta"].lower > allowed.upper)
    updates = {}
    for update, displacement in config["fixed_updates_deg"].items():
        a, b = F(displacement["a1"]), F(displacement["b1"])
        if (a, b) != {"alice_only": (F(-1, 10), F(0)), "bob_only": (F(0), F(1, 10)), "paired": (F(-1, 10), F(1, 10))}[update]:
            raise ValueError("fixed response update changed")
        updates[update] = path_improvement(box, update, F(1, 10), pi)
    positive = positive_branch(box, config, pi)
    return {"case": name, "continuous_domain": {key: value.json() for key, value in box.items()},
            "allowed_xi_over_zeta": allowed.json(), "responses": derivatives,
            "fixed_updates": updates, "orientation_preserving_positive_branch": positive,
            "verdict": "CERTIFIED" if (all(item["stationarity_excluded"] for item in derivatives.values()) and
                                               all(item["strict_improvement_certified"] for item in updates.values()) and positive["positive_certified"]) else "NOT_CERTIFIED"}


def center_controls(case, config, instrument):
    domain = case["continuous_domain"]
    xi = sum(F(domain["xi"][key]) for key in ("exact_lower", "exact_upper"))/2
    zeta = sum(F(domain["zeta"][key]) for key in ("exact_lower", "exact_upper"))/2
    amplitude = instrument["preparation"]["amplitudes"]
    r = float(F(amplitude["VV"])/F(amplitude["HH"]))
    ea, eb = (float(F(config["channel"][name]["center"])) for name in ("eta_A", "eta_B"))
    q = float(sum(map(F, config["channel"]["pair_probability"]))/2)
    ba, bb = (float(F(config["channel"][key])) for key in ("background_A_per_trial", "background_B_per_trial"))
    retention = (math.sqrt(float(xi)), math.sqrt(float(zeta)), math.sqrt(float(xi)), math.sqrt(float(zeta)))
    model = MatrixModel(r, *retention, ea, eb, q, ba, bb)
    angles = list(map(float, instrument["controls"]["alice"]+instrument["controls"]["bob"]))
    result = {"preparation_r": r, "xi": float(xi), "zeta": float(zeta), "q": q,
              "placement": "balanced", "responses": {}, "fixed_update_improvements": {}, "CH": model.score(angles)}
    for side in ("alice", "bob"):
        env = point_environment(r, retention, angles, side, q)
        required_ratio = (1+q*env["delta"]**2)*env["s"]*env["dc"]/(env["chi"]*env["c"]*env["ds"])
        result["responses"][side] = {"physical": model.primed_derivative(angles, side), "required_xi_over_zeta": required_ratio}
    for name, step in config["fixed_updates_deg"].items():
        updated = list(angles)
        updated[1] += float(F(step["a1"]))
        updated[3] += float(F(step["b1"]))
        result["fixed_update_improvements"][name] = model.score(updated)-result["CH"]
    def contains(interval, value):
        return float(F(interval["exact_lower"])) <= value <= float(F(interval["exact_upper"]))
    result["inside_own_enclosures"] = (
        all(contains(case["responses"][side][key], value)
            for side, response in result["responses"].items() for key, value in response.items()) and
        all(contains(case["fixed_updates"][name]["improvement"], value)
            for name, value in result["fixed_update_improvements"].items()) and
        contains(case["orientation_preserving_positive_branch"]["CH"], result["CH"]))
    return result


def computation_ast_digest():
    tree = ast.parse(Path(__file__).read_text())
    nodes = [node for node in tree.body if isinstance(node, (ast.FunctionDef, ast.ClassDef))
             and node.name in COMPUTATION_NAMES]
    if {node.name for node in nodes} != COMPUTATION_NAMES:
        raise ValueError("independent scientific definitions are missing")
    selected = ast.Module(body=nodes, type_ignores=[])
    return hashlib.sha256(ast.dump(selected, include_attributes=False).encode()).hexdigest()


def append_comparison():
    """Post hoc comparison; never invokes either complete interval computation."""
    if computation_ast_digest() != COMPUTATION_AST_SHA256:
        raise ValueError("independent calculation changed after its interval execution")
    config = load_frozen()
    own = json.loads(OUTPUT.read_text())
    main_path = HERE/config["outputs"]["primary"]
    main_bytes = main_path.read_bytes()
    primary = json.loads(main_bytes)
    primary_hash = hashlib.sha256(main_bytes).hexdigest()
    own_relative, main_relative = str(Path(__file__).relative_to(ROOT)), str(main_path.relative_to(ROOT))
    for path, expected in own["bindings"].items():
        if path not in (own_relative, main_relative) and hashlib.sha256((ROOT/path).read_bytes()).hexdigest() != expected:
            raise ValueError("independent calculation source changed: "+path)
    for path, expected in primary["bindings"].items():
        if hashlib.sha256((ROOT/path).read_bytes()).hexdigest() != expected:
            raise ValueError("primary receipt source changed: "+path)
    shared = set(own["bindings"]) & set(primary["bindings"])
    source_agreement = all(own["bindings"][path] == primary["bindings"][path] for path in shared)
    freeze_agreement = (own["criterion_freeze"]["commit"] == primary["criterion_freeze"]["commit"] == FROZEN_COMMIT and
                        own["criterion_freeze"]["sha256"] == primary["criterion_freeze"]["criterion_sha256"] == FROZEN_SHA256 and
                        own["criterion_version"] == primary["criterion_version"] == config["criterion_version"])
    spec = importlib.util.spec_from_file_location("posthoc_primary_response", HERE/"response.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    instrument, _ = read_inputs(config)
    primary_cases = {case["case"]: case for case in primary["cases"]}
    compared = []
    probability_tolerance = float(F(config["matrix_controls"]["probability_tolerance"]))
    derivative_tolerance = float(F(config["matrix_controls"]["derivative_absolute_tolerance"]))

    def contains(interval, value):
        value = F(value)
        return F(interval["exact_lower"]) <= value and ("exact_upper" not in interval or value <= F(interval["exact_upper"]))

    for case in own["cases"]:
        main = primary_cases[case["case"]]
        key_map = {name: name.removesuffix("_deg") for name in case["continuous_domain"]}
        inputs_match = all(
            F(own_interval[edge]) == F(main["box"][key_map[name]][edge])
            for name, own_interval in case["continuous_domain"].items()
            for edge in ("exact_lower", "exact_upper"))
        center = center_controls(case, config, instrument)
        q = center["q"]
        ea, eb = (float(F(config["channel"][name]["center"])) for name in ("eta_A", "eta_B"))
        ba, bb = (float(F(config["channel"][name])) for name in ("background_A_per_trial", "background_B_per_trial"))
        retention = (math.sqrt(center["xi"]), math.sqrt(center["zeta"]), math.sqrt(center["xi"]), math.sqrt(center["zeta"]))
        model = MatrixModel(center["preparation_r"], *retention, ea, eb, q, ba, bb)
        angles = list(map(float, instrument["controls"]["alice"]+instrument["controls"]["bob"]))
        parameters = {"r": center["preparation_r"], "mA": retention[1], "mB": retention[3],
                      "xi": center["xi"], "zeta": center["zeta"]}
        probability_error = 0.
        for a, b in itertools.product(angles[:2], angles[2:]):
            axes = (math.sin(2*math.radians(a)), math.cos(2*math.radians(a)),
                    math.sin(2*math.radians(b)), math.cos(2*math.radians(b)))
            error = max(abs(x-y) for x, y in zip(model.probabilities(a, b), module.source_probabilities(parameters, axes)))
            probability_error = max(probability_error, error)
        responses = {}
        for side, value in center["responses"].items():
            physical, ratio = value["physical"], value["required_xi_over_zeta"]
            normalized = physical/(q*ea*eb)
            responses[side] = {
                "matrix_physical_derivative_per_radian": physical,
                "primary_normalized_center": 2*normalized, "independent_normalized_center": normalized,
                "physical_center_inside_both": contains(case["responses"][side]["physical"], physical) and contains(main["responses"][side]["physical"], physical),
                "normalized_center_inside_both_after_scaling": contains(case["responses"][side]["normalized"], normalized) and contains(main["responses"][side]["normalized"], 2*normalized),
                "necessary_ratio_center_inside_both": contains(case["responses"][side]["required_xi_over_zeta"], ratio) and contains(main["responses"][side]["required_xi_over_zeta"], ratio),
                "signs_agree": case["responses"][side]["sign"] == main["responses"][side]["sign"],
                "stationarity_exclusions_agree": case["responses"][side]["stationarity_excluded"] == main["responses"][side]["stationarity_excluded"]}
        updates = {}
        for name, improvement in center["fixed_update_improvements"].items():
            updates[name] = {"matrix_center_improvement": improvement,
                             "center_above_both_certified_lower_bounds": contains(case["fixed_updates"][name]["improvement"], improvement) and contains(main["fixed_updates"][name]["improvement"], improvement),
                             "strict_improvement_agrees": case["fixed_updates"][name]["strict_improvement_certified"] == main["fixed_updates"][name]["certified_improvement"]}
        ch_inside = contains(case["orientation_preserving_positive_branch"]["CH"], center["CH"]) and contains(main["orientation_preserving_positive_branch"]["CH"], center["CH"])
        cached_center_error = max(abs(center["responses"][side]["physical"]-case["center_controls"]["responses"][side]["physical"]) for side in responses)
        passed = (inputs_match and probability_error <= probability_tolerance and cached_center_error <= derivative_tolerance and ch_inside and
                  all(all(row[key] for key in ("physical_center_inside_both", "normalized_center_inside_both_after_scaling", "necessary_ratio_center_inside_both", "signs_agree", "stationarity_exclusions_agree")) for row in responses.values()) and
                  all(row["center_above_both_certified_lower_bounds"] and row["strict_improvement_agrees"] for row in updates.values()))
        compared.append({"case": case["case"], "input_boxes_match": inputs_match, "responses": responses,
                         "fixed_updates": updates, "matrix_center_CH": center["CH"], "CH_center_inside_both": ch_inside,
                         "primary_positive_branch_certified": main["orientation_preserving_positive_branch"]["certified_positive"],
                         "independent_positive_branch_certified": case["orientation_preserving_positive_branch"]["positive_certified"],
                         "worst_probability_contraction_difference": probability_error,
                         "cached_matrix_center_derivative_error": cached_center_error, "passed": passed})
    # Bind the completed comparison snapshot, not inputs or seeds for computation.
    if hashlib.sha256(main_path.read_bytes()).hexdigest() != primary_hash:
        raise ValueError("primary artifact changed during comparison; retry comparison only")
    own.setdefault("calculation_implementation", {"program_source_sha256": own["bindings"][own_relative],
                                                  "scientific_ast_sha256": COMPUTATION_AST_SHA256,
                                                  "primary_artifact_used_as_input": False})
    own["bindings"][own_relative] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    own["bindings"][main_relative] = primary_hash
    own["comparison"] = {"phase": "post hoc comparison after independent interval computation; no interval recomputation or input/seed exchange",
                         "primary_artifact_sha256": primary_hash, "primary_bindings": primary["bindings"],
                         "source_bindings_agree": source_agreement, "freeze_agrees": freeze_agreement,
                         "normalization": {"independent": "dS/(q eta_A eta_B)", "primary": "2 dS/(q eta_A eta_B)",
                                           "primary_to_independent": "divide by 2", "derivative_angle_unit": "radian", "control_angle_unit": "degree"},
                         "cases": compared, "passed": source_agreement and freeze_agreement and all(row["passed"] for row in compared)}
    OUTPUT.write_text(json.dumps(own, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps({"comparison_passed": own["comparison"]["passed"], "cases": [{"case": row["case"], "passed": row["passed"]} for row in compared]}))
    return own["comparison"]["passed"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare-only", action="store_true")
    args = parser.parse_args()
    if args.compare_only:
        return 0 if append_comparison() else 1
    config = load_frozen()
    bindings = verify_bindings()
    if config["interval"]["independent_trig_terms"] != 14:
        raise ValueError("independent Taylor degree does not match the frozen criterion")
    instrument, base_box = read_inputs(config)
    pi = Interval(*config["interval"]["pi"])
    results = []
    for name, limits in config["cases"].items():
        result = case_result(name, limits, base_box, config, pi)
        result["center_controls"] = center_controls(result, config, instrument)
        results.append(result)
        print(name, result["verdict"], {side: item["sign"] for side, item in result["responses"].items()},
              "CH lower", result["orientation_preserving_positive_branch"]["CH"]["lower"], flush=True)
    controls = matrix_controls(config, instrument)
    payload = {"schema": "nist-response-independent/v1", "criterion_version": config["criterion_version"],
               "criterion_freeze": criterion_freeze(), "source_mapping_identified": False,
               "production_admitted": False, "scope": config["scope"], "bindings": bindings,
               "arithmetic": {"internal": "exact fractions", "trig": "14-term endpoint Taylor polynomials with derivative-bounded Lagrange remainders and monotonicity",
                              "pi": pi.json(), "interval_display": "18-place outward-rounded exact rational decimal endpoints; exact_lower/exact_upper retain authoritative rational endpoints",
                              "subdivision_leaves": 1},
               "symbolic_source_certificate": {"method": "pure density matrix, independent local Pauli conjugations, partial traces, projector contractions",
                                               "normalized_primed_derivatives": {side: polynomial.json() for side, polynomial in zip(("alice", "bob"), generated_responses())},
                                               "full_CH_bilinear_in_efficiencies": True,
                                               "full_CH_factorization_verified": not (generated_score()-(Polynomial.variable("q")*score_factorization()[0]+Polynomial.variable("q")*Polynomial.variable("q")*score_factorization()[1]+score_factorization()[2])).coefficients},
               "cases": results, "matrix_controls": controls,
               "verdict": "CERTIFIED" if all(result["verdict"] == "CERTIFIED" and result["center_controls"]["inside_own_enclosures"] for result in results) and controls["passed"] else "NOT_CERTIFIED"}
    OUTPUT.write_text(json.dumps(payload, indent=2, ensure_ascii=False)+"\n")
    print("matrix controls", controls["passed"], "FD error", controls["worst_finite_difference_error"], flush=True)
    print(payload["verdict"], flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
