"""Observable quotient, complete regular fibers, and projections of the frozen confidence set."""
from fractions import Fraction
import itertools
import math

from likelihood import Directed
from model import Effect, Instrument, decode, encode, source_joint


def quotient(point):
    return {"alice_bias": [str(e.mu) for e in point.alice],
            "bob_bias": [str(e.mu) for e in point.bob],
            "X": [[str(a.u * b.u) for b in point.bob] for a in point.alice],
            "Z": [[str(a.z * b.z) for b in point.bob] for a in point.alice]}


def recover_quotient(table):
    if set(table) != set(itertools.product((0, 1), repeat=5)):
        raise ValueError("Complete generated joint law required")
    mu_a = [2 * sum(table[0, a, 0, 0, y] for y in (0, 1)) - 1 for a in (0, 1)]
    mu_b = [2 * sum(table[0, 0, b, x, 0] for x in (0, 1)) - 1 for b in (0, 1)]
    def correlation(h, a, b):
        return sum((1 - 2 * x) * (1 - 2 * y) * table[h, a, b, x, y]
                   for x, y in itertools.product((0, 1), repeat=2))
    return {"alice_bias": list(map(str, mu_a)), "bob_bias": list(map(str, mu_b)),
            "X": [[str((correlation(1, a, b) - correlation(0, a, b)) / 2) for b in (0, 1)] for a in (0, 1)],
            "Z": [[str(mu_a[a] * mu_b[b] - (correlation(0, a, b) + correlation(1, a, b)) / 2)
                   for b in (0, 1)] for a in (0, 1)]}


def scale(point, s, t):
    s, t = Fraction(s), Fraction(t)
    if s == 0 or t == 0:
        raise ValueError("Two nonzero source scales required")
    return Instrument(tuple(Effect(e.mu, s * e.u, t * e.z) for e in point.alice),
                      tuple(Effect(e.mu, e.u / s, e.z / t) for e in point.bob))


def recover_scales(point, other):
    if point.alice[0].u * point.bob[0].u == 0 or point.alice[0].z * point.bob[0].z == 0:
        raise ValueError("Regular nonzero X/Z anchor required")
    if quotient(point) != quotient(other):
        raise ValueError("Observable quotient changed")
    s, t = other.alice[0].u / point.alice[0].u, other.alice[0].z / point.alice[0].z
    if scale(point, s, t) != other:
        raise ValueError("Regular fiber reconstruction failed")
    return s, t


def positive_rectangle(point, low=Fraction(19, 20), high=Fraction(21, 20)):
    if not 0 < low < high:
        raise ValueError("Positive nontrivial scale interval required")
    # Monotonicity of the four nonnegative quadratic terms covers every interior point.
    constraints = []
    for side in ("alice", "bob"):
        for setting, e in enumerate(getattr(point, side)):
            cap2 = (1 - abs(e.mu)) ** 2
            largest_norm2 = ((e.u ** 2 + e.z ** 2) * high ** 2 if side == "alice" else
                             (e.u ** 2 + e.z ** 2) / low ** 2)
            if largest_norm2 > cap2:
                raise ValueError("Scale rectangle leaves the complete readout cone")
            constraints.append({"side": side, "setting": setting, "maximum_norm_squared": str(largest_norm2),
                                "capacity_squared": str(cap2), "slack": str(cap2 - largest_norm2)})
    return {"s": [str(low), str(high)], "t": [str(low), str(high)], "constraints": constraints,
            "entire_continuous_rectangle_legal": True, "finite_samples_used_as_coverage": False}


def fixed_law_fiber(point):
    if point.alice[0].u * point.bob[0].u == 0 or point.alice[0].z * point.bob[0].z == 0:
        raise ValueError("Regular law required for the complete two-scale fiber")
    constraints = []
    for side in ("alice", "bob"):
        for setting, e in enumerate(getattr(point, side)):
            constraints.append({"side": side, "setting": setting, "u_squared": str(e.u ** 2),
                                "z_squared": str(e.z ** 2), "capacity_squared": str((1 - abs(e.mu)) ** 2),
                                "kind": "u2*S+z2*T<=capacity2" if side == "alice" else
                                        "u2/S+z2/T<=capacity2"})
    return {"regular_anchor": "X00_and_Z00_nonzero", "constraints": constraints,
            "squared_coordinates": {"S": "s^2>0", "T": "t^2>0"},
            "sign_branches": [[s, t] for s, t in itertools.product((-1, 1), repeat=2)],
            "continuous_fiber": "all_nonzero_s_t_satisfying_all_four_source_cones",
            "isotropic_subfamily_preserves_all_axes": True,
            "fixed_generated_law_is_actual_empirical_probability": False}


def own_counts(rows):
    if len(rows) != 8:
        raise ValueError("Complete eight-context counts required")
    result = {side: [[0, 0], [0, 0]] for side in ("alice", "bob")}
    seen = set()
    for row in rows:
        key = tuple(row[k] for k in ("h", "a", "b"))
        if key in seen or any(type(v) is not int or v not in (0, 1) for v in key):
            raise ValueError("Unique binary contexts required")
        seen.add(key)
        numbers = row["counts"]
        if len(numbers) != 4 or any(type(n) is not int or n < 0 for n in numbers):
            raise ValueError("Four natural counts required")
        for event, n in enumerate(numbers):
            x, y = divmod(event, 2)
            result["alice"][key[1]][x] += n
            result["bob"][key[2]][y] += n
    return result


class Profile:
    """A necessary marginal projection of E<40, using its existing 1/6 component."""
    def __init__(self, counts, setting, precision=80):
        if len(counts) != 2 or setting not in (0, 1):
            raise ValueError("Two own settings required")
        self.counts, self.setting = counts, setting
        self.arithmetic = Directed(precision)
        zero = self.arithmetic.logarithm(Fraction(1))
        self.fact = {}
        def factorial(n):
            if n not in self.fact:
                self.fact[n] = self.arithmetic.logarithm(Fraction(math.factorial(n)))
            return self.fact[n]
        pooled = [sum(row[x] for row in counts) for x in (0, 1)]
        numerator = zero
        for n in pooled:
            term = self.arithmetic.subtract(factorial(2 * n), factorial(n))
            term = self.arithmetic.subtract(term, self.arithmetic.scale(self.arithmetic.logarithm(Fraction(2)), 2 * n))
            numerator = self.arithmetic.add(numerator, term)
        numerator = self.arithmetic.subtract(numerator, factorial(sum(pooled)))
        other = counts[1 - setting]
        likelihood = zero
        for n in other:
            if n:
                likelihood = self.arithmetic.add(likelihood, self.arithmetic.scale(
                    self.arithmetic.logarithm(Fraction(n, sum(other))), n))
        self.constant = self.arithmetic.subtract(numerator, likelihood)
        self.threshold = self.arithmetic.logarithm(Fraction(240))
        n0, n1 = counts[setting]
        if not n0 or not n1:
            raise ValueError("This two-endpoint projection requires both observed outcomes")
        self.mle = Fraction(n0, n0 + n1)

    def at(self, p):
        p = Fraction(p)
        if not 0 < p < 1:
            raise ValueError("Interior source marginal required")
        n0, n1 = self.counts[self.setting]
        log_likelihood = self.arithmetic.add(self.arithmetic.scale(self.arithmetic.logarithm(p), n0),
                                            self.arithmetic.scale(self.arithmetic.logarithm(1 - p), n1))
        return self.arithmetic.subtract(self.constant, log_likelihood)

    def bounds(self):
        center = self.at(self.mle)
        if center.upper >= self.threshold.lower:
            raise ValueError("Marginal MLE failed the necessary component test")
        epsilon = None
        for bits in (80, 160, 320, 640, 1280):
            proposal = Fraction(1, 1 << bits)
            if self.at(proposal).lower >= self.threshold.upper and self.at(1 - proposal).lower >= self.threshold.upper:
                epsilon = proposal
                break
        if epsilon is None:
            raise ValueError("No certified outside endpoints found")
        left, middle = epsilon, self.mle
        for _ in range(36):
            midpoint = (left + middle) / 2
            if self.at(midpoint).lower >= self.threshold.upper:
                left = midpoint
            else:
                middle = midpoint
        middle, right = self.mle, 1 - epsilon
        for _ in range(36):
            midpoint = (middle + right) / 2
            if self.at(midpoint).lower >= self.threshold.upper:
                right = midpoint
            else:
                middle = midpoint
        lo, hi = self.at(left), self.at(right)
        if not (left < self.mle < right and lo.lower >= self.threshold.upper and hi.lower >= self.threshold.upper):
            raise ValueError("Marginal envelope not certified")
        return {"setting": self.setting, "counts": self.counts, "p_mle": str(self.mle),
                "p_outer_interval": [str(left), str(right)], "mu_outer_interval": [str(2 * left - 1), str(2 * right - 1)],
                "lower_endpoint_log_e": lo.encode(), "upper_endpoint_log_e": hi.encode(),
                "mle_log_e": center.encode(), "component_threshold": "240",
                "source": "same_parent_all_prefix_E_with_component_weight_1/6",
                "kind": "necessary_outer_projection_of_entire_parent_confidence_set",
                "new_confidence_budget_spent": False, "point_witness_used_as_confidence_bound": False}
