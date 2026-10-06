"""Candidate generation for the complete readout domain; no numerical verdict authority."""
import math
from dataclasses import dataclass
from fractions import Fraction
from itertools import product

from model import Effect, Instrument, encode


CONTEXTS = tuple(product(range(2), repeat=3))
COMPONENT_WEIGHTS = (Fraction(1, 6), Fraction(1, 6), Fraction(1, 6), Fraction(1, 2))


def log_beta_predictor(n0, n1):
    return math.lgamma(n0 + .5) + math.lgamma(n1 + .5) - math.lgamma(n0 + n1 + 1) - 2 * math.lgamma(.5)


def log_joint_predictor(counts):
    return sum(math.lgamma(number + .5) - math.lgamma(.5) for number in counts) - math.lgamma(sum(counts) + 2)


@dataclass(frozen=True)
class TerminalCounts:
    rows: tuple

    def __post_init__(self):
        if len(self.rows) != 8:
            raise ValueError("All eight herald/setting contexts required")
        for counts in self.rows:
            if len(counts) != 4 or any(type(number) is not int or number < 0 for number in counts):
                raise ValueError("Complete nonnegative integer four-outcome counts required")


def polar_effects(parameters):
    if len(parameters) != 12:
        raise ValueError("Twelve primitive search coordinates required")
    answer = []
    for offset in range(0, 12, 3):
        mu, radius, angle = parameters[offset:offset + 3]
        if not (-1 <= mu <= 1 and 0 <= radius <= 1 and math.isfinite(angle)):
            raise ValueError("Search point outside the complete compact carrier")
        length = radius * (1 - abs(mu))
        answer.append((mu, length * math.sin(angle), length * math.cos(angle)))
    return tuple(answer)


def float_source_table(effects):
    table = []
    for h, a, b in CONTEXTS:
        first, second = effects[a], effects[2 + b]
        correlation = first[0] * second[0] - (1 - 2 * h) * first[1] * second[1] - first[2] * second[2]
        table.append(tuple((1 + (1 - 2 * x) * first[0] + (1 - 2 * y) * second[0] +
                            (1 - 2 * x) * (1 - 2 * y) * correlation) / 4 for x, y in product(range(2), repeat=2)))
    return tuple(table)


class TerminalObjective:
    def __init__(self, counts):
        self.counts = counts
        self.alice_counts = [sum(row[0] + row[1] for row in counts.rows), sum(row[2] + row[3] for row in counts.rows)]
        self.bob_counts = [sum(row[0] + row[2] for row in counts.rows), sum(row[1] + row[3] for row in counts.rows)]
        self.numerators = (
            sum(log_beta_predictor(row[0], row[3]) + log_beta_predictor(row[1], row[2]) for row in counts.rows),
            log_beta_predictor(*self.alice_counts), log_beta_predictor(*self.bob_counts),
            sum(log_joint_predictor(row) for row in counts.rows),
        )

    def component_logs(self, probabilities):
        if len(probabilities) != 8:
            raise ValueError("Full source table required")
        denominators = [0., 0., 0., 0.]
        for row, q in zip(self.counts.rows, probabilities):
            for index, number in enumerate(row):
                if not number:
                    continue
                if q[index] <= 0:
                    return (math.inf,) * 4
                x, y = divmod(index, 2)
                parity = x ^ y
                mass = q[0] + q[3] if parity == 0 else q[1] + q[2]
                marginal_a = q[2 * x] + q[2 * x + 1]
                marginal_b = q[y] + q[2 + y]
                denominators[0] += number * (math.log(q[index]) - math.log(mass))
                denominators[1] += number * math.log(marginal_a)
                denominators[2] += number * math.log(marginal_b)
                denominators[3] += number * math.log(q[index])
        return tuple(numerator - denominator for numerator, denominator in zip(self.numerators, denominators))

    def __call__(self, parameters):
        components = self.component_logs(float_source_table(polar_effects(parameters)))
        peak = max(components)
        if not math.isfinite(peak):
            return math.inf
        return peak + math.log(sum(float(weight) * math.exp(value - peak)
                                   for weight, value in zip(COMPONENT_WEIGHTS, components)))


def rationalize_effect(effect, precision=40):
    denominator = 1 << precision
    # Toward-zero rounding is deterministic and reduces every absolute primitive coordinate.
    coordinates = [Fraction(math.trunc(value * denominator), denominator) for value in effect]
    mu, u, z = coordinates
    if not -1 <= mu <= 1:
        raise ValueError("Search bias outside the readout domain")
    if abs(mu) == 1:
        return Effect(mu, 0, 0)
    cap_squared = (1 - abs(mu))**2
    shrink = Fraction(denominator - 1, denominator)
    while u * u + z * z > cap_squared:
        u, z = u * shrink, z * shrink
    return Effect(mu, u, z)


def rational_candidate(parameters, precision=40):
    effects = tuple(rationalize_effect(effect, precision) for effect in polar_effects(parameters))
    return Instrument(effects[:2], effects[2:])


def search_terminal(counts, starts, *, max_iterations=1000):
    """Approximate constrained search emits only exact legal primitive candidates."""
    from scipy.optimize import minimize
    objective = TerminalObjective(counts)
    bounds = [bound for _ in range(4) for bound in ((-1., 1.), (0., 1.), (-math.pi, math.pi))]
    candidates = []
    for start in starts:
        result = minimize(objective, start, method="L-BFGS-B", bounds=bounds,
                          options={"maxiter": max_iterations, "ftol": 1e-12})
        if math.isfinite(result.fun):
            witness = rational_candidate(tuple(float(value) for value in result.x))
            candidates.append({"primitive": encode(witness), "approximate_terminal_log_e": float(result.fun),
                               "optimizer_success": bool(result.success), "numerical_verdict_certified": False,
                               "all_prefix_checked": False})
    return tuple(candidates)
