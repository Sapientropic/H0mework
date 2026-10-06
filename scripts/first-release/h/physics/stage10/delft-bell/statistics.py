"""Predeclared, outcome-sequential goodness-of-fit for the Delft joint model.

The null is conditional on the past and the current (herald, a, b): its four
outcome probabilities lie in the locked per-cell radius of the fixed table.
Settings and herald rates are not predicted. Their final counts are not used
as conditioning events, and arbitrary memory is allowed inside that null.

Each component predicts r before the outcome, then multiplies r[o]/u[o], where
u[o] = min(1, q[o] + radius). Since p[o] <= u[o], its conditional expected
multiplier is at most sum(r) = 1. We mix component PRODUCTS with fixed weights;
Ville's bound gives min(1, 1/max_t E_t). The radius envelope is conservative:
its four upper bounds need not sum to one. A radius is a conditional sensitivity
assumption, not a confidence region inferred from published error bars.
"""

from __future__ import annotations

import math
from collections.abc import Iterable, Mapping, Sequence


ANGLE_CORRECTION = 0.026 * math.pi
VISIBILITY_GRID = (0.0, 0.25, 0.5, 0.75, 0.9, 1.0)
RADIUS_GRID = (0.0, 0.01, 0.02, 0.05, 0.1, 0.2)
OUTCOMES = ((1, 1), (1, -1), (-1, 1), (-1, -1))
CONTEXTS = tuple((h, a, b) for h in (-1, 1) for a in (0, 1) for b in (0, 1))
COMPONENT_NAMES = tuple(f"visibility_{v:g}" for v in VISIBILITY_GRID) + ("kt_prior_only",)
COMPONENT_WEIGHTS = (1.0 / len(COMPONENT_NAMES),) * len(COMPONENT_NAMES)

Context = tuple[int, int, int]
Probabilities = tuple[float, float, float, float]


def _context(herald: int, a: int, b: int) -> Context:
    if type(herald) is not int or herald not in (-1, 1):
        raise ValueError("herald must be -1 (psi-) or +1 (psi+)")
    if any(type(value) is not int or value not in (0, 1) for value in (a, b)):
        raise ValueError("a and b must be integer bits")
    return herald, a, b


def predict_joint(herald: int, a: int, b: int) -> Probabilities:
    """Ideal Bell source at the published Delft angles; raw +1 means a click.

    The 2015 paper specifies the 0.026*pi correction. The 2016 paper states
    that settings other than its enumerated changes are inherited. Its example
    analysis prints nominal angle labels but does not compute from them.
    """
    _context(herald, a, b)
    alpha = (0.0, math.pi / 2)[a]
    beta = (-3 * math.pi / 4 - ANGLE_CORRECTION,
            3 * math.pi / 4 + ANGLE_CORRECTION)[b]
    correlation = -math.cos(alpha - beta if herald == -1 else alpha + beta)
    return tuple((1 + x * y * correlation) / 4 for x, y in OUTCOMES)


def _probabilities(values: Sequence[float]) -> Probabilities:
    if len(values) != 4:
        raise ValueError("each fixed prediction must contain four probabilities")
    result = tuple(float(value) for value in values)
    if any(not math.isfinite(value) or not 0 <= value <= 1 for value in result):
        raise ValueError("probabilities must be finite and in [0, 1]")
    if not math.isclose(math.fsum(result), 1.0, rel_tol=0, abs_tol=1e-12):
        raise ValueError("each fixed prediction must sum to one")
    return result


def _log_mixture(log_values: Sequence[float]) -> float:
    largest = max(log_values)
    if math.isinf(largest):
        return largest
    return largest + math.log(math.fsum(
        weight * math.exp(value - largest)
        for weight, value in zip(COMPONENT_WEIGHTS, log_values)
    ))


def _json_log(value: float) -> float | str:
    return value if math.isfinite(value) else ("Infinity" if value > 0 else "-Infinity")


def _json_exp(value: float) -> float | str:
    if value == math.inf:
        return "Infinity"
    try:
        return math.exp(value)
    except OverflowError:
        # Preserve the finite logarithm, rather than reporting arithmetic
        # overflow as a mathematically infinite evidence value.
        return f"exp({value!r})"


class BellEProcess:
    """One pass over trials, with a frozen point table and seven alternatives.

    An explicit point table may represent independently specified calibration.
    The table is copied at construction and never estimated from test outcomes.
    The v=1 component is intentionally retained: its point-null product is one,
    and all seven predeclared components have equal weights.
    """

    def __init__(self, predictions: Mapping[Context, Sequence[float]] | None = None,
                 radii: Sequence[float] = RADIUS_GRID):
        if predictions is None:
            self._predictions = {context: predict_joint(*context) for context in CONTEXTS}
            self.prediction_kind = "ideal_source_at_published_delft_angles"
        else:
            if set(predictions) != set(CONTEXTS):
                raise ValueError("the fixed prediction table must cover exactly eight contexts")
            self._predictions = {context: _probabilities(predictions[context])
                                 for context in CONTEXTS}
            self.prediction_kind = "caller_fixed_point_table"
        self.radii = tuple(float(radius) for radius in radii)
        if (not self.radii or len(set(self.radii)) != len(self.radii)
                or any(not math.isfinite(radius) or not 0 <= radius <= 1
                       for radius in self.radii)):
            raise ValueError("radii must be distinct finite values in [0, 1]")
        self._counts = {context: [0, 0, 0, 0] for context in CONTEXTS}
        self._component_logs = [[0.0] * len(COMPONENT_NAMES) for _ in self.radii]
        self._max_logs = [0.0] * len(self.radii)  # Include E_0 = 1.
        self._support_violations = [False] * len(self.radii)
        self.n_trials = 0

    def current_numerators(self, herald: int, a: int, b: int) -> tuple[Probabilities, ...]:
        """Return all seven probability vectors using strictly previous outcomes."""
        context = _context(herald, a, b)
        q = self._predictions[context]
        fixed = tuple(tuple((1 - v) / 4 + v * probability for probability in q)
                      for v in VISIBILITY_GRID)
        counts = self._counts[context]
        denominator = sum(counts) + 2  # Four KT pseudocounts of 1/2.
        kt = tuple((count + 0.5) / denominator for count in counts)
        return fixed + (kt,)

    def update(self, trial: Mapping[str, object]) -> None:
        """Consume one accepted trial. Extra provenance fields are ignored."""
        try:
            context = _context(trial["herald"], trial["a"], trial["b"])
            x, y = trial["x"], trial["y"]
        except KeyError as error:
            raise ValueError(f"missing trial field: {error.args[0]}") from error
        if any(type(value) is not int or value not in (-1, 1) for value in (x, y)):
            raise ValueError("x and y must be integer outcomes -1 or +1")
        outcome = OUTCOMES.index((x, y))
        numerators = self.current_numerators(*context)
        predicted = self._predictions[context][outcome]
        for index, radius in enumerate(self.radii):
            denominator = min(1.0, predicted + radius)
            if denominator == 0:
                # A zero-null-mass event rejects that null regardless of the
                # alternative, including the otherwise ambiguous 0/0 case.
                self._support_violations[index] = True
                self._component_logs[index] = [math.inf] * len(COMPONENT_NAMES)
            elif not self._support_violations[index]:
                for component, numerator in enumerate(numerators):
                    value = numerator[outcome]
                    increment = math.log(value) - math.log(denominator) if value else -math.inf
                    self._component_logs[index][component] += increment
            mixed = _log_mixture(self._component_logs[index])
            self._max_logs[index] = max(self._max_logs[index], mixed)
        # Updating counts last is the statistical separation between a
        # predictable numerator and fitting the very outcome being scored.
        self._counts[context][outcome] += 1
        self.n_trials += 1

    def result(self) -> dict:
        rows = []
        for index, radius in enumerate(self.radii):
            log_e = _log_mixture(self._component_logs[index])
            max_log_e = self._max_logs[index]
            rows.append({
                "radius": radius,
                "scope": ("fixed_point_model" if radius == 0
                          else "conditional_per_cell_radius_sensitivity"),
                "terminal_e": _json_exp(log_e),
                "terminal_log_e": _json_log(log_e),
                "max_log_e": _json_log(max_log_e),
                "anytime_p": math.exp(-max_log_e),
                "support_violation": self._support_violations[index],
            })
        return {
            "prediction_kind": self.prediction_kind,
            "n_trials": self.n_trials,
            "outcome_order": [list(outcome) for outcome in OUTCOMES],
            "components": [{"name": name, "weight": weight}
                           for name, weight in zip(COMPONENT_NAMES, COMPONENT_WEIGHTS)],
            "radii": rows,
            "context_counts": [
                {"herald": h, "a": a, "b": b, "n": sum(self._counts[h, a, b]),
                 "outcome_counts": self._counts[h, a, b].copy()}
                for h, a, b in CONTEXTS
            ],
        }


def process_trials(trials: Iterable[Mapping[str, object]],
                   predictions: Mapping[Context, Sequence[float]] | None = None,
                   radii: Sequence[float] = RADIUS_GRID) -> dict:
    process = BellEProcess(predictions=predictions, radii=radii)
    for trial in trials:
        process.update(trial)
    return process.result()
