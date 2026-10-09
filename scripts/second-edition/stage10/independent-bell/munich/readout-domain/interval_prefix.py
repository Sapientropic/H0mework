"""The original four likelihood processes over exact probability enclosures.

Rows enclose normalized distributions; they do not certify a Born or CPTP
producer.  A raw-source consumer must establish that its joint law belongs to
the table before interpreting a compatible result as a physical witness.
"""
from decimal import Decimal
from fractions import Fraction
import hashlib
import json

from likelihood import CONTEXTS, ORDER, Directed, Interval, fraction_bytes


INFINITY = Decimal("Infinity")


def exact(value):
    if type(value) not in (int, str, Fraction):
        raise ValueError("exact rational probability endpoint required")
    return Fraction(value)


def _bits(values, length):
    if type(values) is not tuple or len(values) != length or any(
            type(value) is not int or value not in (0, 1) for value in values):
        raise ValueError("canonical binary context or trial required")


def probability_table(table):
    if type(table) is not dict:
        raise ValueError("complete eight-context probability enclosure required")
    for context in table:
        _bits(context, 3)
    if set(table) != set(CONTEXTS):
        raise ValueError("complete eight-context probability enclosure required")
    result = {}
    for context, row in table.items():
        if type(row) not in (tuple, list) or len(row) != 4:
            raise ValueError("four outcome enclosures in 00/01/10/11 order required")
        values = []
        for interval in row:
            if type(interval) not in (tuple, list) or len(interval) != 2:
                raise ValueError("two exact probability endpoints required")
            low, high = map(exact, interval)
            if not 0 <= low <= high <= 1:
                raise ValueError("probability enclosure outside unit interval")
            values.append((low, high))
        if not sum(low for low, _ in values) <= 1 <= sum(high for _, high in values):
            raise ValueError("probability envelope contains no normalized distribution")
        result[context] = tuple(values)
    return result


def _sum_interval(first, second):
    return first[0] + second[0], min(Fraction(1), first[1] + second[1])


def _encode(bounds):
    if bounds is None:
        return None
    return {"lower": str(bounds[0]), "upper": None if bounds[1] is None else str(bounds[1])}


def _divide(forecast, denominator):
    low, high = denominator
    if high == 0:
        return None
    return forecast / high, None if low == 0 else forecast / low


class IntervalPrefixChecker:
    def __init__(self, table, precision=80):
        self.table = probability_table(table)
        table_records = [{"context": list(key), "q": [list(map(str, bounds)) for bounds in self.table[key]]}
                         for key in CONTEXTS]
        self.table_digest = hashlib.sha256(json.dumps(table_records, sort_keys=True,
                                                     separators=(",", ":")).encode()).hexdigest()
        self.directed = Directed(precision)
        self.threshold = self.directed.logarithm(Fraction(40))
        self.counts = {key: [0, 0, 0, 0] for key in CONTEXTS}
        self.complement = {key + (parity,): [0, 0] for key in CONTEXTS for parity in (0, 1)}
        self.alice, self.bob = [0, 0], [0, 0]
        self.logs = [Interval(Decimal(0), Decimal(0)) for _ in ORDER]
        self.factors, self.factor_intervals, self.sequence = (hashlib.sha256() for _ in range(3))
        self.exact_factor_sequence = True
        self.maximum = self.last = Interval(Decimal(0), Decimal(0))
        self.maximum_upper_prefix, self.trials = 0, 0
        self.first_rejection = None
        self.uncertain_prefixes, self.zero_lower_prefixes, self.zero_support_prefixes = [], [], []
        self.last_forecasts, self.last_factors = {}, {}
        self.last_step_record = None

    def _factor_log(self, bounds):
        lower, upper = bounds
        low = self.directed.logarithm(lower)
        if upper is None:
            return Interval(low.lower, INFINITY)
        if lower == upper:
            return low
        return Interval(low.lower, self.directed.logarithm(upper).upper)

    def _mixture(self):
        if any(value.upper == INFINITY for value in self.logs):
            lower_points = [Interval(value.lower, value.lower) for value in self.logs]
            return Interval(self.directed.mixture_log(lower_points).lower, INFINITY)
        return self.directed.mixture_log(self.logs)

    def step(self, h, a, b, x, y):
        bits = (h, a, b, x, y)
        _bits(bits, 5)
        context, event, parity = (h, a, b), 2 * x + y, x ^ y
        row, current = self.table[context], self.counts[context]
        # These are the fixed past-count formulas of likelihood.PrefixChecker.
        # Both parity forecasts are formed before observing the selected factor.
        parity_forecasts = [tuple(Fraction(2 * n + 1, 2 * sum(self.complement[context + (c,)]) + 2)
                                 for n in self.complement[context + (c,)]) for c in (0, 1)]
        forecasts = (parity_forecasts[parity][x],
                     Fraction(2 * self.alice[x] + 1, 2 * sum(self.alice) + 2),
                     Fraction(2 * self.bob[y] + 1, 2 * sum(self.bob) + 2),
                     Fraction(2 * current[event] + 1, 2 * sum(current) + 4))
        event_q, other_q = row[event], row[3 - event]
        marginal_a = _sum_interval(row[2 * x], row[2 * x + 1])
        marginal_b = _sum_interval(row[y], row[2 + y])
        if event_q[1] == 0:
            # The complete law assigns zero mass to this event.  Conditional
            # component products on this impossible path need no 0/0 convention.
            factors = (None,) * 4
            self.zero_support_prefixes.append(self.trials + 1)
        else:
            conditional_upper = (forecasts[0] if other_q[1] == 0 else
                                 None if event_q[0] == 0 else forecasts[0] * (1 + other_q[1] / event_q[0]))
            conditional = (forecasts[0] * (1 + other_q[0] / event_q[1]),
                           conditional_upper)
            factors = (conditional, _divide(forecasts[1], marginal_a),
                       _divide(forecasts[2], marginal_b), _divide(forecasts[3], event_q))
            if event_q[0] == 0:
                self.zero_lower_prefixes.append(self.trials + 1)
            if not self.zero_support_prefixes:
                for index, factor in enumerate(factors):
                    self.logs[index] = self.directed.add(self.logs[index], self._factor_log(factor))
        self.last_forecasts = {name: str(value) for name, value in zip(ORDER, forecasts)}
        self.last_factors = {name: _encode(value) for name, value in zip(ORDER, factors)}
        record = {"bits": list(bits), "forecasts": self.last_forecasts, "factors": self.last_factors,
                  "parity_forecasts": [list(map(str, values)) for values in parity_forecasts],
                  "q_event": _encode(event_q), "q_same_parity_other": _encode(other_q),
                  "alice_marginal": _encode(marginal_a), "bob_marginal": _encode(marginal_b)}
        self.last_step_record = record
        self.factor_intervals.update(json.dumps(record, sort_keys=True, separators=(",", ":")).encode())
        for factor in factors:
            if factor is None or factor[1] is None or factor[0] != factor[1]:
                self.exact_factor_sequence = False
            elif self.exact_factor_sequence:
                self.factors.update(fraction_bytes(factor[0]))
        self.sequence.update(bytes(bits))
        current[event] += 1
        self.complement[context + (parity,)][x] += 1
        self.alice[x] += 1
        self.bob[y] += 1
        self.trials += 1
        self.last = Interval(INFINITY, INFINITY) if self.zero_support_prefixes else self._mixture()
        if self.last.upper > self.maximum.upper:
            self.maximum_upper_prefix = self.trials
        self.maximum = Interval(max(self.maximum.lower, self.last.lower), max(self.maximum.upper, self.last.upper))
        if self.last.lower >= self.threshold.upper and self.first_rejection is None:
            self.first_rejection = self.trials
        if self.last.lower < self.threshold.upper and self.last.upper >= self.threshold.lower:
            self.uncertain_prefixes.append(self.trials)
        return self.last

    def result(self):
        compatible = (self.trials > 0 and self.first_rejection is None
                      and self.maximum.upper < self.threshold.lower)
        if self.trials == 0:
            status = "inconclusive"
        elif self.first_rejection is not None:
            status = "point_excluded"
        elif compatible:
            status = "all_prefix_witness_verified"
        else:
            status = "numerical_boundary_unresolved"
        components = None if self.zero_support_prefixes else {
            name: value.encode() for name, value in zip(ORDER, self.logs)}
        return {"schema": "stage10-interval-prefix/v1", "status": status, "trials": self.trials,
                "all_prefixes_checked": True, "all_prefixes_below_threshold_certified": compatible,
                "terminal_log_e": self.last.encode(), "maximum_log_e": self.maximum.encode(),
                "maximum_upper_prefix": self.maximum_upper_prefix, "first_rejection": self.first_rejection,
                "uncertain_prefixes": list(self.uncertain_prefixes),
                "zero_lower_probability_prefixes": list(self.zero_lower_prefixes),
                "zero_support_prefixes": list(self.zero_support_prefixes),
                "component_terminal_log_e": components,
                "factor_sequence_sha256": self.factors.hexdigest() if self.exact_factor_sequence else None,
                "factor_interval_sequence_sha256": self.factor_intervals.hexdigest(),
                "trial_bit_sequence_sha256": self.sequence.hexdigest(),
                "probability_table_sha256": self.table_digest,
                "last_step": self.last_step_record,
                "counts": [{"h": h, "a": a, "b": b, "counts": list(self.counts[h, a, b])}
                           for h, a, b in CONTEXTS],
                "pooled_counts": {"alice": list(self.alice), "bob": list(self.bob)},
                "numerical_precision": self.directed.context.prec,
                "threshold": "40", "per_run_alpha": "1/40", "new_confidence_budget_spent": False,
                "normalized_probability_envelope": True, "interval_probability_observer": True,
                "q_source_proof_required": True, "quantum_source_binding_verified": False,
                "complete_positivity_claimed": False}


def check_prefixes(trials, table, precision=80):
    checker = IntervalPrefixChecker(table, precision)
    for trial in trials:
        if type(trial) not in (tuple, list) or len(trial) != 5:
            raise ValueError("ordered five-bit trial required")
        checker.step(*trial)
    return checker.result()
