"""Directed log arithmetic for the four fixed source likelihood processes."""
from dataclasses import dataclass
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction
import hashlib
from itertools import product


CONTEXTS = tuple(product(range(2), repeat=3))
ORDER = ('complement', 'alice', 'bob', 'full')
WEIGHTS = (Fraction(1, 6), Fraction(1, 6), Fraction(1, 6), Fraction(1, 2))


@dataclass(frozen=True)
class Interval:
    lower: Decimal
    upper: Decimal

    def encode(self):
        return {'lower': str(self.lower), 'upper': str(self.upper)}


class Directed:
    def __init__(self, precision=80):
        if type(precision) is not int or precision < 40:
            raise ValueError('At least forty Decimal digits are required')
        self.context = Context(prec=precision, Emin=-999999999, Emax=999999999)
        self.cache = {}

    def add(self, first, second):
        with localcontext(self.context) as context:
            context.rounding = ROUND_FLOOR
            lower = first.lower + second.lower
            context.rounding = ROUND_CEILING
            upper = first.upper + second.upper
        return Interval(lower, upper)

    def subtract(self, first, second):
        return self.add(first, Interval(second.upper.copy_negate(), second.lower.copy_negate()))

    def logarithm(self, value):
        value = Fraction(value)
        if value <= 0:
            raise ValueError('Positive exact rational required')
        if value not in self.cache:
            with localcontext(self.context) as context:
                context.rounding = ROUND_FLOOR
                lower = Decimal(value.numerator) / Decimal(value.denominator)
                context.rounding = ROUND_CEILING
                upper = Decimal(value.numerator) / Decimal(value.denominator)
                result = Interval(lower.ln().next_minus(context), upper.ln().next_plus(context))
            self.cache[value] = result
        return self.cache[value]

    def decimal_logarithm(self, interval):
        if interval.lower <= 0:
            raise ValueError('Positive logarithm interval required')
        with localcontext(self.context) as context:
            return Interval(interval.lower.ln().next_minus(context), interval.upper.ln().next_plus(context))

    def exponential(self, interval):
        with localcontext(self.context) as context:
            low = interval.lower.exp().next_minus(context)
            high = interval.upper.exp().next_plus(context)
        return Interval(max(Decimal(0), low), high)

    def scale(self, interval, weight):
        weight = Fraction(weight)
        if weight < 0:
            raise ValueError('Nonnegative mixture weight required')
        with localcontext(self.context) as context:
            context.rounding = ROUND_FLOOR
            low = interval.lower * Decimal(weight.numerator) / Decimal(weight.denominator)
            context.rounding = ROUND_CEILING
            high = interval.upper * Decimal(weight.numerator) / Decimal(weight.denominator)
        return Interval(low, high)

    def mixture_log(self, components):
        shift = max(value.upper for value in components)
        shifted = Interval(shift, shift)
        total = Interval(Decimal(0), Decimal(0))
        for component, weight in zip(components, WEIGHTS):
            total = self.add(total, self.scale(self.exponential(self.subtract(component, shifted)), weight))
        return self.add(shifted, self.decimal_logarithm(total))


def fraction_bytes(value):
    value = Fraction(value)
    if value <= 0:
        raise ValueError('Positive factor required')
    answer = bytearray()
    for number in (value.numerator, value.denominator):
        raw = number.to_bytes((number.bit_length() + 7) // 8, 'big')
        answer.extend(len(raw).to_bytes(8, 'big'))
        answer.extend(raw)
    return bytes(answer)


class PrefixChecker:
    def __init__(self, table, precision=80):
        if set(table) != set(CONTEXTS):
            raise ValueError('Complete source table required')
        for row in table.values():
            if len(row) != 4 or any(not isinstance(q, Fraction) or q < 0 for q in row) or sum(row) != 1:
                raise ValueError('Source distribution must be exact, nonnegative and normalized')
        self.table = table
        self.directed = Directed(precision)
        self.threshold = self.directed.logarithm(Fraction(40))
        self.counts = {key: [0, 0, 0, 0] for key in CONTEXTS}
        self.complement = {key + (parity,): [0, 0] for key in CONTEXTS for parity in (0, 1)}
        self.alice = [0, 0]
        self.bob = [0, 0]
        self.logs = [Interval(Decimal(0), Decimal(0)) for _ in ORDER]
        self.factors = hashlib.sha256()
        self.sequence = hashlib.sha256()
        self.maximum = Interval(Decimal(0), Decimal(0))
        self.maximum_upper_prefix = 0
        self.first_rejection = None
        self.uncertain_prefixes = []
        self.trials = 0
        self.last = Interval(Decimal(0), Decimal(0))

    def step(self, h, a, b, x, y):
        bits = (h, a, b, x, y)
        if any(type(v) is not int or v not in (0, 1) for v in bits):
            raise ValueError('Canonical binary trial required')
        q = self.table[h, a, b]
        event = 2 * x + y
        if q[event] == 0:
            raise ValueError('Observed zero-probability source event')
        current = self.counts[h, a, b]
        parity = x ^ y
        # Both parity forecasts use only past counts; the current event selects the factor.
        forecasts = [tuple(Fraction(2 * n + 1, 2 * sum(self.complement[h, a, b, c]) + 2)
                           for n in self.complement[h, a, b, c]) for c in (0, 1)]
        mass = q[0] + q[3] if parity == 0 else q[1] + q[2]
        marginal_a = q[2 * x] + q[2 * x + 1]
        marginal_b = q[y] + q[2 + y]
        factors = (forecasts[parity][x] * mass / q[event],
                   Fraction(2 * self.alice[x] + 1, 2 * sum(self.alice) + 2) / marginal_a,
                   Fraction(2 * self.bob[y] + 1, 2 * sum(self.bob) + 2) / marginal_b,
                   Fraction(2 * current[event] + 1, 2 * sum(current) + 4) / q[event])
        for index, factor in enumerate(factors):
            self.logs[index] = self.directed.add(self.logs[index], self.directed.logarithm(factor))
            self.factors.update(fraction_bytes(factor))
        self.sequence.update(bytes(bits))
        current[event] += 1
        self.complement[h, a, b, parity][x] += 1
        self.alice[x] += 1
        self.bob[y] += 1
        self.trials += 1
        self.last = self.directed.mixture_log(self.logs)
        if self.last.upper > self.maximum.upper:
            self.maximum_upper_prefix = self.trials
        self.maximum = Interval(max(self.maximum.lower, self.last.lower), max(self.maximum.upper, self.last.upper))
        if self.last.lower >= self.threshold.upper and self.first_rejection is None:
            self.first_rejection = self.trials
        if self.last.lower < self.threshold.upper and self.last.upper >= self.threshold.lower:
            self.uncertain_prefixes.append(self.trials)
        return self.last

    def result(self):
        if self.trials == 0:
            status = 'inconclusive'
        elif self.first_rejection is not None:
            status = 'point_excluded'
        elif self.uncertain_prefixes:
            status = 'numerical_boundary_unresolved'
        else:
            status = 'all_prefix_witness_verified'
        return {'status': status, 'trials': self.trials, 'all_prefixes_checked': True,
                'terminal_log_e': self.last.encode(), 'maximum_log_e': self.maximum.encode(),
                'maximum_upper_prefix': self.maximum_upper_prefix, 'first_rejection': self.first_rejection,
                'uncertain_prefixes': self.uncertain_prefixes,
                'component_terminal_log_e': {k: v.encode() for k, v in zip(ORDER, self.logs)},
                'factor_sequence_sha256': self.factors.hexdigest(),
                'trial_bit_sequence_sha256': self.sequence.hexdigest(),
                'counts': [{'h': h, 'a': a, 'b': b, 'counts': self.counts[h, a, b]}
                           for h, a, b in CONTEXTS],
                'pooled_counts': {'alice': self.alice, 'bob': self.bob},
                'numerical_precision': self.directed.context.prec}


def check_prefixes(trials, table, precision=80):
    checker = PrefixChecker(table, precision)
    for trial in trials:
        checker.step(trial.h, trial.a, trial.b, trial.x, trial.y)
    return checker.result()
