"""Integer-lattice four-process checker with an explicit zero-boundary mode.

The q-source proof belongs to the raw producer's consumer.  This checker uses
the original beta/Dirichlet count formulas and spends no new confidence budget.
"""
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import itertools
import json

from independent import Arithmetic, Bounds, COMPONENTS, THRESHOLD, factor_bytes, trial_bits


CONTEXTS = tuple(itertools.product((0, 1), repeat=3))


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _exact(value):
    _require(type(value) in (Fraction, int, str), "exact rational probability endpoint required")
    return Fraction(value)


def probability_table(table, allow_zero_lower=False):
    _require(type(allow_zero_lower) is bool, "explicit boolean zero-boundary mode required")
    _require(type(table) is dict, "complete eight-context probability enclosure required")
    for context in table:
        _require(type(context) is tuple and len(context) == 3 and
                 all(type(n) is int and n in (0, 1) for n in context),
                 "canonical binary context required")
    _require(set(table) == set(CONTEXTS), "complete eight-context probability enclosure required")
    answer = {}
    for context in CONTEXTS:
        row = table[context]
        _require(type(row) in (tuple, list) and len(row) == 4,
                 "four outcome enclosures in 00/01/10/11 order required")
        values = []
        for interval in row:
            _require(type(interval) in (tuple, list) and len(interval) == 2,
                     "two exact probability endpoints required")
            low, high = map(_exact, interval)
            _require(0 <= low <= high <= 1, "probability enclosure outside unit interval")
            values.append((low, high))
        _require(sum(lo for lo, _ in values) <= 1 <= sum(hi for _, hi in values),
                 "probability envelope contains no normalized distribution")
        _require(allow_zero_lower or all(lo > 0 for lo, _ in values),
                 "unsupported-unresolved: strictly positive probability lower bounds required")
        answer[context] = tuple(values)
    return answer


def denominator_bounds(row, x, y):
    """Linked conditional and own-setting marginal probability bounds."""
    event, other = row[2 * x + y], row[3 - (2 * x + y)]
    _require(event[0] > 0 and other[0] > 0,
             "unsupported-unresolved: strictly positive probability lower bounds required")
    complement = (event[0] / (event[0] + other[1]),
                  event[1] / (event[1] + other[0]))
    alice = (row[2 * x][0] + row[2 * x + 1][0],
             min(Fraction(1), row[2 * x][1] + row[2 * x + 1][1]))
    bob = (row[y][0] + row[2 + y][0],
           min(Fraction(1), row[y][1] + row[2 + y][1]))
    return dict(zip(COMPONENTS, (complement, alice, bob, event)))


def _canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


@dataclass(frozen=True)
class ExtendedBounds:
    """Log-wealth lattice endpoints; None represents positive infinity."""
    lo: int | None
    hi: int | None

    def __post_init__(self):
        _require((self.lo is None or type(self.lo) is int) and
                 (self.hi is None or type(self.hi) is int) and
                 (self.lo is not None or self.hi is None) and
                 (self.hi is None or self.lo <= self.hi), "extended integer interval")


def _max_endpoint(first, second):
    return None if first is None or second is None else max(first, second)


def _extended_bounds(low, high):
    return ExtendedBounds(low, high) if low is None or high is None else Bounds(low, high)


def _boundary_denominators(row, x, y):
    event, other = row[2*x+y], row[3-(2*x+y)]
    if event[1] == 0:
        return None
    # If its opposite event is impossible, supported paths in this parity
    # have conditional probability one, even when event.lower is zero.
    low = (Fraction(1) if other[1] == 0 else event[0]/(event[0]+other[1]))
    complement = low, event[1]/(event[1]+other[0])
    alice = row[2*x][0]+row[2*x+1][0], min(Fraction(1), row[2*x][1]+row[2*x+1][1])
    bob = row[y][0]+row[2+y][0], min(Fraction(1), row[y][1]+row[2+y][1])
    return dict(zip(COMPONENTS, (complement, alice, bob, event)))


def _rational_bounds(bounds):
    return None if bounds is None else {"lower": str(bounds[0]),
                                       "upper": None if bounds[1] is None else str(bounds[1])}


class IntervalPrefixes:
    def __init__(self, q_table, bits=240, *, allow_zero_lower=False):
        self.q = probability_table(q_table, allow_zero_lower)
        self.allow_zero_lower = allow_zero_lower
        self.arithmetic = Arithmetic(bits)
        self.threshold = self.arithmetic.log(THRESHOLD)
        self.cells = {key: [0] * 4 for key in CONTEXTS}
        self.complements = {key + (parity,): [0, 0]
                            for key in CONTEXTS for parity in (0, 1)}
        self.alice, self.bob = [0, 0], [0, 0]
        self.denominators = {key: Bounds(0, 0) for key in COMPONENTS}
        self.components = {key: Bounds(0, 0) for key in COMPONENTS}
        self.last = self.maximum = Bounds(0, 0)
        self.count, self.maximum_upper_prefix = 0, 0
        self.first_rejection, self.uncertain_prefixes = None, []
        self.prefixes = []
        self.event_digest, self.interval_digest = hashlib.sha256(), hashlib.sha256()
        self.last_denominators = None
        records = [{"context": list(key), "q": [list(map(str, pair)) for pair in self.q[key]]}
                   for key in CONTEXTS]
        self.table_digest = hashlib.sha256(_canonical(records).encode()).hexdigest()
        if self.allow_zero_lower:
            self.zero_lower_prefixes, self.zero_support_prefixes = [], []
            self.unbounded_components = dict.fromkeys(COMPONENTS, False)
            self.factors, self.factor_intervals = hashlib.sha256(), hashlib.sha256()
            self.exact_factor_sequence = True
            self.last_step_record = None

    def step(self, trial):
        if self.allow_zero_lower:
            return self._boundary_step(trial)
        _require(all(hasattr(trial, name) for name in ("row", "h", "a", "b", "x", "y")),
                 "original ordered trial record required")
        h, a, b, x, y = trial_bits(trial, self.count + 1)
        context, parity = (h, a, b), x ^ y
        denominators = denominator_bounds(self.q[context], x, y)
        for name, (low, high) in denominators.items():
            interval = Bounds(self.arithmetic.log(low).lo, self.arithmetic.log(high).hi)
            self.denominators[name] += interval
        self.cells[context][2 * x + y] += 1
        self.complements[context + (parity,)][x] += 1
        self.alice[x] += 1
        self.bob[y] += 1
        numerators = {
            "alice": self.arithmetic.predictor_log(self.alice, 2),
            "bob": self.arithmetic.predictor_log(self.bob, 2),
            "complement": sum((self.arithmetic.predictor_log(counts, 2)
                               for counts in self.complements.values()), start=Bounds(0, 0)),
            "full": sum((self.arithmetic.predictor_log(counts, 4)
                         for counts in self.cells.values()), start=Bounds(0, 0)),
        }
        self.components = {name: numerators[name] - self.denominators[name]
                           for name in COMPONENTS}
        self.last = self.arithmetic.mixture_log([self.components[name] for name in COMPONENTS])
        self.count += 1
        self.event_digest.update(bytes((h, a, b, x, y)))
        self.interval_digest.update(_canonical([self.count, self.last.lo, self.last.hi]).encode() + b"\n")
        self.prefixes.append(dict(prefix=self.count, **self.arithmetic.record(self.last)))
        self.last_denominators = {name: {"lower": str(pair[0]), "upper": str(pair[1])}
                                  for name, pair in denominators.items()}
        if self.last.hi > self.maximum.hi:
            self.maximum_upper_prefix = self.count
        self.maximum = Bounds(max(self.maximum.lo, self.last.lo), max(self.maximum.hi, self.last.hi))
        if self.first_rejection is None and self.last.lo >= self.threshold.hi:
            self.first_rejection = self.count
        if self.last.lo < self.threshold.hi and self.last.hi >= self.threshold.lo:
            self.uncertain_prefixes.append(self.count)
        return self.last

    def _log_record(self, value):
        return {"lower": "Infinity" if value.lo is None else str(Fraction(value.lo, self.arithmetic.scale)),
                "upper": "Infinity" if value.hi is None else str(Fraction(value.hi, self.arithmetic.scale))}

    def _factor_record(self, bits, row, denominators):
        h,a,b,x,y = bits
        context, parity, event = (h,a,b), x ^ y, 2*x+y
        parity_forecasts = [[Fraction(2*n+1, 2*sum(self.complements[context+(c,)])+2)
                             for n in self.complements[context+(c,)]] for c in (0,1)]
        forecasts = (parity_forecasts[parity][x],
                     Fraction(2*self.alice[x]+1, 2*sum(self.alice)+2),
                     Fraction(2*self.bob[y]+1, 2*sum(self.bob)+2),
                     Fraction(2*self.cells[context][event]+1, 2*sum(self.cells[context])+4))
        factors = (None,)*4 if denominators is None else tuple(
            (forecast/denominators[name][1],
             None if denominators[name][0] == 0 else forecast/denominators[name][0])
            for name, forecast in zip(COMPONENTS,forecasts))
        marginal_a = row[2*x][0]+row[2*x+1][0], min(Fraction(1),row[2*x][1]+row[2*x+1][1])
        marginal_b = row[y][0]+row[2+y][0], min(Fraction(1),row[y][1]+row[2+y][1])
        record = {"bits":list(bits), "forecasts":dict(zip(COMPONENTS,map(str,forecasts))),
                  "factors":dict(zip(COMPONENTS,map(_rational_bounds,factors))),
                  "parity_forecasts":[list(map(str,values)) for values in parity_forecasts],
                  "q_event":_rational_bounds(row[event]), "q_same_parity_other":_rational_bounds(row[3-event]),
                  "alice_marginal":_rational_bounds(marginal_a), "bob_marginal":_rational_bounds(marginal_b)}
        self.factor_intervals.update(_canonical(record).encode())
        for factor in factors:
            if factor is None or factor[1] is None or factor[0] != factor[1]:
                self.exact_factor_sequence = False
            elif self.exact_factor_sequence:
                self.factors.update(factor_bytes(factor[0]))
        self.last_step_record = record

    def _boundary_step(self, trial):
        _require(all(hasattr(trial,name) for name in ("row","h","a","b","x","y")),
                 "original ordered trial record required")
        bits = h,a,b,x,y = trial_bits(trial,self.count+1)
        table = probability_table(self.q, allow_zero_lower=True)
        row, context, parity = table[h,a,b], (h,a,b), x ^ y
        denominators = _boundary_denominators(row,x,y)
        self._factor_record(bits,row,denominators)
        if denominators is None:
            self.zero_support_prefixes.append(self.count+1)
        else:
            if row[2*x+y][0] == 0:
                self.zero_lower_prefixes.append(self.count+1)
            if not self.zero_support_prefixes:
                for name,(low,high) in denominators.items():
                    high_log = self.arithmetic.log(high)
                    if low == 0:
                        self.unbounded_components[name] = True
                    low_log = self.arithmetic.log(low).lo if low else high_log.lo
                    # Once a zero lower denominator occurs, this finite lower
                    # slot is unused; only the certified upper log sum enters
                    # the finite lower wealth.  Its true lower log is -infinity.
                    self.denominators[name] += Bounds(low_log,high_log.hi)
        self.cells[context][2*x+y] += 1
        self.complements[context+(parity,)][x] += 1
        self.alice[x] += 1
        self.bob[y] += 1
        if self.zero_support_prefixes:
            self.last = ExtendedBounds(None,None)
        else:
            numerators = {
                "alice":self.arithmetic.predictor_log(self.alice,2),
                "bob":self.arithmetic.predictor_log(self.bob,2),
                "complement":sum((self.arithmetic.predictor_log(counts,2)
                                  for counts in self.complements.values()),start=Bounds(0,0)),
                "full":sum((self.arithmetic.predictor_log(counts,4)
                            for counts in self.cells.values()),start=Bounds(0,0))}
            self.components = {}
            for name in COMPONENTS:
                finite = numerators[name]-self.denominators[name]
                self.components[name] = _extended_bounds(finite.lo,
                                   None if self.unbounded_components[name] else finite.hi)
            if any(self.unbounded_components.values()):
                lower = self.arithmetic.mixture_log([Bounds(self.components[name].lo,
                                    self.components[name].lo) for name in COMPONENTS]).lo
                self.last = ExtendedBounds(lower,None)
            else:
                self.last = self.arithmetic.mixture_log([self.components[name] for name in COMPONENTS])
        self.count += 1
        self.event_digest.update(bytes(bits))
        self.interval_digest.update(_canonical([self.count,self.last.lo,self.last.hi]).encode()+b"\n")
        self.prefixes.append(dict(prefix=self.count,**self._log_record(self.last)))
        self.last_denominators = (None if denominators is None else
                         {name:_rational_bounds(pair) for name,pair in denominators.items()})
        if self.maximum.hi is not None and (self.last.hi is None or self.last.hi > self.maximum.hi):
            self.maximum_upper_prefix = self.count
        self.maximum = _extended_bounds(_max_endpoint(self.maximum.lo,self.last.lo),
                                       _max_endpoint(self.maximum.hi,self.last.hi))
        if self.first_rejection is None and (self.last.lo is None or self.last.lo >= self.threshold.hi):
            self.first_rejection = self.count
        if self.last.lo is not None and self.last.lo < self.threshold.hi and (
                self.last.hi is None or self.last.hi >= self.threshold.lo):
            self.uncertain_prefixes.append(self.count)
        return self.last

    def result(self):
        if self.allow_zero_lower:
            return self._boundary_result()
        compatible = self.count > 0 and self.maximum.hi < self.threshold.lo
        status = ("inconclusive" if self.count == 0 else
                  "point_excluded" if self.first_rejection is not None else
                  "all_prefix_witness_verified" if compatible else
                  "numerical_boundary_unresolved")
        return {
            "schema": "stage10-interval-prefix-independent/v1", "status": status,
            "trials": self.count, "prefixes_checked": self.count, "all_prefixes_checked": True,
            "all_prefixes_below_threshold_certified": compatible,
            "prefix_log_e": list(self.prefixes),
            "maximum_log_e": self.arithmetic.record(self.maximum),
            "terminal_log_e": self.arithmetic.record(self.last),
            "maximum_upper_prefix": self.maximum_upper_prefix,
            "first_rejection": self.first_rejection,
            "uncertain_prefixes": list(self.uncertain_prefixes),
            "component_terminal_log_e": {name: self.arithmetic.record(self.components[name])
                                         for name in COMPONENTS},
            "trial_bit_sequence_sha256": self.event_digest.hexdigest(),
            "prefix_interval_sha256": self.interval_digest.hexdigest(),
            "probability_table_sha256": self.table_digest,
            "counts": [dict(zip(("h", "a", "b"), key), counts=list(self.cells[key]))
                       for key in CONTEXTS],
            "pooled_counts": {"alice": list(self.alice), "bob": list(self.bob)},
            "last_denominators": self.last_denominators,
            "precision_bits": self.arithmetic.bits,
            "threshold": "40", "per_run_alpha": "1/40", "new_confidence_budget_spent": False,
            "normalized_probability_envelope": True, "strictly_positive_probability_lower_bounds": True,
            "interval_probability_observer": True, "q_source_proof_required": True,
            "quantum_source_binding_verified": False, "complete_positivity_claimed": False,
        }

    def _boundary_result(self):
        compatible = self.count > 0 and self.maximum.hi is not None and self.maximum.hi < self.threshold.lo
        status = ("inconclusive" if self.count == 0 else "point_excluded" if self.first_rejection is not None else
                  "all_prefix_witness_verified" if compatible else "numerical_boundary_unresolved")
        return {"schema":"stage10-interval-prefix-independent/v1", "status":status,
                "trials":self.count,"prefixes_checked":self.count,"all_prefixes_checked":True,
                "all_prefixes_below_threshold_certified":compatible,"prefix_log_e":list(self.prefixes),
                "maximum_log_e":self._log_record(self.maximum),"terminal_log_e":self._log_record(self.last),
                "maximum_upper_prefix":self.maximum_upper_prefix,"first_rejection":self.first_rejection,
                "uncertain_prefixes":list(self.uncertain_prefixes),
                "zero_lower_probability_prefixes":list(self.zero_lower_prefixes),
                "zero_support_prefixes":list(self.zero_support_prefixes),
                "component_terminal_log_e":None if self.zero_support_prefixes else
                        {name:self._log_record(self.components[name]) for name in COMPONENTS},
                "factor_sequence_sha256":self.factors.hexdigest() if self.exact_factor_sequence else None,
                "factor_interval_sequence_sha256":self.factor_intervals.hexdigest(),
                "trial_bit_sequence_sha256":self.event_digest.hexdigest(),
                "prefix_interval_sha256":self.interval_digest.hexdigest(),
                "probability_table_sha256":self.table_digest,
                "last_step":self.last_step_record,
                "counts":[dict(zip(("h","a","b"),key),counts=list(self.cells[key])) for key in CONTEXTS],
                "pooled_counts":{"alice":list(self.alice),"bob":list(self.bob)},
                "last_denominators":self.last_denominators,"precision_bits":self.arithmetic.bits,
                "threshold":"40","per_run_alpha":"1/40","new_confidence_budget_spent":False,
                "normalized_probability_envelope":True,"strictly_positive_probability_lower_bounds":False,
                "allow_zero_lower":True,"interval_probability_observer":True,"q_source_proof_required":True,
                "quantum_source_binding_verified":False,"complete_positivity_claimed":False}


def iter_prefixes(trials, q_table, bits=240, *, allow_zero_lower=False):
    checker = IntervalPrefixes(q_table, bits, allow_zero_lower=allow_zero_lower)
    for trial in trials:
        yield checker.step(trial)


def check_run(trials, q_table, bits=240, *, allow_zero_lower=False):
    checker = IntervalPrefixes(q_table, bits, allow_zero_lower=allow_zero_lower)
    for trial in trials:
        checker.step(trial)
    return checker.result()
