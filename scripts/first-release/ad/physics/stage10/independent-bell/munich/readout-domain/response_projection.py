"""Necessary correlation and response projections of the entire original confidence set."""
from fractions import Fraction
import itertools
import math

from likelihood import Directed


CONTEXTS = tuple(itertools.product((0, 1), repeat=3))


def counts_table(rows):
    if type(rows) is not list or len(rows) != 8:
        raise ValueError("All eight original source contexts required")
    result = {}
    for row in rows:
        if set(row) != {"h", "a", "b", "counts"}:
            raise ValueError("Only the original four-outcome sufficient counts admitted")
        key = tuple(row[k] for k in ("h", "a", "b"))
        counts = row["counts"]
        if (any(type(b) is not int or b not in (0, 1) for b in key) or key in result or
                type(counts) is not list or len(counts) != 4 or any(type(n) is not int or n < 0 for n in counts)):
            raise ValueError("Unique binary contexts with natural four-outcome counts required")
        result[key] = tuple(counts)
    if set(result) != set(CONTEXTS):
        raise ValueError("Complete context inventory required")
    return result


class FullProfile:
    """Unconstrained likelihood maxima pay simultaneous necessary outer projections."""
    def __init__(self, rows, precision=80):
        self.counts = counts_table(rows)
        self.arithmetic = Directed(precision)
        self.threshold = self.arithmetic.logarithm(Fraction(80))
        zero = self.arithmetic.logarithm(Fraction(1))
        two = self.arithmetic.logarithm(Fraction(2))
        self.factorials = {}
        def factorial(n):
            if n not in self.factorials:
                self.factorials[n] = self.arithmetic.logarithm(Fraction(math.factorial(n)))
            return self.factorials[n]
        self.mle_log = zero
        for counts in self.counts.values():
            total = sum(counts)
            numerator, mle = zero, zero
            for n in counts:
                term = self.arithmetic.subtract(factorial(2 * n), factorial(n))
                term = self.arithmetic.subtract(term, self.arithmetic.scale(two, 2 * n))
                numerator = self.arithmetic.add(numerator, term)
                if n:
                    mle = self.arithmetic.add(mle, self.arithmetic.scale(self.arithmetic.logarithm(Fraction(n, total)), n))
            numerator = self.arithmetic.subtract(numerator, factorial(total + 1))
            self.mle_log = self.arithmetic.add(self.mle_log, self.arithmetic.subtract(numerator, mle))

    def correlation(self, context):
        if context not in self.counts:
            raise ValueError("An original source context required")
        counts = self.counts[context]
        grouped = (counts[0] + counts[3], counts[1] + counts[2])
        if not all(n > 0 for n in grouped):
            raise ValueError("This two-sided projection requires both observed parities")
        total = sum(grouped)
        constant = self.mle_log
        for n in grouped:
            constant = self.arithmetic.add(constant, self.arithmetic.scale(self.arithmetic.logarithm(Fraction(n, total)), n))
        return CorrelationProfile(self, context, grouped, constant)


class CorrelationProfile:
    def __init__(self, full, context, grouped, constant):
        self.full, self.context, self.grouped, self.constant = full, context, grouped, constant
        self.mle = Fraction(grouped[0], sum(grouped))

    def at(self, p):
        p = Fraction(p)
        if not 0 < p < 1:
            raise ValueError("Interior even-parity probability required")
        ar = self.full.arithmetic
        denominator = ar.add(ar.scale(ar.logarithm(p), self.grouped[0]),
                             ar.scale(ar.logarithm(1 - p), self.grouped[1]))
        return ar.subtract(self.constant, denominator)

    def bounds(self):
        threshold = self.full.threshold
        center = self.at(self.mle)
        if center.upper >= threshold.lower:
            raise ValueError("Full MLE excluded by the inherited component threshold")
        for bits in (80, 160, 320, 640, 1280):
            epsilon = Fraction(1, 1 << bits)
            if self.at(epsilon).lower >= threshold.upper and self.at(1 - epsilon).lower >= threshold.upper:
                break
        else:
            raise ValueError("No certified outside parity endpoints")
        lo, interior = epsilon, self.mle
        for _ in range(36):
            midpoint = (lo + interior) / 2
            if self.at(midpoint).lower >= threshold.upper:
                lo = midpoint
            else:
                interior = midpoint
        interior, hi = self.mle, 1 - epsilon
        for _ in range(36):
            midpoint = (interior + hi) / 2
            if self.at(midpoint).lower >= threshold.upper:
                hi = midpoint
            else:
                interior = midpoint
        left, right = self.at(lo), self.at(hi)
        if not lo < self.mle < hi or left.lower < threshold.upper or right.lower < threshold.upper:
            raise ValueError("Necessary entire-CS correlation envelope not certified")
        return {"h": self.context[0], "a": self.context[1], "b": self.context[2],
                "counts": list(self.full.counts[self.context]), "parity_counts": list(self.grouped),
                "p_mle": str(self.mle), "p_outer_interval": list(map(str, (lo, hi))),
                "correlation_outer_interval": list(map(str, (2 * lo - 1, 2 * hi - 1))),
                "lower_endpoint_log_e": left.encode(), "upper_endpoint_log_e": right.encode(),
                "mle_log_e": center.encode(), "component_threshold": "80",
                "kind": "necessary_outer_projection_of_entire_parent_confidence_set",
                "new_confidence_budget_spent": False, "point_witness_used_as_confidence_bound": False}


def response_envelopes(correlations, biases):
    if len(correlations) != 8 or len(biases) != 4:
        raise ValueError("Complete correlation and bias projection inventories required")
    bias = {(row["side"], row["setting"]): tuple(map(Fraction, row["mu_outer_interval"])) for row in biases}
    roles = tuple(itertools.product(("alice", "bob"), (0, 1)))
    if set(bias) != set(roles):
        raise ValueError("Each own-setting bias required")
    contributions = {key: [] for key in roles}
    seen = set()
    for row in correlations:
        key = tuple(row[k] for k in ("h", "a", "b"))
        if key in seen or key not in CONTEXTS:
            raise ValueError("Unique full source correlation contexts required")
        seen.add(key)
        cl, cu = map(Fraction, row["correlation_outer_interval"])
        aa, bb = bias["alice", key[1]], bias["bob", key[2]]
        products = [a * b for a in aa for b in bb]
        centered = (cl - max(products), cu - min(products))
        lower = max(Fraction(0), centered[0], -centered[1])
        contribution = {"context": list(key), "bias_product_outer_interval": list(map(str, (min(products), max(products)))),
                        "centered_correlation_outer_interval": list(map(str, centered)), "gain_lower": str(lower)}
        contributions["alice", key[1]].append(contribution)
        contributions["bob", key[2]].append(contribution)
    result = []
    for side, setting in roles:
        lo, hi = bias[side, setting]
        gain = max(Fraction(row["gain_lower"]) for row in contributions[side, setting])
        upper = 1 - max(Fraction(0), lo, -hi)
        if not -1 <= lo <= hi <= 1 or not 0 <= gain <= upper:
            raise ValueError("Response outer projections conflict with the source cone")
        result.append({"side": side, "setting": setting, "canonical_gain": list(map(str, (gain, upper))),
                       "canonical_e0": list(map(str, (max(Fraction(0), -hi), (1 - gain - lo) / 2))),
                       "canonical_e1": list(map(str, (max(Fraction(0), lo), (1 - gain + hi) / 2))),
                       "bias_outer_interval": list(map(str, (lo, hi))), "source_contributions": contributions[side, setting],
                       "kind": "necessary_outer_projection_of_entire_parent_confidence_set",
                       "fixed_law_point_used_as_confidence_bound": False, "actual_ideal_label_identity_selected": False})
    return result
