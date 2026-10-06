"""Joint likelihood bounds for one response shared across four source contexts."""
from fractions import Fraction
import itertools

from response_projection import CONTEXTS, FullProfile


ROLES = tuple(itertools.product(("alice", "bob"), (0, 1)))
BRACKET = Fraction(1, 1 << 36)


def bias_table(rows):
    if type(rows) is not list or len(rows) != 4:
        raise ValueError("Four original own-setting bias projections required")
    result = {}
    for row in rows:
        side, setting = row["side"], row["setting"]
        if side not in ("alice", "bob") or type(setting) is not int or setting not in (0, 1):
            raise ValueError("Original bias role required")
        interval = row["mu_outer_interval"]
        if len(interval) != 2 or any(type(x) is not str for x in interval):
            raise ValueError("Exact bias endpoints required")
        lo, hi = map(Fraction, interval)
        if not -1 <= lo <= hi <= 1 or (side, setting) in result:
            raise ValueError("Ordered legal bias intervals required")
        result[side, setting] = (lo, hi)
    return result


class SharedProfile:
    def __init__(self, full, biases, side, setting):
        if side not in ("alice", "bob") or type(setting) is not int or setting not in (0, 1):
            raise ValueError("One source side and own setting required")
        self.full, self.side, self.setting = full, side, setting
        self.biases = bias_table(biases)
        self.contexts = []
        ar = full.arithmetic
        for key in CONTEXTS:
            if key[1 if side == "alice" else 2] != setting:
                continue
            counts = full.counts[key]
            even, odd = counts[0] + counts[3], counts[1] + counts[2]
            if not even or not odd:
                raise ValueError("Shared two-sided projection requires both observed parities")
            products = [a * b for a in self.biases["alice", key[1]] for b in self.biases["bob", key[2]]]
            mle = Fraction(even, even + odd)
            likelihood = ar.add(ar.scale(ar.logarithm(mle), even), ar.scale(ar.logarithm(1 - mle), odd))
            self.contexts.append((key, even, odd, min(products), max(products), mle, likelihood))
        if len(self.contexts) != 4:
            raise ValueError("All herald and partner-setting contexts required")

    def at(self, gain):
        gain = Fraction(gain)
        if not 0 <= gain <= 1:
            raise ValueError("Legal hypothesized response cap required")
        ar, value = self.full.arithmetic, self.full.mle_log
        records, infinite = [], False
        for key, even, odd, product_lo, product_hi, mle, mle_likelihood in self.contexts:
            lo = max(Fraction(0), (1 + product_lo - gain) / 2)
            hi = min(Fraction(1), (1 + product_hi + gain) / 2)
            maximizing = min(max(mle, lo), hi)
            records.append({"context": list(key), "parity_counts": [even, odd],
                            "bias_product_outer_interval": list(map(str, (product_lo, product_hi))),
                            "allowed_even_probability": list(map(str, (lo, hi))),
                            "parity_mle": str(mle), "maximizing_even_probability": str(maximizing)})
            if maximizing in (0, 1):
                infinite = True
                continue
            denominator = ar.add(ar.scale(ar.logarithm(maximizing), even),
                                 ar.scale(ar.logarithm(1 - maximizing), odd))
            value = ar.add(value, ar.subtract(mle_likelihood, denominator))
        return {"log_e": {"infinite": True} if infinite else value.encode(), "contexts": records,
                "interval": None if infinite else value}

    def bounds(self, legacy_lower):
        lo, hi = Fraction(0), Fraction(1)
        first, last = self.at(lo), self.at(hi)
        threshold = self.full.threshold
        if (first["interval"] is not None and first["interval"].lower < threshold.upper) or \
                last["interval"] is None or last["interval"].upper >= threshold.lower:
            raise ValueError("Shared response threshold not bracketed by zero and one")
        for _ in range(36):
            middle = (lo + hi) / 2
            candidate = self.at(middle)["interval"]
            if candidate is None or candidate.lower >= threshold.upper:
                lo = middle
            else:
                hi = middle
        left, right = self.at(lo), self.at(hi)
        if (left["interval"] is not None and left["interval"].lower < threshold.upper) or \
                right["interval"] is None or right["interval"].upper >= threshold.lower or hi - lo > BRACKET:
            raise ValueError("Uniform shared-response exclusion not certified")
        legacy_lower = Fraction(legacy_lower)
        gain = max(lo, legacy_lower)
        mu_lo, mu_hi = self.biases[self.side, self.setting]
        upper = 1 - max(Fraction(0), mu_lo, -mu_hi)
        if not 0 <= gain <= upper:
            raise ValueError("Source response projections conflict")
        def record(value):
            return {"log_e": value["log_e"], "contexts": value["contexts"]}
        return {"side": self.side, "setting": self.setting,
                "shared_profile_threshold_bracket": list(map(str, (lo, hi))),
                "threshold_bracket_gap": str(hi - lo), "profile_lower_endpoint": record(left),
                "profile_upper_endpoint": record(right), "component_threshold": "80",
                "canonical_gain": list(map(str, (gain, upper))),
                "canonical_e0": list(map(str, (max(Fraction(0), -mu_hi), (1 - gain - mu_lo) / 2))),
                "canonical_e1": list(map(str, (max(Fraction(0), mu_lo), (1 - gain + mu_hi) / 2))),
                "bias_outer_interval": list(map(str, (mu_lo, mu_hi))), "legacy_gain_lower": str(legacy_lower),
                "strictly_improved_gain_lower": gain > legacy_lower,
                "all_four_contexts_share_one_source_response": True,
                "entire_low_response_interval_excluded": True,
                "whole_empirical_confidence_set_bounds": True,
                "actual_gain_extremum_sharpness_claimed": False,
                "new_confidence_budget_spent": False, "actual_ideal_label_identity_selected": False}
