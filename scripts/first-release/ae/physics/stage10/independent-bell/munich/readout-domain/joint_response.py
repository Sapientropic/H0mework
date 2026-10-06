"""Source-coupled gain caps constrain all eight joint contexts simultaneously."""
from fractions import Fraction
import math

from response_projection import CONTEXTS, FullProfile
from shared_response import BRACKET, ROLES, bias_table


RAYS = ("uniform", "alice", "bob")


def caps(values):
    if type(values) not in (list, tuple) or len(values) != 4 or any(type(v) is bool for v in values):
        raise ValueError("Four ordered source response caps required")
    result = tuple(map(Fraction, values))
    if any(not 0 <= v <= 1 for v in result):
        raise ValueError("Legal source response caps required")
    return result


def ray_caps(ray, t):
    t = Fraction(t)
    if ray not in RAYS or not 0 <= t <= 1:
        raise ValueError("Predeclared response ray required")
    return (t, t, t, t) if ray == "uniform" else (t, t, Fraction(1), Fraction(1)) if ray == "alice" else (Fraction(1), Fraction(1), t, t)


def witness_caps(primitive):
    result = []
    scale = 1 << 48
    for side, setting in ROLES:
        effect = primitive[side][setting]
        mu, u, z = (Fraction(effect[name]) for name in ("mu", "u", "z"))
        square = u * u + z * z
        if not -1 <= mu <= 1 or square > (1 - abs(mu)) ** 2:
            raise ValueError("Original lawful primitive required")
        root = math.isqrt(square.numerator * scale * scale // square.denominator)
        if Fraction(root * root, scale * scale) < square:
            root += 1
        bound = Fraction(root, scale)
        if not 0 <= bound <= 1 or bound * bound < square:
            raise ValueError("Outward primitive gain bound failed")
        result.append(bound)
    return tuple(result)


def individual_box_caps(envelopes):
    if [(row["side"], row["setting"]) for row in envelopes] != list(ROLES):
        raise ValueError("Ordered cp0002 response roles required")
    lower = max(Fraction(row["canonical_gain"][0]) for row in envelopes)
    value = Fraction(-(-lower.numerator * 1000000 // lower.denominator), 1000000)
    if any(not Fraction(row["canonical_gain"][0]) <= value <= Fraction(row["canonical_gain"][1]) for row in envelopes):
        raise ValueError("Control outside original individual gain projections")
    return (value,) * 4


def record(value):
    return {name: value[name] for name in ("log_e", "contexts")}


class JointProfile:
    def __init__(self, full, biases):
        self.full, self.biases = full, bias_table(biases)
        self.contexts = []
        ar = full.arithmetic
        for key in CONTEXTS:
            count = full.counts[key]
            even, odd = count[0] + count[3], count[1] + count[2]
            if not even or not odd:
                raise ValueError("Both observed parities required in every context")
            corners = [a * b for a in self.biases["alice", key[1]] for b in self.biases["bob", key[2]]]
            mle = Fraction(even, even + odd)
            likelihood = ar.add(ar.scale(ar.logarithm(mle), even), ar.scale(ar.logarithm(1 - mle), odd))
            self.contexts.append((key, even, odd, min(corners), max(corners), mle, likelihood))

    def at(self, proposed):
        proposed = caps(proposed)
        ar, value = self.full.arithmetic, self.full.mle_log
        records, infinite = [], False
        for key, even, odd, product_lo, product_hi, mle, mle_likelihood in self.contexts:
            radius = proposed[key[1]] * proposed[2 + key[2]]
            lo = max(Fraction(0), (1 + product_lo - radius) / 2)
            hi = min(Fraction(1), (1 + product_hi + radius) / 2)
            maximizing = min(max(mle, lo), hi)
            records.append({"context": list(key), "parity_counts": [even, odd],
                            "gain_product_cap": str(radius),
                            "bias_product_outer_interval": list(map(str, (product_lo, product_hi))),
                            "allowed_even_probability": list(map(str, (lo, hi))),
                            "parity_mle": str(mle), "maximizing_even_probability": str(maximizing)})
            if maximizing in (0, 1):
                infinite = True
            elif maximizing != mle:
                denominator = ar.add(ar.scale(ar.logarithm(maximizing), even),
                                     ar.scale(ar.logarithm(1 - maximizing), odd))
                value = ar.add(value, ar.subtract(mle_likelihood, denominator))
        return {"log_e": {"infinite": True} if infinite else value.encode(), "contexts": records,
                "interval": None if infinite else value}

    def bounds(self, ray):
        low, high = Fraction(0), Fraction(1)
        threshold = self.full.threshold
        first, last = self.at(ray_caps(ray, low)), self.at(ray_caps(ray, high))
        if (first["interval"] is not None and first["interval"].lower < threshold.upper) or \
                last["interval"] is None or last["interval"].upper >= threshold.lower:
            raise ValueError("Joint response threshold not bracketed")
        for _ in range(36):
            middle = (low + high) / 2
            candidate = self.at(ray_caps(ray, middle))["interval"]
            if candidate is None or candidate.lower >= threshold.upper:
                low = middle
            else:
                high = middle
        left, right = self.at(ray_caps(ray, low)), self.at(ray_caps(ray, high))
        if (left["interval"] is not None and left["interval"].lower < threshold.upper) or \
                right["interval"] is None or right["interval"].upper >= threshold.lower or high - low > BRACKET:
            raise ValueError("Entire joint low-response orthant not certified")
        return {"ray": ray, "profile_threshold_bracket": list(map(str, (low, high))),
                "threshold_bracket_gap": str(high - low),
                "lower_caps": list(map(str, ray_caps(ray, low))),
                "upper_caps": list(map(str, ray_caps(ray, high))),
                "profile_lower_endpoint": record(left), "profile_upper_endpoint": record(right),
                "component_threshold": "80", "entire_lower_orthant_excluded": True,
                "all_eight_contexts_used": True, "actual_gain_extremum_sharpness_claimed": False}

    def control(self, name, proposed):
        value = self.at(proposed)
        interval = value["interval"]
        if interval is None or interval.lower >= self.full.threshold.upper:
            status = "entire_lower_orthant_excluded"
        elif interval.upper < self.full.threshold.lower:
            status = "necessary_profile_not_excluded"
        else:
            raise ValueError("Control threshold not resolved")
        return {"name": name, "caps": list(map(str, caps(proposed))), "status": status, **record(value)}
