"""Independent native response-box realizers of fixed signed source effects.

The checker consumes a certified atomic spectral interval and produces detector
coordinates for a given effect. It does not generate a new physical prediction
from that effect or identify common detector parameters across settings.
"""
from fractions import Fraction
from math import isqrt

from detector_fiber_independent import Effect, exact


def _effect(value):
    if isinstance(value, Effect):
        return value
    if type(value) is dict:
        if set(value) != {"mu", "u", "z"}:
            raise ValueError("source_effect_primitive_shape")
        return Effect(**value)
    return Effect(value.mu, value.u, value.z)


def interval(row):
    if type(row) not in (list, tuple) or len(row) != 2:
        raise ValueError("two_atomic_probability_endpoints_required")
    lower, upper = map(exact, row)
    if not 0 <= lower <= upper <= 1:
        raise ValueError("physical_ordered_atomic_response_required")
    return lower, upper


def feasible(effect, bright, dark):
    point, b, r = _effect(effect), exact(bright), exact(dark)
    if not 0 <= r < b <= 1:
        raise ValueError("strictly_ordered_physical_atomic_spectrum_required")
    gain_squared = point.u ** 2 + point.z ** 2
    if gain_squared == 0:
        raise ValueError("positive_signed_source_gain_required")
    gap, trace = b - r, b + r
    # Both nonnegative constraints can be squared without changing signs.
    # Direct ratio bounds supply an independent decision before constructing
    # the polynomial slacks used by the receipt's common representation.
    first_gain_upper = (1 - point.mu) * gap / trace
    second_gain_upper = (1 + point.mu) * gap / (2 - trace)
    accepted = gain_squared <= first_gain_upper ** 2 and gain_squared <= second_gain_upper ** 2
    first = (first_gain_upper ** 2 - gain_squared) * trace ** 2
    second = (second_gain_upper ** 2 - gain_squared) * (2 - trace) ** 2
    return accepted, (first, second)


def square_root_interval(square, bits=240):
    square = exact(square)
    if square < 0 or type(bits) is not int or bits < 32:
        raise ValueError("nonnegative_gain_square_and_precision_required")
    root_numerator, root_denominator = isqrt(square.numerator), isqrt(square.denominator)
    if root_numerator ** 2 == square.numerator and root_denominator ** 2 == square.denominator:
        root = Fraction(root_numerator, root_denominator)
        return root, root
    scale = 1 << bits
    scaled_floor = isqrt((square.numerator << (2 * bits)) // square.denominator)
    lo, hi = Fraction(scaled_floor, scale), Fraction(scaled_floor + 1, scale)
    if not lo ** 2 <= square <= hi ** 2:
        raise ValueError("gain_square_root_enclosure_failure")
    return lo, hi


def realize_box(effect, bright, dark):
    point = _effect(effect)
    bl, bu = interval(bright)
    rl, ru = interval(dark)
    if bl <= ru:
        return {"status": "response_gap_not_uniformly_positive", "whole_response_box_realizes_source_effect": False}
    accepted, squared_slacks = feasible(point, bl, ru)
    best_accepted, _ = feasible(point, bu, rl)
    if accepted:
        status = "whole_response_box_realizes_source_effect"
    elif best_accepted:
        status = "undetermined_response_box"
    else:
        status = "whole_response_box_excluded_for_source_effect"
    result = {"status": status, "whole_response_box_realizes_source_effect": accepted,
              "worst_corner": [str(bl), str(ru)], "worst_corner_squared_slacks": list(map(str, squared_slacks)),
              "source_effect": {name: str(getattr(point, name)) for name in ("mu", "u", "z")}}
    if not accepted:
        return result
    g2 = point.u ** 2 + point.z ** 2
    gain_lo, gain_hi = square_root_interval(g2)
    gap_lo, gap_hi = bl - ru, bu - rl
    trace_lo, trace_hi = bl + rl, bu + ru
    k_lo, k_hi = gain_lo / gap_hi, gain_hi / gap_lo
    # Monotonic positive interval products bound every response in the box.
    trace_product_lo, trace_product_hi = k_lo * trace_lo, k_hi * trace_hi
    d_lo = max(Fraction(0), (1 - point.mu - trace_product_hi) / 2)
    d_hi = min(1 - k_lo, (1 - point.mu - trace_product_lo) / 2)
    if not 0 <= d_lo <= d_hi < 1:
        raise ValueError("physical_realizer_background_interval_empty")
    eta_lo = max(Fraction(0), k_lo / (1 - d_lo))
    eta_hi = min(Fraction(1), k_hi / (1 - d_hi))
    if eta_lo > eta_hi:
        raise ValueError("physical_realizer_efficiency_interval_empty")
    result.update(detection_interval=[str(k_lo), str(k_hi)], background_interval=[str(d_lo), str(d_hi)],
                  fragment_efficiency_interval=[str(eta_lo), str(eta_hi)],
                  generator_definition={"gain_squared": str(g2), "detection": "sqrt(gain_squared)/(p_bright-p_dark)",
                                        "background": "(1-source_mu-detection*(p_bright+p_dark))/2",
                                        "fragment_efficiency": "detection/(1-background)",
                                        "axis_x": "-source_u/sqrt(gain_squared)", "axis_z": "-source_z/sqrt(gain_squared)"},
                  source_effect_restored_exactly=True, normalized_axis_is_symbolic=True,
                  intervals_intersected_with_exact_realizer_domain=True)
    return result


def responses_separated(first, second):
    separated = False
    for name in ("p_bright", "p_dark"):
        left, right = first[name], second[name]
        if type(left) not in (list, tuple) or type(right) not in (list, tuple) or len(left) != 2 or len(right) != 2:
            raise ValueError("complete_atomic_response_intervals_required")
        a, b, c, d = map(exact, (*left, *right))
        if a > b or c > d:
            raise ValueError("ordered_atomic_response_intervals_required")
        separated = separated or b < c or d < a
    return separated
