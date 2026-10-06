"""Necessary raw readout-pulse exposure of the entire original confidence set.

The registered fixed-chart ionization generator pays g <= 7 A^2/4 for
A = integral Omega_12 dt.  The old confidence projection pays g >= G.
Both are consumed before taking an outward square-root bound.
"""
from fractions import Fraction
from math import isqrt


ROLES = (("alice", 0), ("alice", 1), ("bob", 0), ("bob", 1))


def exact(value):
    if type(value) not in (str, int, Fraction):
        raise ValueError("Exact pulse or confidence coordinate required")
    return Fraction(value)


def square_root_lower(value, bits=80):
    value = exact(value)
    if value < 0 or type(bits) is not int or bits < 32:
        raise ValueError("Nonnegative square and adequate exact precision required")
    scale = 1 << bits
    return Fraction(isqrt(value.numerator * scale * scale // value.denominator), scale)


def area(pulses):
    value = Fraction(0)
    for pulse in pulses:
        duration, omega = (exact(pulse[name]) if type(pulse) is dict else exact(getattr(pulse, name))
                           for name in ("duration", "omega_r"))
        if duration < 0 or omega < 0:
            raise ValueError("Nonnegative raw pulse controls required")
        value += duration * omega
    return value


def bounds(shared_run, joint_run):
    entries = shared_run["shared_response_envelopes"]
    if [(entry["side"], entry["setting"]) for entry in entries] != list(ROLES):
        raise ValueError("Whole ordered original response projections required")
    individual = []
    for entry in entries:
        gain = exact(entry["canonical_gain"][0])
        if not 0 < gain <= 1:
            raise ValueError("Positive certified source response lower bound required")
        square = 4 * gain / 7
        individual.append({"side": entry["side"], "setting": entry["setting"],
                           "source_gain_lower": str(gain), "readout_rabi_area_squared_lower": str(square),
                           "readout_rabi_area_lower": str(square_root_lower(square)),
                           "whole_parent_confidence_set_necessary_bound": True})
    joint = []
    if [entry["ray"] for entry in joint_run["joint_response_rays"]] != ["uniform", "alice", "bob"]:
        raise ValueError("All original joint cap rays required")
    for entry in joint_run["joint_response_rays"]:
        gain = exact(entry["profile_threshold_bracket"][0])
        if not 0 < gain <= 1 or entry["entire_lower_orthant_excluded"] is not True:
            raise ValueError("Original entire low-response orthant exclusion required")
        square = 4 * gain / 7
        joint.append({"ray": entry["ray"], "source_max_gain_strict_lower": str(gain),
                      "maximum_readout_rabi_area_squared_strict_lower": str(square),
                      "maximum_readout_rabi_area_strict_lower": str(square_root_lower(square))})
    return {"individual_exposures": individual, "joint_maximum_exposures": joint,
            "area_definition": "sum_dimensionless_readout_Rabi_times_dimensionless_duration=integral_Omega12_dt",
            "source_inequality": "gain<=min(1,7*area^2/4)",
            "scope": "registered_fixed_chart_12_state_ionization_model_intersected_with_original_parent_confidence_set",
            "cycling_and_ion_rates_restricted_by_this_bound": False, "new_confidence_budget_spent": False,
            "actual_raw_controls_uniquely_identified": False}
