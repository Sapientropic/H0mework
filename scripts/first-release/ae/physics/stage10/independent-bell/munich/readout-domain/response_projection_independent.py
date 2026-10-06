"""Integer verification of necessary projections of the original parent CS.

Inputs are sufficient counts and rational proposed endpoints.  The primary
projection formulas, endpoint numerics, event archives and fitted points are
not imported.  Log enclosures reuse the signed integer atanh arithmetic.
"""
import argparse
from fractions import Fraction
from functools import lru_cache
import itertools
from pathlib import Path

import independent as source


CONTEXTS = tuple(itertools.product((0, 1), repeat=3))
ROLES = tuple(itertools.product(("alice", "bob"), (0, 1)))
KIND = "necessary_outer_projection_of_entire_parent_confidence_set"
THRESHOLD = Fraction(80)
require, rational = source.require, source.rational
BASE, ROOT = source.BASE, source.ROOT
VERSION = "stage10-munich-readout-cp0001"
PRIMARY_SCHEMA = "stage10-munich-readout-response-projection-primary/v1"
SCHEMA = "stage10-munich-readout-response-projection-independent/v1"
FILES = ("criterion-cp0001.md", "response_projection.py", "test_response_projection.py", "response_projection_run.py",
         "response_projection_independent.py", "test_response_projection_independent.py",
         "ResponseBoundsCertification.lean", "response_bounds_certify.py", "test_response_bounds_certify.py",
         "response-bounds-certification-first.json")
INPUTS = ("verification.json", "primary-first-c0002.json", "identification-first.json",
          "identification-verification.json", "identification-certification-first.json", "likelihood.py")
MODULE = ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutResponseBounds.lean"


def binary_context(value):
    require(type(value) in (list, tuple) and len(value) == 3 and
            all(type(v) is int and v in (0, 1) for v in value), "original_binary_context")
    return tuple(value)


def natural_counts(value, length):
    require(type(value) is list and len(value) == length and
            all(type(n) is int and n >= 0 for n in value), "original_natural_count_vector")
    return tuple(value)


def counts_table(rows):
    require(type(rows) is list and len(rows) == 8, "all_eight_original_contexts")
    table = {}
    for row in rows:
        require(type(row) is dict and set(row) == {"h", "a", "b", "counts"}, "original_four_outcome_row")
        key = binary_context([row[name] for name in ("h", "a", "b")])
        require(key not in table, "duplicate_original_context")
        table[key] = natural_counts(row["counts"], 4)
    require(set(table) == set(CONTEXTS), "complete_original_context_coverage")
    return table


def exact_interval(value, domain=None):
    require(type(value) is list and len(value) == 2, "two_exact_interval_endpoints")
    low, high = map(rational, value)
    require(low <= high, "ordered_exact_interval")
    if domain is not None:
        require(domain[0] <= low <= high <= domain[1], "interval_outside_source_coordinate_domain")
    return low, high


def log_interval(record):
    require(type(record) is dict and set(record) == {"lower", "upper"} and
            all(type(value) is str for value in record.values()), "finite_log_interval_record")
    # Directed Decimal output is a rational string, including possible exponents.
    low, high = Fraction(record["lower"]), Fraction(record["upper"])
    require(low <= high, "ordered_log_interval")
    return low, high


def cross_logs(original, checked, threshold, outside):
    low, high = log_interval(original)
    require(type(checked) is dict, "integer_log_interval_record")
    if checked.get("infinite") is True:
        raise ValueError("finite_primary_log_at_zero_support")
    own_low, own_high = log_interval(checked)
    require(max(low, own_low) <= min(high, own_high), "independent_primary_log_intervals_disjoint")
    if outside:
        require(low >= threshold[1], "primary_profile_endpoint_below_threshold")
    else:
        require(high < threshold[0], "primary_MLE_not_inside_component_cut")


class FullProfile:
    """Global Jeffreys numerator divided by unconstrained likelihood maxima."""
    def __init__(self, rows, bits=240):
        self.counts = counts_table(rows)
        self.arithmetic = source.Arithmetic(bits)
        self.threshold = self.arithmetic.log(THRESHOLD)
        self.numerator_log = source.Bounds(0, 0)
        self.full_mle_likelihood_log = source.Bounds(0, 0)
        for key in CONTEXTS:
            counts = self.counts[key]
            # predictor_log is the previously signed four-outcome Dirichlet kernel.
            self.numerator_log += self.arithmetic.predictor_log(counts, 4)
            self.full_mle_likelihood_log += self.mle_likelihood(counts)
        self.mle_log = self.numerator_log - self.full_mle_likelihood_log

    def mle_likelihood(self, counts):
        total, result = sum(counts), source.Bounds(0, 0)
        for n in counts:
            if n:
                result += self.arithmetic.log(Fraction(n, total)).times(n)
        return result

    def parity_counts(self, context):
        context = binary_context(context)
        counts = self.counts[context]
        return counts[0] + counts[3], counts[1] + counts[2]

    def mle(self, context):
        even, odd = self.parity_counts(context)
        return Fraction(even, even + odd) if even + odd else Fraction(1, 2)

    def at(self, context, p):
        p = rational(p)
        require(0 <= p <= 1, "even_parity_probability")
        grouped = self.parity_counts(context)
        if (grouped[0] and p == 0) or (grouped[1] and p == 1):
            return None
        denominator = source.Bounds(0, 0)
        for n, probability in zip(grouped, (p, 1 - p)):
            if n:
                denominator += self.arithmetic.log(probability).times(n)
        return self.mle_log + self.mle_likelihood(grouped) - denominator

    def derivative_sign_numerator(self, context, p):
        p = rational(p)
        require(0 < p < 1, "interior_profile_derivative")
        even, odd = self.parity_counts(context)
        return (even + odd) * p - even

    def certify(self, context, interval):
        key = binary_context(context)
        low, high = exact_interval(interval, (Fraction(0), Fraction(1)))
        grouped = self.parity_counts(key)
        require(all(n > 0 for n in grouped), "two_sided_profile_requires_both_observed_parities")
        mle = self.mle(key)
        require(low < mle < high, "parity_interval_straddles_exact_MLE")
        center, left, right = self.at(key, mle), self.at(key, low), self.at(key, high)
        require(center is not None and center.hi < self.threshold.lo, "full_MLE_not_inside_component_cut")
        require(left is None or left.lo >= self.threshold.hi, "left_parity_endpoint_not_excluded")
        require(right is None or right.lo >= self.threshold.hi, "right_parity_endpoint_not_excluded")
        total = sum(grouped)
        require(total * low - grouped[0] < 0 and total * high - grouped[0] > 0,
                "entire_outside_profile_monotonicity")
        record = lambda value: {"infinite": True} if value is None else self.arithmetic.record(value)
        return {"h": key[0], "a": key[1], "b": key[2], "counts": list(self.counts[key]),
                "parity_counts": list(grouped), "p_mle": str(mle),
                "p_outer_interval": [str(low), str(high)],
                "correlation_outer_interval": [str(2 * low - 1), str(2 * high - 1)],
                "lower_endpoint_log_e": record(left), "upper_endpoint_log_e": record(right),
                "mle_log_e": record(center), "component_threshold": "80", "kind": KIND,
                "new_confidence_budget_spent": False, "point_witness_used_as_confidence_bound": False,
                "precision_bits": self.arithmetic.bits, "entire_outside_intervals_excluded": True,
                "profile_is_lower_bound_of_actual_full_component": True,
                "primary_endpoint_numerics_used": False}


@lru_cache(maxsize=8)
def cached_profile(signature, bits):
    rows = [{"h": key[0], "a": key[1], "b": key[2], "counts": list(counts)} for key, counts in signature]
    return FullProfile(rows, bits)


def verify_correlation_envelope(rows, context, entry, bits=240):
    table, key = counts_table(rows), binary_context(context)
    require(type(entry) is dict, "correlation_entry")
    require(binary_context([entry[name] for name in ("h", "a", "b")]) == key,
            "proposed_correlation_context_changed")
    require(natural_counts(entry["counts"], 4) == table[key], "correlation_counts_not_from_parent")
    expected_parity = (table[key][0] + table[key][3], table[key][1] + table[key][2])
    require(natural_counts(entry["parity_counts"], 2) == expected_parity, "proposed_parity_counts_changed")
    require(entry["component_threshold"] == "80" and entry["kind"] == KIND and
            entry["new_confidence_budget_spent"] is False and
            entry["point_witness_used_as_confidence_bound"] is False, "correlation_projection_scope_changed")
    signature = tuple((key, table[key]) for key in CONTEXTS)
    profile = cached_profile(signature, bits)
    checked = profile.certify(key, entry["p_outer_interval"])
    require(entry["p_mle"] == checked["p_mle"] and
            exact_interval(entry["correlation_outer_interval"], (Fraction(-1), Fraction(1))) ==
            tuple(map(rational, checked["correlation_outer_interval"])), "correlation_exact_coordinate_changed")
    threshold = tuple(Fraction(value, profile.arithmetic.scale) for value in (profile.threshold.lo, profile.threshold.hi))
    for field in ("lower_endpoint_log_e", "upper_endpoint_log_e", "mle_log_e"):
        cross_logs(entry[field], checked[field], threshold, field != "mle_log_e")
    checked["primary_log_intervals_crossed"] = True
    return checked


def response_envelopes(rows, correlations, biases):
    table = counts_table(rows)
    require(type(correlations) is list and len(correlations) == 8 and
            type(biases) is list and len(biases) == 4, "complete_correlation_and_bias_projections")
    correlation, bias = {}, {}
    for row in correlations:
        require(type(row) is dict, "correlation_projection_row")
        key = binary_context([row[name] for name in ("h", "a", "b")])
        require(key not in correlation and natural_counts(row["counts"], 4) == table[key],
                "response_correlation_inventory_or_parent_counts")
        correlation[key] = exact_interval(row["correlation_outer_interval"], (Fraction(-1), Fraction(1)))
    for row in biases:
        require(type(row) is dict and row["side"] in ("alice", "bob") and
                type(row["setting"]) is int and row["setting"] in (0, 1), "original_bias_role")
        key = row["side"], row["setting"]
        require(key not in bias, "duplicate_own_setting_bias")
        bias[key] = exact_interval(row["mu_outer_interval"], (Fraction(-1), Fraction(1)))
    require(set(correlation) == set(CONTEXTS) and set(bias) == set(ROLES), "whole_projection_coverage")
    results = []
    for side, setting in ROLES:
        contributions = []
        for key in CONTEXTS:
            if (key[1] if side == "alice" else key[2]) != setting:
                continue
            corners = [a * b for a in bias["alice", key[1]] for b in bias["bob", key[2]]]
            product_low, product_high = min(corners), max(corners)
            corr_low, corr_high = correlation[key]
            centered_low, centered_high = corr_low - product_high, corr_high - product_low
            if centered_low > 0:
                distance = centered_low
            elif centered_high < 0:
                distance = -centered_high
            else:
                distance = Fraction(0)
            contributions.append({"context": list(key), "bias_product_outer_interval": list(map(str, (product_low, product_high))),
                                  "centered_correlation_outer_interval": list(map(str, (centered_low, centered_high))),
                                  "gain_lower": str(distance)})
        require(len(contributions) == 4, "all_herald_remote_contexts_for_own_setting")
        gain_lower = max(rational(row["gain_lower"]) for row in contributions)
        mu_low, mu_high = bias[side, setting]
        minimum_bias_magnitude = mu_low if mu_low > 0 else -mu_high if mu_high < 0 else Fraction(0)
        gain_upper = 1 - minimum_bias_magnitude
        require(0 <= gain_lower <= gain_upper, "response_intersection_conflicts_with_source_cone")
        error_zero = (max(Fraction(0), -mu_high), (1 - gain_lower - mu_low) / 2)
        error_one = (max(Fraction(0), mu_low), (1 - gain_lower + mu_high) / 2)
        require(0 <= error_zero[0] <= error_zero[1] <= 1 and
                0 <= error_one[0] <= error_one[1] <= 1, "canonical_error_interval_legal")
        results.append({"side": side, "setting": setting, "canonical_gain": list(map(str, (gain_lower, gain_upper))),
                        "canonical_e0": list(map(str, error_zero)), "canonical_e1": list(map(str, error_one)),
                        "bias_outer_interval": list(map(str, (mu_low, mu_high))), "source_contributions": contributions,
                        "kind": KIND, "fixed_law_point_used_as_confidence_bound": False,
                        "actual_ideal_label_identity_selected": False})
    return results


def verify_report(primary, counts, biases):
    require(type(primary) is dict and primary.get("schema") == PRIMARY_SCHEMA and primary.get("version") == VERSION and
            primary.get("status") == "generated_parent_confidence_response_envelopes", "response_projection_primary_identity")
    for key in ("whole_empirical_confidence_set_bounds", "simultaneous_necessary_outer_projections"):
        require(primary.get(key) is True, "whole_parent_CS_projection_scope_lost")
    for key in ("new_confidence_budget_spent", "fixed_law_point_used_as_confidence_bound",
                "hardware_parameter_uniqueness_certified", "optimizer_executed", "new_statistical_fit_executed"):
        require(primary.get(key) is False, "response_projection_scope_promoted")
    require(primary.get("parent_confidence_budget") == "1/20" and primary.get("full_component_threshold") == "80" and
            type(primary.get("trial_event_files_read")) is int and primary["trial_event_files_read"] == 0,
            "response_projection_budget_threshold_or_event_access_changed")
    require(type(counts) is dict and counts.get("schema") == "stage10-munich-readout-primary-point/v1" and
            counts.get("version") == "stage10-munich-readout-rd0001", "original_parent_count_receipt_identity")
    require(type(biases) is dict and biases.get("schema") == "stage10-munich-readout-identification-primary/v1" and
            biases.get("version") == "stage10-munich-readout-id0001", "original_parent_bias_receipt_identity")
    for report in (primary, counts, biases):
        require(type(report.get("runs")) is list and
                all(type(row) is dict for row in report["runs"]) and
                tuple(row.get("run") for row in report["runs"]) == source.RUNS, "complete_ordered_original_two_runs")
    results = []
    for supplied, counted, biased in zip(primary["runs"], counts["runs"], biases["runs"]):
        rows = counted["four_outcomes"]
        table = counts_table(rows)
        total = sum(sum(value) for value in table.values())
        require(type(counted["trials"]) is int and counted["trials"] == total and
                type(supplied["parent_trials"]) is int and supplied["parent_trials"] == total,
                "original_parent_trial_denominator_changed")
        factor = counted["prefix_check"]["factor_sequence_sha256"]
        require(type(factor) is str and len(factor) == 64 and all(c in "0123456789abcdef" for c in factor) and
                supplied["parent_factor_sequence_sha256"] == factor, "original_parent_factor_identity_changed")
        require(source.canonical(supplied["bias_envelopes"]) == source.canonical(biased["bias_envelopes"]),
                "copied_parent_bias_envelopes_changed")
        proposed = supplied["correlation_envelopes"]
        require(type(proposed) is list and len(proposed) == 8, "complete_eight_correlation_envelopes")
        checked_correlations = []
        for entry, key in zip(proposed, CONTEXTS):
            failure = None
            for bits in (240, 320, 384):
                try:
                    checked = verify_correlation_envelope(rows, key, entry, bits)
                    break
                except ValueError as error:
                    failure = error
            else:
                raise failure
            checked_correlations.append(checked)
        responses = response_envelopes(rows, checked_correlations, biased["bias_envelopes"])
        require(source.canonical(supplied["response_envelopes"]) == source.canonical(responses),
                "whole_parent_CS_response_transport_changed")
        results.append({"run": counted["run"], "correlation_envelopes": checked_correlations,
                        "response_envelopes": responses, "parent_trials": total,
                        "parent_factor_sequence_sha256": factor})
    return {"schema": SCHEMA, "version": VERSION, "status": "certified_parent_confidence_response_envelopes",
            "evidence_valid": True, "runs": results, "correlation_envelopes_checked": 16,
            "correlation_endpoints_checked": 32, "response_envelopes_checked": 8,
            "whole_empirical_confidence_set_bounds": True, "simultaneous_necessary_outer_projections": True,
            "parent_confidence_budget": "1/20", "new_confidence_budget_spent": False,
            "fixed_law_point_used_as_confidence_bound": False, "hardware_parameter_uniqueness_certified": False,
            "source_optimizer_executed": False, "optimizer_executed": False, "new_statistical_fit_executed": False,
            "trial_event_files_read": 0, "primary_endpoint_numerics_used": False,
            "full_component_threshold": "80", "source_theorem_changed": False, "controller_advance": False}


def frozen_bindings(commit):
    bindings = []
    for path in [*(BASE / name for name in (*FILES, *INPUTS)), MODULE]:
        raw = source.frozen_bytes(path, commit)
        require(raw == source.frozen_bytes(path), "response_projection_not_at_execution_HEAD")
        bindings.append({"path": str(path.relative_to(ROOT)), "sha256": source.digest(raw)})
    return bindings


def primary_provenance(primary, bindings, provenance):
    inventory = {row["path"]: row for row in bindings}
    expected = [inventory[str((BASE / name).relative_to(ROOT))] for name in (*FILES, *INPUTS)]
    expected.append(inventory[str(MODULE.relative_to(ROOT))])
    require(source.canonical(primary["source_bindings"]) == source.canonical(expected), "primary_scientific_bindings_changed")
    require(primary["freeze_commit"] == provenance["freeze_commit"], "primary_response_freeze_changed")
    require(primary["kernel_sha256"] == inventory[str((BASE / "response-bounds-certification-first.json").relative_to(ROOT))]["sha256"] and
            primary["parent_identification_sha256"] == inventory[str((BASE / "identification-verification.json").relative_to(ROOT))]["sha256"],
            "source_kernel_or_parent_confidence_certificate_changed")
    attempt_raw = source.frozen_bytes(BASE / "response-projection-attempt.json")
    require(primary["attempt_sha256"] == source.digest(attempt_raw), "primary_response_first_attempt_changed")
    attempt = source.strict_json(attempt_raw)
    require(attempt["version"] == VERSION and attempt["freeze_commit"] == primary["freeze_commit"] and
            attempt["execution_head"] == primary["execution_head"] and
            source.canonical(attempt["source_bindings"]) == source.canonical(primary["source_bindings"]) and
            type(attempt["event_files_read_at_reservation"]) is int and attempt["event_files_read_at_reservation"] == 0,
            "primary_response_attempt_provenance_changed")
    for older, newer in ((primary["freeze_commit"], primary["execution_head"]),
                         (primary["execution_head"], provenance["execution_head"])):
        ancestry = source.subprocess.run(["git", "merge-base", "--is-ancestor", older, newer], cwd=ROOT,
                                         capture_output=True, check=False)
        require(ancestry.returncode == 0, "primary_science_not_frozen_before_execution")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    parser.add_argument("--primary-receipt", type=Path, default=BASE / "response-projection-first.json")
    args = parser.parse_args()
    attempt, first = BASE / "response-projection-independent-attempt.json", BASE / "response-projection-independent-first.json"
    try:
        require(not attempt.exists() and not first.exists(), "response_projection_independent_first_already_reserved")
        provenance = source.execution_provenance(args.freeze_commit)
        bindings = frozen_bindings(provenance["freeze_commit"])
        primary_raw = source.frozen_bytes(BASE / "response-projection-first.json")
        require(args.primary_receipt.read_bytes() == primary_raw, "response_projection_override_changes_primary_receipt")
        counts_raw = source.frozen_bytes(BASE / "primary-first-c0002.json")
        biases_raw = source.frozen_bytes(BASE / "identification-first.json")
        source.exclusive_json(attempt, {"schema": "stage10-munich-response-projection-independent-attempt/v1",
                                       "version": VERSION, "provenance": provenance, "source_bindings": bindings,
                                       "primary_receipt_sha256": source.digest(primary_raw), "trial_event_files_read": 0})
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(source.canonical({"schema": SCHEMA, "status": "not_started", "reason": str(error)}))
        return 2
    try:
        # The original dual-first consumer pays the reused arithmetic/source closure.
        import verify as parent
        require(parent.consume()["evidence_valid"] is True, "original_parent_source_or_joint_certificate_changed")
        primary = source.strict_json(primary_raw)
        primary_provenance(primary, bindings, provenance)
        report = verify_report(primary, source.strict_json(counts_raw), source.strict_json(biases_raw))
    except Exception as error:
        report = {"schema": SCHEMA, "version": VERSION, "status": "execution_failed", "evidence_valid": False,
                  "reason": str(error), "error_type": type(error).__name__}
    report.update({"source_bindings": bindings, "provenance": provenance,
                   "primary_receipt_sha256": source.digest(primary_raw), "parent_counts_sha256": source.digest(counts_raw),
                   "parent_biases_sha256": source.digest(biases_raw), "attempt_sha256": source.digest(attempt.read_bytes())})
    source.exclusive_json(first, report)
    print(source.canonical({"schema": SCHEMA, "status": report["status"], "evidence_valid": report["evidence_valid"]}))
    return 0 if report["evidence_valid"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
