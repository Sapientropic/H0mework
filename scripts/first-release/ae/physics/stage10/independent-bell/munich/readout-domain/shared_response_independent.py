"""Independent integer checker for a response shared by four source contexts.

The signed cp0001 full numerator and integer arithmetic are reused.  This
checker constructs its own parity caps and likelihood maxima; it imports no
cp0002 producer and neither searches a boundary nor reads event files.
"""
import argparse
from fractions import Fraction
from pathlib import Path

import response_projection_independent as projection


source = projection.source
require, rational = source.require, source.rational
CONTEXTS, ROLES = projection.CONTEXTS, projection.ROLES
BRACKET = Fraction(1, 1 << 36)
VERSION = "stage10-munich-readout-cp0002"
BASE, ROOT = projection.BASE, projection.ROOT
PRIMARY_SCHEMA = "stage10-munich-shared-response-primary/v1"
SCHEMA = "stage10-munich-shared-response-independent/v1"
FILES = ("criterion-cp0002.md", "shared_response.py", "test_shared_response.py", "shared_response_run.py",
         "shared_response_independent.py", "test_shared_response_independent.py",
         "shared-response-audit.md", "shared-response-audit.json")
INPUTS = ("primary-first-c0002.json", "identification-first.json", "response-projection-first.json",
          "response-projection-verification.json", "response-bounds-certification-first.json",
          "response_projection.py", "response_projection_independent.py", "likelihood.py")
MODULE = ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutResponseBounds.lean"


def role(side, setting):
    require(side in ("alice", "bob") and type(setting) is int and setting in (0, 1), "original_own_setting_response_role")
    return side, setting


def bias_table(rows):
    require(type(rows) is list and len(rows) == 4, "all_four_original_bias_projections")
    result = {}
    for row in rows:
        require(type(row) is dict, "original_bias_projection_row")
        key = role(row["side"], row["setting"])
        require(key not in result, "duplicate_original_bias_projection")
        result[key] = projection.exact_interval(row["mu_outer_interval"], (Fraction(-1), Fraction(1)))
    require(set(result) == set(ROLES), "original_bias_role_coverage")
    return result


class SharedProfile:
    def __init__(self, rows, biases, side, setting, bits=240):
        self.side, self.setting = role(side, setting)
        table = projection.counts_table(rows)
        signature = tuple((key, table[key]) for key in CONTEXTS)
        self.full = projection.cached_profile(signature, bits)
        self.arithmetic = self.full.arithmetic
        self.biases = bias_table(biases)
        self.contexts = tuple(key for key in CONTEXTS if key[1 if side == "alice" else 2] == setting)
        require(len(self.contexts) == 4, "all_four_shared_source_contexts")
        self.inputs = {}
        for key in self.contexts:
            grouped = self.full.parity_counts(key)
            require(all(n > 0 for n in grouped), "both_parities_observed_in_shared_context")
            corners = [a * b for a in self.biases["alice", key[1]] for b in self.biases["bob", key[2]]]
            self.inputs[key] = grouped, min(corners), max(corners), self.full.mle(key), self.full.mle_likelihood(grouped)

    def parity_likelihood(self, counts, p):
        if (p == 0 and counts[0]) or (p == 1 and counts[1]):
            return None
        value = source.Bounds(0, 0)
        for n, probability in zip(counts, (p, 1 - p)):
            if n:
                value += self.arithmetic.log(probability).times(n)
        return value

    def at(self, gain):
        gain = rational(gain)
        require(0 <= gain <= 1, "legal_shared_response_cap")
        value, records, likelihoods = self.full.mle_log, [], []
        infinite = False
        for key in self.contexts:
            grouped, product_low, product_high, mle, mle_likelihood = self.inputs[key]
            allowed_low = max(Fraction(0), (1 + product_low - gain) / 2)
            allowed_high = min(Fraction(1), (1 + product_high + gain) / 2)
            require(allowed_low <= allowed_high, "nonempty_shared_parity_domain")
            if mle < allowed_low:
                maximizing = allowed_low
            elif mle > allowed_high:
                maximizing = allowed_high
            else:
                maximizing = mle
            # The binary log likelihood is concave; its derivative changes sign at the exact MLE.
            derivative = grouped[0] - sum(grouped) * maximizing
            require((maximizing == mle and derivative == 0) or
                    (maximizing == allowed_low and derivative <= 0) or
                    (maximizing == allowed_high and derivative >= 0), "clipped_probability_not_likelihood_maximum")
            likelihood = self.parity_likelihood(grouped, maximizing)
            records.append({"context": list(key), "parity_counts": list(grouped),
                            "bias_product_outer_interval": list(map(str, (product_low, product_high))),
                            "allowed_even_probability": list(map(str, (allowed_low, allowed_high))),
                            "parity_mle": str(mle), "maximizing_even_probability": str(maximizing)})
            likelihoods.append({"context": list(key), "parity_MLE_log_likelihood": self.arithmetic.record(mle_likelihood),
                                "clipped_parity_log_likelihood": {"negative_infinite": True} if likelihood is None
                                else self.arithmetic.record(likelihood)})
            if likelihood is None:
                infinite = True
            elif maximizing != mle:
                value += mle_likelihood - likelihood
        return {"log_e": {"infinite": True} if infinite else self.arithmetic.record(value),
                "contexts": records, "context_likelihoods": likelihoods, "interval": None if infinite else value}


def cross_endpoint(profile, proposed, checked, outside):
    require(type(proposed) is dict and set(proposed) == {"log_e", "contexts"}, "shared_profile_endpoint_record")
    require(source.canonical(proposed["contexts"]) == source.canonical(checked["contexts"]),
            "shared_source_context_or_clipped_MLE_changed")
    value = checked["interval"]
    if value is None:
        require(outside and type(proposed["log_e"]) is dict and set(proposed["log_e"]) == {"infinite"} and
                proposed["log_e"]["infinite"] is True, "shared_zero_support_profile_changed")
        return
    threshold = profile.full.threshold
    require(value.lo >= threshold.hi if outside else value.hi < threshold.lo,
            "shared_response_profile_not_on_declared_threshold_side")
    projected_threshold = tuple(Fraction(v, profile.arithmetic.scale) for v in (threshold.lo, threshold.hi))
    projection.cross_logs(proposed["log_e"], checked["log_e"], projected_threshold, outside)


def verify_bound(rows, biases, side, setting, entry, legacy_entry, bits=240):
    profile = SharedProfile(rows, biases, side, setting, bits)
    require(type(entry) is dict and role(entry["side"], entry["setting"]) == (side, setting), "shared_response_bound_role_changed")
    for name in ("all_four_contexts_share_one_source_response", "entire_low_response_interval_excluded",
                 "whole_empirical_confidence_set_bounds"):
        require(entry[name] is True, "shared_response_scope_lost")
    for name in ("actual_gain_extremum_sharpness_claimed", "new_confidence_budget_spent", "actual_ideal_label_identity_selected"):
        require(entry[name] is False, "shared_response_scope_promoted")
    require(entry["component_threshold"] == "80", "shared_full_component_threshold_changed")
    low, high = projection.exact_interval(entry["shared_profile_threshold_bracket"], (Fraction(0), Fraction(1)))
    require(low < high and high - low <= BRACKET and entry["threshold_bracket_gap"] == str(high - low),
            "shared_profile_boundary_bracket_changed")
    left, right = profile.at(low), profile.at(high)
    cross_endpoint(profile, entry["profile_lower_endpoint"], left, True)
    cross_endpoint(profile, entry["profile_upper_endpoint"], right, False)
    require(type(legacy_entry) is dict and role(legacy_entry["side"], legacy_entry["setting"]) == (side, setting) and
            legacy_entry["kind"] == projection.KIND and legacy_entry["fixed_law_point_used_as_confidence_bound"] is False and
            legacy_entry["actual_ideal_label_identity_selected"] is False, "original_cp0001_response_role_or_scope_changed")
    old_gain = projection.exact_interval(legacy_entry["canonical_gain"], (Fraction(0), Fraction(1)))
    mu_low, mu_high = profile.biases[side, setting]
    require(projection.exact_interval(legacy_entry["bias_outer_interval"], (Fraction(-1), Fraction(1))) == (mu_low, mu_high),
            "shared_response_parent_bias_identity_changed")
    gain = max(low, old_gain[0])
    minimum_bias = mu_low if mu_low > 0 else -mu_high if mu_high < 0 else Fraction(0)
    upper = 1 - minimum_bias
    require(0 <= gain <= upper, "shared_response_cut_conflicts_with_source_cone")
    response = {"canonical_gain": [str(gain), str(upper)],
                "canonical_e0": [str(max(Fraction(0), -mu_high)), str((1 - gain - mu_low) / 2)],
                "canonical_e1": [str(max(Fraction(0), mu_low)), str((1 - gain + mu_high) / 2)]}
    for field, interval in response.items():
        require(source.canonical(entry[field]) == source.canonical(interval), "shared_canonical_response_transport_changed")
        old_low, old_high = projection.exact_interval(legacy_entry[field], (Fraction(0), Fraction(1)))
        new_low, new_high = map(rational, interval)
        require(old_low <= new_low <= new_high <= old_high, "shared_response_is_weaker_than_cp0001")
    require(entry["bias_outer_interval"] == list(map(str, (mu_low, mu_high))) and
            entry["legacy_gain_lower"] == str(old_gain[0]) and
            entry["strictly_improved_gain_lower"] is (gain > old_gain[0]), "shared_gain_or_bias_exact_fields_changed")
    # Increasing G expands all four allowed parity intervals, so their maxima cannot decrease.
    return {"side": side, "setting": setting,
            "shared_profile_threshold_bracket": [str(low), str(high)], "threshold_bracket_gap": str(high - low),
            "profile_lower_endpoint": {key: left[key] for key in ("log_e", "contexts")},
            "profile_upper_endpoint": {key: right[key] for key in ("log_e", "contexts")},
            "lower_context_likelihoods": left["context_likelihoods"], "upper_context_likelihoods": right["context_likelihoods"],
            **response, "bias_outer_interval": list(map(str, (mu_low, mu_high))), "legacy_gain_lower": str(old_gain[0]),
            "strictly_improved_gain_lower": gain > old_gain[0], "component_threshold": "80",
            "all_four_contexts_share_one_source_response": True, "entire_low_response_interval_excluded": True,
            "whole_empirical_confidence_set_bounds": True, "actual_gain_extremum_sharpness_claimed": False,
            "new_confidence_budget_spent": False, "actual_ideal_label_identity_selected": False,
            "all_allowed_probability_domains_nested": True, "all_four_likelihood_maxima_checked": True,
            "shared_profile_is_lower_bound_of_actual_full_component": True,
            "primary_endpoint_numerics_used": False, "boundary_search_executed": False,
            "cp0001_response_envelopes_preserved_or_tightened": True, "precision_bits": profile.arithmetic.bits}


def verify_report(primary, counts, biases, legacy):
    require(type(primary) is dict and primary.get("schema") == PRIMARY_SCHEMA and primary.get("version") == VERSION and
            primary.get("status") == "generated_shared_response_parent_confidence_bounds", "shared_response_primary_identity")
    require(primary.get("shared_response_profile_certified") is True and
            primary.get("whole_empirical_confidence_set_bounds") is True and
            primary.get("parent_confidence_budget") == "1/20" and primary.get("full_component_threshold") == "80" and
            primary.get("profile_threshold_bracket_precision") == str(BRACKET), "shared_response_parent_contract_changed")
    for field in ("new_confidence_budget_spent", "fixed_law_point_used_as_confidence_bound",
                  "hardware_parameter_uniqueness_certified", "actual_gain_extremum_sharpness_claimed",
                  "source_theorem_changed", "optimizer_executed", "new_statistical_fit_executed"):
        require(primary.get(field) is False, "shared_response_scope_promoted")
    require(type(primary.get("trial_event_files_read")) is int and primary["trial_event_files_read"] == 0,
            "shared_response_event_access_changed")
    require(type(counts) is dict and counts.get("schema") == "stage10-munich-readout-primary-point/v1" and
            counts.get("version") == "stage10-munich-readout-rd0001", "original_parent_count_receipt_identity")
    require(type(biases) is dict and biases.get("schema") == "stage10-munich-readout-identification-primary/v1" and
            biases.get("version") == "stage10-munich-readout-id0001", "original_parent_bias_receipt_identity")
    require(type(legacy) is dict and legacy.get("schema") == projection.PRIMARY_SCHEMA and
            legacy.get("version") == projection.VERSION and
            legacy.get("status") == "generated_parent_confidence_response_envelopes", "original_cp0001_response_receipt_identity")
    for report in (primary, counts, biases, legacy):
        require(type(report.get("runs")) is list and all(type(row) is dict for row in report["runs"]) and
                tuple(row.get("run") for row in report["runs"]) == source.RUNS, "whole_original_ordered_two_run_family")
    results, improved = [], 0
    for supplied, counted, biased, previous in zip(primary["runs"], counts["runs"], biases["runs"], legacy["runs"]):
        table = projection.counts_table(counted["four_outcomes"])
        total = sum(map(sum, table.values()))
        require(type(counted["trials"]) is int and counted["trials"] == total and
                type(supplied["parent_trials"]) is int and supplied["parent_trials"] == total,
                "shared_response_original_trial_denominator_changed")
        factor = counted["prefix_check"]["factor_sequence_sha256"]
        require(type(factor) is str and len(factor) == 64 and all(c in "0123456789abcdef" for c in factor) and
                supplied["parent_factor_sequence_sha256"] == factor, "shared_response_original_factor_identity_changed")
        bias_table(biased["bias_envelopes"])
        entries, old_entries = supplied["shared_response_envelopes"], previous["response_envelopes"]
        require(type(entries) is list and len(entries) == 4 and type(old_entries) is list and len(old_entries) == 4,
                "complete_shared_and_original_own_setting_response_inventories")
        checked_entries = []
        for supplied_entry, old_entry, (side, setting) in zip(entries, old_entries, ROLES):
            failure = None
            for bits in (240, 320, 384):
                try:
                    checked = verify_bound(counted["four_outcomes"], biased["bias_envelopes"], side, setting,
                                           supplied_entry, old_entry, bits)
                    break
                except ValueError as error:
                    failure = error
            else:
                raise failure
            checked_entries.append(checked)
            improved += int(checked["strictly_improved_gain_lower"])
        results.append({"run": counted["run"], "shared_response_envelopes": checked_entries,
                        "parent_trials": total, "parent_factor_sequence_sha256": factor})
    require(type(primary["strictly_improved_gain_count"]) is int and primary["strictly_improved_gain_count"] == improved,
            "shared_response_improvement_count_changed")
    return {"schema": SCHEMA, "version": VERSION, "status": "certified_shared_response_parent_confidence_bounds",
            "evidence_valid": True, "runs": results, "shared_response_envelopes_checked": 8,
            "shared_response_endpoints_checked": 16, "context_likelihood_checks": 64,
            "strictly_improved_gain_count": improved, "old_cp0001_envelopes_preserved_or_tightened": True,
            "profile_threshold_bracket_precision": str(BRACKET), "shared_response_profile_certified": True,
            "whole_empirical_confidence_set_bounds": True, "parent_confidence_budget": "1/20",
            "new_confidence_budget_spent": False, "fixed_law_point_used_as_confidence_bound": False,
            "hardware_parameter_uniqueness_certified": False, "actual_gain_extremum_sharpness_claimed": False,
            "source_theorem_changed": False, "controller_advance": False, "trial_event_files_read": 0,
            "optimizer_executed": False, "source_optimizer_executed": False, "new_statistical_fit_executed": False,
            "boundary_search_executed": False, "primary_endpoint_numerics_used": False, "full_component_threshold": "80"}


def frozen_bindings(commit):
    entries = []
    for path in [*(BASE / name for name in (*FILES, *INPUTS)), MODULE]:
        raw = source.frozen_bytes(path, commit)
        require(raw == source.frozen_bytes(path), "shared_response_science_not_at_execution_HEAD")
        entries.append({"path": str(path.relative_to(ROOT)), "sha256": source.digest(raw)})
    return entries


def source_review():
    audit = source.strict_json(source.frozen_bytes(BASE / "shared-response-audit.json"))
    require(audit.get("schema") == "stage10-munich-readout-shared-response-audit/v1" and
            audit.get("version") == VERSION and audit.get("status") == "accepted_shared_response_source_and_statistical_logic" and
            audit.get("evidence_valid") is True and audit.get("substantive_defects") == [], "shared_response_source_audit_rejected")
    contract = audit["confidence_contract"]
    require(contract["parent_confidence_budget"] == "1/20" and contract["new_confidence_budget_spent"] is False and
            contract["full_component_threshold"] == "80" and contract["full_component_weight"] == "1/2" and
            contract["parent_threshold"] == "40", "shared_response_audited_confidence_contract_changed")
    entries = audit["source_bindings"]
    require(type(entries) is list and len(entries) == 11, "shared_response_audit_source_inventory_changed")
    seen = set()
    for entry in entries:
        require(type(entry) is dict and set(entry) == {"path", "sha256"} and type(entry["path"]) is str,
                "shared_response_audit_source_entry")
        relative = Path(entry["path"])
        require(not relative.is_absolute() and not {".", ".."}.intersection(relative.parts) and entry["path"] not in seen,
                "shared_response_audit_source_identity")
        seen.add(entry["path"])
        require(source.digest(source.frozen_bytes(ROOT / relative)) == entry["sha256"], "shared_response_audited_source_changed")
    return audit


def primary_provenance(primary, bindings, provenance):
    require(source.canonical(primary["source_bindings"]) == source.canonical(bindings), "shared_primary_scientific_bindings_changed")
    require(primary["freeze_commit"] == provenance["freeze_commit"], "shared_primary_scientific_freeze_changed")
    inventory = {row["path"]: row["sha256"] for row in bindings}
    for field, name in (("source_kernel_sha256", "response-bounds-certification-first.json"),
                        ("previous_response_certificate_sha256", "response-projection-verification.json")):
        require(primary[field] == inventory[str((BASE / name).relative_to(ROOT))], "shared_source_or_previous_certificate_changed")
    raw = source.frozen_bytes(BASE / "shared-response-attempt.json")
    require(source.digest(raw) == primary["attempt_sha256"], "shared_primary_first_attempt_changed")
    attempt = source.strict_json(raw)
    require(attempt["version"] == VERSION and attempt["freeze_commit"] == primary["freeze_commit"] and
            attempt["execution_head"] == primary["execution_head"] and
            source.canonical(attempt["source_bindings"]) == source.canonical(bindings) and
            type(attempt["event_files_read_at_reservation"]) is int and attempt["event_files_read_at_reservation"] == 0,
            "shared_primary_attempt_provenance_or_event_access_changed")
    for older, newer in ((primary["freeze_commit"], primary["execution_head"]),
                         (primary["execution_head"], provenance["execution_head"])):
        result = source.subprocess.run(["git", "merge-base", "--is-ancestor", older, newer], cwd=ROOT,
                                       capture_output=True, check=False)
        require(result.returncode == 0, "shared_primary_source_not_frozen_before_science")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    parser.add_argument("--primary-receipt", type=Path, default=BASE / "shared-response-first.json")
    args = parser.parse_args()
    attempt, first = BASE / "shared-response-independent-attempt.json", BASE / "shared-response-independent-first.json"
    try:
        require(not attempt.exists() and not first.exists(), "shared_response_independent_first_already_reserved")
        provenance = source.execution_provenance(args.freeze_commit)
        bindings = frozen_bindings(provenance["freeze_commit"])
        primary_raw = source.frozen_bytes(BASE / "shared-response-first.json")
        require(args.primary_receipt.read_bytes() == primary_raw, "shared_response_override_changes_primary_receipt")
        count_raw = source.frozen_bytes(BASE / "primary-first-c0002.json")
        bias_raw = source.frozen_bytes(BASE / "identification-first.json")
        legacy_raw = source.frozen_bytes(BASE / "response-projection-first.json")
        source.exclusive_json(attempt, {"schema": "stage10-munich-shared-response-independent-attempt/v1", "version": VERSION,
                                       **provenance, "source_bindings": bindings, "primary_receipt_sha256": source.digest(primary_raw),
                                       "event_files_read_at_reservation": 0})
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(source.canonical({"schema": SCHEMA, "status": "not_started", "reason": str(error)}))
        return 2
    try:
        import response_projection_verify as previous
        require(previous.consume()["evidence_valid"] is True, "original_parent_source_and_cp0001_response_changed")
        source_review()
        primary = source.strict_json(primary_raw)
        primary_provenance(primary, bindings, provenance)
        report = verify_report(primary, source.strict_json(count_raw), source.strict_json(bias_raw), source.strict_json(legacy_raw))
    except Exception as error:
        report = {"schema": SCHEMA, "version": VERSION, "status": "execution_failed", "evidence_valid": False,
                  "reason": str(error), "error_type": type(error).__name__}
    inventory = {row["path"]: row["sha256"] for row in bindings}
    report.update({**provenance, "source_bindings": bindings, "primary_receipt_sha256": source.digest(primary_raw),
                   "source_kernel_sha256": inventory[str((BASE / "response-bounds-certification-first.json").relative_to(ROOT))],
                   "previous_response_certificate_sha256": inventory[str((BASE / "response-projection-verification.json").relative_to(ROOT))],
                   "parent_counts_sha256": source.digest(count_raw), "parent_biases_sha256": source.digest(bias_raw),
                   "previous_response_first_sha256": source.digest(legacy_raw), "attempt_sha256": source.digest(attempt.read_bytes())})
    source.exclusive_json(first, report)
    print(source.canonical({"schema": SCHEMA, "status": report["status"], "evidence_valid": report["evidence_valid"],
                            "strictly_improved_gain_count": report.get("strictly_improved_gain_count")}))
    return 0 if report["evidence_valid"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
