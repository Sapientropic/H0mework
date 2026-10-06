"""Synthetic controls for the four-context cap; no new primary imports or data."""
from decimal import Decimal, localcontext
from fractions import Fraction
import copy
from pathlib import Path
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import shared_response_independent as checker


LOW = Fraction(8254341995, 17179869184)
HIGH = Fraction(33017367981, 68719476736)


def rows(counts=(90, 10, 10, 90)):
    return [{"h": h, "a": a, "b": b, "counts": list(counts)} for h, a, b in checker.CONTEXTS]


def biases(first=(Fraction(0), Fraction(0)), second=(Fraction(0), Fraction(0))):
    return [{"side": side, "setting": setting, "mu_outer_interval": list(map(str, first if side == "alice" else second))}
            for side, setting in checker.ROLES]


def sequential_predictor(counts):
    seen, total, result = [0] * 4, 0, Fraction(1)
    for event, number in enumerate(counts):
        for _ in range(number):
            result *= Fraction(2 * seen[event] + 1, 2 * total + 4)
            seen[event] += 1
            total += 1
    return result


def exact_shared_ratio(gain):
    # For the symmetric fixture all selected contexts have MLE9/10 and cap(1+G)/2.
    p = min(Fraction(9, 10), (1 + gain) / 2)
    selected_likelihood = (p / 2) ** 180 * ((1 - p) / 2) ** 20
    unrestricted_likelihood = Fraction(9, 20) ** 180 * Fraction(1, 20) ** 20
    numerator = sequential_predictor((90, 10, 10, 90)) ** 8
    return numerator / (selected_likelihood ** 4 * unrestricted_likelihood ** 4)


def legacy(side="alice", setting=0, lower=Fraction(0)):
    return {"side": side, "setting": setting, "canonical_gain": [str(lower), "1"],
            "canonical_e0": ["0", str((1 - lower) / 2)], "canonical_e1": ["0", str((1 - lower) / 2)],
            "bias_outer_interval": ["0", "0"], "kind": checker.projection.KIND,
            "fixed_law_point_used_as_confidence_bound": False, "actual_ideal_label_identity_selected": False}


def entry(side="alice", setting=0, old_lower=Fraction(0)):
    profile = checker.SharedProfile(rows(), biases(), side, setting)
    left, right = profile.at(LOW), profile.at(HIGH)
    lower = max(LOW, old_lower)
    return {"side": side, "setting": setting, "shared_profile_threshold_bracket": [str(LOW), str(HIGH)],
            "threshold_bracket_gap": str(HIGH - LOW),
            "profile_lower_endpoint": {key: left[key] for key in ("log_e", "contexts")},
            "profile_upper_endpoint": {key: right[key] for key in ("log_e", "contexts")},
            "component_threshold": "80", "canonical_gain": [str(lower), "1"],
            "canonical_e0": ["0", str((1 - lower) / 2)], "canonical_e1": ["0", str((1 - lower) / 2)],
            "bias_outer_interval": ["0", "0"], "legacy_gain_lower": str(old_lower),
            "strictly_improved_gain_lower": lower > old_lower,
            "all_four_contexts_share_one_source_response": True, "entire_low_response_interval_excluded": True,
            "whole_empirical_confidence_set_bounds": True, "actual_gain_extremum_sharpness_claimed": False,
            "new_confidence_budget_spent": False, "actual_ideal_label_identity_selected": False}


class SharedProfileControls(unittest.TestCase):
    def test_integer_four_context_profile_matches_sequential_exact_probability(self):
        profile = checker.SharedProfile(rows(), biases(), "alice", 0, bits=160)
        for gain in (Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(1)):
            value = profile.at(gain)["interval"]
            exact = exact_shared_ratio(gain)
            with localcontext() as context:
                context.prec = 100
                actual = (Decimal(exact.numerator) / Decimal(exact.denominator)).ln()
                self.assertLessEqual(Decimal(value.lo) / Decimal(profile.arithmetic.scale), actual)
                self.assertGreaterEqual(Decimal(value.hi) / Decimal(profile.arithmetic.scale), actual)

    def test_global_MLE_is_added_once_and_MLE_cap_has_zero_penalty(self):
        profile = checker.SharedProfile(rows(), biases(), "bob", 1, bits=160)
        self.assertEqual(profile.at(1)["interval"], profile.full.mle_log)
        self.assertTrue(all(row["maximizing_even_probability"] == "9/10" for row in profile.at(1)["contexts"]))

    def test_every_herald_and_remote_setting_is_retained_for_all_roles(self):
        for side, setting in checker.ROLES:
            profile = checker.SharedProfile(rows(), biases(), side, setting, bits=160)
            expected = [list(key) for key in checker.CONTEXTS if key[1 if side == "alice" else 2] == setting]
            self.assertEqual([row["context"] for row in profile.at(0)["contexts"]], expected)

    def test_four_signed_bias_corners_and_clamp_are_exact(self):
        profile = checker.SharedProfile(rows(), biases((Fraction(-1, 4), Fraction(-1, 10)),
                                                       (Fraction(1, 5), Fraction(1, 2))), "alice", 0, bits=160)
        first = profile.at(Fraction(1, 10))["contexts"][0]
        self.assertEqual(first["bias_product_outer_interval"], ["-1/8", "-1/50"])
        self.assertEqual(first["allowed_even_probability"], ["31/80", "27/50"])
        self.assertEqual(first["maximizing_even_probability"], "27/50")

    def test_nested_domains_pay_monotonic_profile_without_boundary_search(self):
        profile = checker.SharedProfile(rows(), biases(), "alice", 0, bits=160)
        records = [profile.at(gain) for gain in (Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(3, 4), Fraction(1))]
        for previous, following in zip(records, records[1:]):
            self.assertGreaterEqual(previous["interval"].lo, following["interval"].hi)
            for first, second in zip(previous["contexts"], following["contexts"]):
                p, q = map(Fraction, first["allowed_even_probability"]), map(Fraction, second["allowed_even_probability"])
                pl, ph = p; ql, qh = q
                self.assertLessEqual(ql, pl)
                self.assertGreaterEqual(qh, ph)

    def test_zero_support_is_infinite_and_keeps_all_four_trace_rows(self):
        profile = checker.SharedProfile(rows(), biases((Fraction(1), Fraction(1)),
                                                       (Fraction(1), Fraction(1))), "alice", 0, bits=160)
        answer = profile.at(0)
        self.assertIsNone(answer["interval"])
        self.assertEqual(answer["log_e"], {"infinite": True})
        self.assertEqual(len(answer["contexts"]), 4)
        self.assertTrue(all(row["clipped_parity_log_likelihood"] == {"negative_infinite": True}
                            for row in answer["context_likelihoods"]))

    def test_boolean_roles_counts_duplicate_bias_and_missing_parity_rejected(self):
        bad_bias = biases(); bad_bias[-1] = bad_bias[0]
        for original, bound, side, setting in ((rows(), biases(), "alice", False),
                                             (rows(), bad_bias, "alice", 0),
                                             (rows((1, 0, 0, 1)), biases(), "alice", 0)):
            with self.subTest(side=side, setting=setting), self.assertRaises(ValueError):
                checker.SharedProfile(original, bound, side, setting, bits=160)
        profile = checker.SharedProfile(rows(), biases(), "alice", 0, bits=160)
        for gain in (True, -1, 2):
            with self.assertRaises(ValueError):
                profile.at(gain)


class BoundControls(unittest.TestCase):
    def test_primary_proposed_synthetic_bracket_is_checked_without_IO_or_search(self):
        supplied, old = entry(), legacy()
        with patch.object(Path, "read_bytes", side_effect=AssertionError("receipt IO")):
            result = checker.verify_bound(rows(), biases(), "alice", 0, supplied, old)
        self.assertTrue(result["entire_low_response_interval_excluded"])
        self.assertFalse(result["boundary_search_executed"])
        self.assertFalse(result["actual_gain_extremum_sharpness_claimed"])
        self.assertEqual(Fraction(result["threshold_bracket_gap"]), Fraction(1, 1 << 36))
        self.assertGreater(Fraction(result["canonical_gain"][1]), HIGH)

    def test_original_stronger_lower_bound_is_preserved_by_max(self):
        old_lower = Fraction(1, 2)
        result = checker.verify_bound(rows(), biases(), "alice", 0, entry(old_lower=old_lower), legacy(lower=old_lower))
        self.assertEqual(result["canonical_gain"], ["1/2", "1"])
        self.assertEqual(result["canonical_e0"], ["0", "1/4"])
        self.assertFalse(result["strictly_improved_gain_lower"])

    def test_wrong_clip_log_scope_rate_or_wide_bracket_rejected(self):
        mutations = (lambda x: x["profile_lower_endpoint"]["contexts"][0].update(maximizing_even_probability="9/10"),
                     lambda x: x["profile_lower_endpoint"].update(log_e={"lower": "1000", "upper": "1001"}),
                     lambda x: x.update(whole_empirical_confidence_set_bounds=1),
                     lambda x: x.update(actual_gain_extremum_sharpness_claimed=True),
                     lambda x: x.update(component_threshold="40"),
                     lambda x: x.update(canonical_e0=["0", "1/10"]),
                     lambda x: x.update(shared_profile_threshold_bracket=["0", "1"], threshold_bracket_gap="1"))
        for change in mutations:
            supplied = copy.deepcopy(entry())
            change(supplied)
            with self.subTest(change=change), self.assertRaises(ValueError):
                checker.verify_bound(rows(), biases(), "alice", 0, supplied, legacy())


def synthetic_reports():
    primary = {"schema": checker.PRIMARY_SCHEMA, "version": checker.VERSION,
               "status": "generated_shared_response_parent_confidence_bounds",
               "profile_threshold_bracket_precision": str(checker.BRACKET), "shared_response_profile_certified": True,
               "whole_empirical_confidence_set_bounds": True, "parent_confidence_budget": "1/20",
               "new_confidence_budget_spent": False, "fixed_law_point_used_as_confidence_bound": False,
               "hardware_parameter_uniqueness_certified": False, "actual_gain_extremum_sharpness_claimed": False,
               "source_theorem_changed": False, "trial_event_files_read": 0, "optimizer_executed": False,
               "new_statistical_fit_executed": False, "full_component_threshold": "80",
               "strictly_improved_gain_count": 8, "runs": []}
    counts = {"schema": "stage10-munich-readout-primary-point/v1", "version": "stage10-munich-readout-rd0001", "runs": []}
    bias = {"schema": "stage10-munich-readout-identification-primary/v1", "version": "stage10-munich-readout-id0001", "runs": []}
    old = {"schema": checker.projection.PRIMARY_SCHEMA, "version": checker.projection.VERSION,
           "status": "generated_parent_confidence_response_envelopes", "runs": []}
    for index, run in enumerate(checker.source.RUNS):
        factor = ("01" if index == 0 else "02") * 32
        primary["runs"].append({"run": run, "shared_response_envelopes": [entry(side, setting) for side, setting in checker.ROLES],
                                "parent_trials": 1600, "parent_factor_sequence_sha256": factor})
        counts["runs"].append({"run": run, "four_outcomes": rows(), "trials": 1600,
                              "prefix_check": {"factor_sequence_sha256": factor}})
        bias["runs"].append({"run": run, "bias_envelopes": biases()})
        old["runs"].append({"run": run, "response_envelopes": [legacy(side, setting) for side, setting in checker.ROLES]})
    return primary, counts, bias, old


class ReportControls(unittest.TestCase):
    def test_two_runs_all_eight_bounds_and_64_context_likelihoods_without_IO(self):
        reports = synthetic_reports()
        with patch.object(Path, "read_bytes", side_effect=AssertionError("receipt IO")):
            result = checker.verify_report(*reports)
        self.assertTrue(result["evidence_valid"])
        self.assertEqual(result["shared_response_envelopes_checked"], 8)
        self.assertEqual(result["shared_response_endpoints_checked"], 16)
        self.assertEqual(result["context_likelihood_checks"], 64)
        self.assertEqual(result["strictly_improved_gain_count"], 8)
        self.assertFalse(result["boundary_search_executed"])

    def test_partial_run_and_boolean_or_promoted_metadata_rejected(self):
        for field, value in (("schema", "stage10-munich-shared-response-primary/v2"),
                             ("trial_event_files_read", False), ("whole_empirical_confidence_set_bounds", 1),
                             ("strictly_improved_gain_count", True), ("actual_gain_extremum_sharpness_claimed", True)):
            reports = synthetic_reports()
            reports[0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                checker.verify_report(*reports)
        reports = synthetic_reports(); reports[0]["runs"].pop()
        with self.assertRaises(ValueError):
            checker.verify_report(*reports)

    def test_swapped_role_changed_factor_count_or_legacy_response_rejected(self):
        mutations = (lambda p, c, b, o: p["runs"][0]["shared_response_envelopes"].reverse(),
                     lambda p, c, b, o: p["runs"][0].update(parent_trials=1599),
                     lambda p, c, b, o: p["runs"][0].update(parent_factor_sequence_sha256="ff" * 32),
                     lambda p, c, b, o: o["runs"][0]["response_envelopes"][0].update(canonical_gain=["1/2", "1"]),
                     lambda p, c, b, o: b["runs"][0]["bias_envelopes"][0].update(mu_outer_interval=["-1/10", "1/10"]))
        for change in mutations:
            reports = synthetic_reports(); change(*reports)
            with self.subTest(change=change), self.assertRaises(ValueError):
                checker.verify_report(*reports)

    def test_top_level_freeze_and_first_attempt_are_byte_bound(self):
        names = [str((checker.BASE / name).relative_to(checker.ROOT)) for name in (*checker.FILES, *checker.INPUTS)]
        names.append(str(checker.MODULE.relative_to(checker.ROOT)))
        bindings = [{"path": name, "sha256": f"{index:064x}"} for index, name in enumerate(names)]
        inventory = {item["path"]: item["sha256"] for item in bindings}
        primary = {"source_bindings": bindings, "freeze_commit": "frozen-cp2", "execution_head": "science-head",
                   "source_kernel_sha256": inventory[str((checker.BASE / "response-bounds-certification-first.json").relative_to(checker.ROOT))],
                   "previous_response_certificate_sha256": inventory[str((checker.BASE / "response-projection-verification.json").relative_to(checker.ROOT))]}
        attempt = {"version": checker.VERSION, "freeze_commit": "frozen-cp2", "execution_head": "science-head",
                   "source_bindings": bindings, "event_files_read_at_reservation": 0}
        raw = checker.source.canonical(attempt).encode()
        primary["attempt_sha256"] = checker.source.digest(raw)
        provenance = {"freeze_commit": "frozen-cp2", "execution_head": "intake-head"}
        with patch.object(checker.source, "frozen_bytes", return_value=raw), \
                patch.object(checker.source.subprocess, "run", return_value=SimpleNamespace(returncode=0)):
            checker.primary_provenance(primary, bindings, provenance)
            primary["attempt_sha256"] = "different-first"
            with self.assertRaises(ValueError):
                checker.primary_provenance(primary, bindings, provenance)
        with patch.object(checker.source, "frozen_bytes", side_effect=lambda path, commit="HEAD":
                          b"mutated-code" if commit == "HEAD" else b"frozen-code"):
            with self.assertRaises(ValueError):
                checker.frozen_bindings("frozen-cp2")

    def test_source_audit_contract_and_source_inventory_checked_without_primary_import(self):
        raw_source = b"fixed pure source"
        audit = {"schema": "stage10-munich-readout-shared-response-audit/v1", "version": checker.VERSION,
                 "status": "accepted_shared_response_source_and_statistical_logic", "evidence_valid": True,
                 "substantive_defects": [], "confidence_contract": {"parent_confidence_budget": "1/20",
                 "new_confidence_budget_spent": False, "full_component_threshold": "80",
                 "full_component_weight": "1/2", "parent_threshold": "40"},
                 "source_bindings": [{"path": f"Lean/pure_{i}.lean", "sha256": checker.source.digest(raw_source)}
                                     for i in range(11)]}
        def frozen(path, commit="HEAD"):
            return checker.source.canonical(audit).encode() if path.name == "shared-response-audit.json" else raw_source
        with patch.object(checker.source, "frozen_bytes", side_effect=frozen):
            self.assertTrue(checker.source_review()["evidence_valid"])
            audit["source_bindings"][0]["path"] = "../cache/event_archive.zip"
            with self.assertRaises(ValueError):
                checker.source_review()


if __name__ == "__main__":
    unittest.main()
