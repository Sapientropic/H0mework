"""Synthetic joint-product controls; no new producer imports or event inputs."""
from decimal import Decimal, localcontext
from fractions import Fraction
import copy
from pathlib import Path
import unittest
from unittest.mock import patch

import joint_response_independent as checker


BRACKETS = {"uniform": (Fraction(52735988039, 68719476736), Fraction(6591998505, 8589934592)),
            "alice": (Fraction(40470104933, 68719476736), Fraction(20235052467, 34359738368)),
            "bob": (Fraction(40470104933, 68719476736), Fraction(20235052467, 34359738368))}
OLD_LOWER = Fraction(8254341995, 17179869184)


def rows(counts=(90, 10, 10, 90)):
    return [{"h": h, "a": a, "b": b, "counts": list(counts)} for h, a, b in checker.CONTEXTS]


def biases(first=(Fraction(0), Fraction(0)), second=(Fraction(0), Fraction(0))):
    return [{"side": side, "setting": setting, "mu_outer_interval": list(map(str, first if side == "alice" else second))}
            for side, setting in checker.ROLES]


def primitive():
    return {side: [{"mu": "0", "u": "0", "z": "4/5" if side == "alice" else "-4/5"} for _ in (0, 1)]
            for side in ("alice", "bob")}


def shared_bounds():
    return [{"side": side, "setting": setting, "canonical_gain": [str(OLD_LOWER), "1"]} for side, setting in checker.ROLES]


def sequential_predictor():
    seen, total, result = [0] * 4, 0, Fraction(1)
    for event, n in enumerate((90, 10, 10, 90)):
        for _ in range(n):
            result *= Fraction(2 * seen[event] + 1, 2 * total + 4)
            seen[event] += 1; total += 1
    return result


def exact_ratio(caps):
    likelihood = Fraction(1)
    for _, a, b in checker.CONTEXTS:
        p = min(Fraction(9, 10), (1 + caps[a] * caps[2 + b]) / 2)
        likelihood *= (p / 2) ** 180 * ((1 - p) / 2) ** 20
    return sequential_predictor() ** 8 / likelihood


def endpoint(value):
    return {key: value[key] for key in ("log_e", "contexts")}


def ray_entry(profile, ray):
    low, high = BRACKETS[ray]
    lc, uc = checker.ray_caps(ray, low), checker.ray_caps(ray, high)
    return {"ray": ray, "profile_threshold_bracket": [str(low), str(high)], "threshold_bracket_gap": str(high - low),
            "lower_caps": list(map(str, lc)), "upper_caps": list(map(str, uc)),
            "profile_lower_endpoint": endpoint(profile.at(lc)), "profile_upper_endpoint": endpoint(profile.at(uc)),
            "component_threshold": "80", "entire_lower_orthant_excluded": True,
            "all_eight_contexts_used": True, "actual_gain_extremum_sharpness_claimed": False}


def control_entry(profile, name, proposed):
    value = profile.at(proposed)
    excluded = value["interval"] is None or value["interval"].lo >= profile.full.threshold.hi
    return {"name": name, "caps": list(map(str, proposed)),
            "status": "entire_lower_orthant_excluded" if excluded else "necessary_profile_not_excluded", **endpoint(value)}


class JointProfileControls(unittest.TestCase):
    def test_integer_eight_context_profile_matches_exact_sequential_probability(self):
        profile = checker.JointProfile(rows(), biases(), bits=160)
        for proposed in ((Fraction(1),) * 4, (Fraction(1, 2),) * 4,
                         (Fraction(3, 5), Fraction(7, 10), Fraction(4, 5), Fraction(9, 10))):
            value, exact = profile.at(proposed)["interval"], exact_ratio(proposed)
            with localcontext() as context:
                context.prec = 100
                actual = (Decimal(exact.numerator) / Decimal(exact.denominator)).ln()
                self.assertLessEqual(Decimal(value.lo) / Decimal(profile.arithmetic.scale), actual)
                self.assertGreaterEqual(Decimal(value.hi) / Decimal(profile.arithmetic.scale), actual)
        self.assertEqual(profile.at((1, 1, 1, 1))["interval"], profile.full.mle_log)

    def test_product_radius_and_signed_four_corner_bias_are_exact(self):
        profile = checker.JointProfile(rows(), biases((Fraction(-1, 4), Fraction(-1, 10)),
                                                     (Fraction(1, 5), Fraction(1, 2))), bits=160)
        record = profile.at((Fraction(1, 2), Fraction(1, 2), Fraction(1, 5), Fraction(1, 5)))["contexts"][0]
        self.assertEqual(record["gain_product_cap"], "1/10")
        self.assertEqual(record["bias_product_outer_interval"], ["-1/8", "-1/50"])
        self.assertEqual(record["allowed_even_probability"], ["31/80", "27/50"])
        self.assertEqual(record["maximizing_even_probability"], "27/50")

    def test_increasing_one_coordinate_expands_only_its_four_contexts(self):
        profile = checker.JointProfile(rows(), biases(), bits=160)
        first = profile.at((Fraction(2, 5), Fraction(1, 2), Fraction(3, 5), Fraction(3, 5)))
        second = profile.at((Fraction(4, 5), Fraction(1, 2), Fraction(3, 5), Fraction(3, 5)))
        self.assertGreater(first["interval"].lo, second["interval"].hi)
        for a, b in zip(first["contexts"], second["contexts"]):
            if a["context"][1] == 0:
                self.assertLess(Fraction(a["gain_product_cap"]), Fraction(b["gain_product_cap"]))
            else:
                self.assertEqual(a, b)

    def test_all_three_primary_proposed_brackets_are_checked_without_IO_or_search(self):
        profile = checker.JointProfile(rows(), biases())
        proposed = [ray_entry(profile, ray) for ray in checker.RAYS]
        with patch.object(Path, "read_bytes", side_effect=AssertionError("receipt IO")):
            result = [checker.verify_ray(profile, entry, ray) for entry, ray in zip(proposed, checker.RAYS)]
        self.assertTrue(all(row["entire_lower_orthant_excluded"] for row in result))
        self.assertTrue(all(not row["boundary_search_executed"] for row in result))

    def test_sqrt_caps_are_minimal_outward_dyadics_and_primitive_is_lawful(self):
        proposed, squares = checker.witness_caps(primitive())
        step = Fraction(1, 1 << 48)
        self.assertEqual(squares, ["16/25"] * 4)
        for upper in proposed:
            self.assertLess((upper - step) ** 2, Fraction(16, 25))
            self.assertGreaterEqual(upper ** 2, Fraction(16, 25))
        wrong = primitive(); wrong["alice"][0]["u"] = "1"
        with self.assertRaises(ValueError):
            checker.witness_caps(wrong)

    def test_positive_lawful_and_lookalike_controls_have_distinct_classifications(self):
        profile = checker.JointProfile(rows(), biases())
        lawful = checker.witness_caps(primitive())[0]
        lookalike = checker.individual_caps(shared_bounds())
        good = checker.verify_control(profile, control_entry(profile, "original_lawful_witness", lawful), "original_lawful_witness", lawful)
        bad = checker.verify_control(profile, control_entry(profile, "individual_projection_lookalike", lookalike),
                                     "individual_projection_lookalike", lookalike)
        self.assertEqual(good["status"], "necessary_profile_not_excluded")
        self.assertEqual(bad["status"], "entire_lower_orthant_excluded")
        self.assertTrue(all(Fraction(row["canonical_gain"][0]) <= lookalike[i] <= Fraction(row["canonical_gain"][1])
                            for i, row in enumerate(shared_bounds())))

    def test_zero_support_keeps_all_eight_contexts_and_uses_no_epsilon(self):
        profile = checker.JointProfile(rows(), biases((Fraction(1), Fraction(1)), (Fraction(1), Fraction(1))), bits=160)
        value = profile.at((0, 0, 0, 0))
        self.assertEqual(value["log_e"], {"infinite": True})
        self.assertIsNone(value["interval"])
        self.assertEqual(len(value["contexts"]), 8)

    def test_malformed_caps_contexts_ray_or_threshold_records_rejected(self):
        profile = checker.JointProfile(rows(), biases())
        for proposed in ((True, 1, 1, 1), (-1, 1, 1, 1), (1, 1, 1)):
            with self.assertRaises(ValueError): profile.at(proposed)
        for mutation in (lambda x: x.update(component_threshold="40"),
                         lambda x: x["profile_lower_endpoint"]["contexts"].pop(),
                         lambda x: x["profile_lower_endpoint"]["contexts"][0].update(gain_product_cap="1"),
                         lambda x: x.update(actual_gain_extremum_sharpness_claimed=True)):
            supplied = copy.deepcopy(ray_entry(profile, "uniform")); mutation(supplied)
            with self.assertRaises(ValueError): checker.verify_ray(profile, supplied, "uniform")


def reports():
    profile = checker.JointProfile(rows(), biases())
    rays = [ray_entry(profile, ray) for ray in checker.RAYS]
    controls = [control_entry(profile, "original_lawful_witness", checker.witness_caps(primitive())[0]),
                control_entry(profile, "individual_projection_lookalike", checker.individual_caps(shared_bounds()))]
    p = {"schema": checker.PRIMARY_SCHEMA, "version": checker.VERSION, "status": "generated_joint_response_parent_confidence_qualification",
         "joint_response_profile_certified": True, "whole_empirical_confidence_set_bounds": True,
         "parent_confidence_budget": "1/20", "full_component_threshold": "80", "profile_threshold_bracket_precision": str(checker.BRACKET),
         "trial_event_files_read": 0, "runs": []}
    for field in ("new_confidence_budget_spent", "fixed_law_point_used_as_confidence_bound", "hardware_parameter_uniqueness_certified",
                  "actual_ideal_label_identity_selected", "actual_gain_extremum_sharpness_claimed", "profile_pass_used_as_full_source_membership",
                  "source_theorem_changed", "optimizer_executed", "new_statistical_fit_executed"):
        p[field] = False
    c = {"schema": "stage10-munich-readout-primary-point/v1", "version": "stage10-munich-readout-rd0001", "runs": []}
    b = {"schema": "stage10-munich-readout-identification-primary/v1", "version": "stage10-munich-readout-id0001", "runs": []}
    s = {"schema": "stage10-munich-shared-response-primary/v1", "version": "stage10-munich-readout-cp0002", "runs": []}
    w = {"schema": "stage10-munich-readout-primitive-witness/v1", "version": "stage10-munich-readout-rd0001", "runs": []}
    for i, run in enumerate(checker.source.RUNS):
        factor = ("01" if i == 0 else "02") * 32
        p["runs"].append({"run": run, "joint_response_rays": copy.deepcopy(rays), "controls": copy.deepcopy(controls),
                          "parent_trials": 1600, "parent_factor_sequence_sha256": factor})
        c["runs"].append({"run": run, "four_outcomes": rows(), "trials": 1600, "prefix_check": {"factor_sequence_sha256": factor}})
        b["runs"].append({"run": run, "bias_envelopes": biases()})
        s["runs"].append({"run": run, "shared_response_envelopes": shared_bounds()})
        w["runs"].append({"run": run, "primitive": primitive()})
    return p, c, b, s, w


class ReportControls(unittest.TestCase):
    def test_whole_two_run_report_has_six_brackets_and_two_control_kinds(self):
        result = checker.verify_report(*reports())
        self.assertEqual(result["profile_brackets_checked"], 6)
        self.assertEqual(result["endpoints_checked"], 12)
        self.assertEqual(result["context_likelihood_checks"], 96)
        self.assertEqual(result["control_context_likelihood_checks"], 32)
        self.assertEqual(result["individual_projection_lookalikes_excluded"], 2)
        self.assertEqual(result["lawful_witness_controls_not_excluded"], 2)

    def test_partial_run_boolean_literal_or_source_membership_promotion_rejected(self):
        for field, value in (("trial_event_files_read", False), ("whole_empirical_confidence_set_bounds", 1),
                             ("profile_pass_used_as_full_source_membership", True), ("actual_ideal_label_identity_selected", True)):
            values = reports(); values[0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError): checker.verify_report(*values)
        values = reports(); values[0]["runs"].pop()
        with self.assertRaises(ValueError): checker.verify_report(*values)

    def test_control_caps_factor_or_primitive_identity_cannot_be_substituted(self):
        for mutation in (lambda v: v[0]["runs"][0].update(parent_factor_sequence_sha256="ff" * 32),
                         lambda v: v[0]["runs"][0]["controls"][1].update(caps=["1"] * 4),
                         lambda v: v[4]["runs"][0]["primitive"]["alice"][0].update(u="1"),
                         lambda v: v[0]["runs"][0]["joint_response_rays"].reverse()):
            values = reports(); mutation(values)
            with self.assertRaises(ValueError): checker.verify_report(*values)


if __name__ == "__main__":
    unittest.main()
