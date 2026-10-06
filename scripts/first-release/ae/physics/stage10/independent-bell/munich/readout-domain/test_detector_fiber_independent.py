"""Exact independent detector inverse and necessary-domain controls."""
from fractions import Fraction as Q
import inspect
from itertools import product
import copy
import unittest

import detector_fiber_independent as check


class DetectorFiberIndependentTests(unittest.TestCase):
    def confidence_fixture(self):
        roles = (("alice", 0), ("alice", 1), ("bob", 0), ("bob", 1))
        shared = {"run": "synthetic", "shared_response_envelopes": [
            {"side": side, "setting": setting, "canonical_gain": ["2/5", "1"]} for side, setting in roles]}
        bias = {"run": "synthetic", "bias_envelopes": [
            {"side": side, "setting": setting, "mu_outer_interval": [str(-bound), str(bound)]}
            for (side, setting), bound in zip(roles, (Q(1, 20), Q(1, 10), Q(1, 4), Q(1, 2)))]}
        joint = {"run": "synthetic", "joint_response_rays": [
            {"ray": ray, "profile_threshold_bracket": ["1/2", "3/4"], "entire_lower_orthant_excluded": True}
            for ray in ("uniform", "alice", "bob")]}
        return shared, bias, joint

    def test_inverse_recovers_entire_effect(self):
        atom = check.AtomicEffect(Q(1), Q(3, 10), Q(2, 5))
        effect = check.forward(atom, Q(1, 20), Q(9, 10))
        recovered = check.inverse(effect, Q(1, 20), Q(171, 200))
        self.assertEqual(recovered["atom"], atom)
        self.assertEqual(recovered["fragment_efficiency"], Q(9, 10))
        self.assertTrue(check.admits(effect, Q(1, 20), Q(171, 200)))

    def test_inverse_rejects_illegal_atomic_effect(self):
        point = check.Effect(Q(0), Q(3, 10), Q(2, 5))
        for d, k in ((Q(3, 4), Q(1, 4)), (Q(0), Q(1, 4)), (Q(0), Q(0))):
            self.assertFalse(check.admits(point, d, k))
            with self.assertRaises(ValueError):
                check.inverse(point, d, k)

    def test_zero_factor_complete_stratum(self):
        for background in (Q(0), Q(1, 3), Q(1)):
            scalar = check.Effect(1 - 2 * background, Q(0), Q(0))
            self.assertTrue(check.admits(scalar, background, Q(0)))
            self.assertFalse(check.admits(scalar, 1 - background, Q(0)))
        self.assertFalse(check.admits(check.Effect(Q(0), Q(1, 3), Q(0)), Q(1, 2), Q(0)))

    def test_multiple_detector_realizations_preserve_effect(self):
        point = check.Effect(Q(0), Q(3, 10), Q(2, 5))
        realizations = [check.inverse(point, d, k) for d, k in
                        ((Q(0), Q(1)), (Q(1, 10), Q(4, 5)), (Q(1, 4), Q(1, 2)))]
        for row in realizations:
            self.assertEqual(check.forward(row["atom"], row["background"], row["fragment_efficiency"]), point)
        self.assertEqual(len({row["atom"] for row in realizations}), 3)

    def test_product_bounds_hold_on_legal_fibres(self):
        checked = 0
        for radius, trace, background, eta in product((Q(1, 4), Q(1, 2), Q(3, 4)),
                                                     (Q(3, 4), Q(1), Q(5, 4)),
                                                     (Q(0), Q(1, 10), Q(1, 4)),
                                                     (Q(1, 2), Q(3, 4), Q(1))):
            if radius > min(trace, 2 - trace):
                continue
            atom = check.AtomicEffect(trace, radius * Q(3, 5), radius * Q(4, 5))
            point = check.forward(atom, background, eta)
            gain = (1 - background) * eta * radius
            bounds = check.necessary_bounds(gain, (point.mu, point.mu))
            h = Q(bounds["eta_times_lambda_max_lower"])
            maximum_eigenvalue = (trace + radius) / 2
            self.assertGreaterEqual(eta * maximum_eigenvalue, h)
            self.assertGreaterEqual(eta, h)
            self.assertGreaterEqual(maximum_eigenvalue, h)
            self.assertLessEqual(background, Q(bounds["dark_background_upper"]))
            exposure_squared = maximum_eigenvalue * Q(4, 7)
            self.assertGreaterEqual(eta * exposure_squared, Q(bounds["eta_times_area_squared_lower"]))
            self.assertGreaterEqual(check.hardware_gain_cap(eta, exposure_squared, abs(point.mu)), gain)
            checked += 1
        self.assertEqual(checked, 81)

    def test_sharp_detector_product_boundary(self):
        gain, mu = Q(2, 5), Q(1, 10)
        bounds = check.necessary_bounds(gain, (mu, mu))
        h = Q(bounds["eta_times_lambda_max_lower"])
        background = (1 - mu - gain) / 2
        eta = gain / (1 - background)
        atom = check.AtomicEffect(Q(1), Q(1), Q(0))
        point = check.forward(atom, background, eta)
        self.assertEqual(point.mu, mu)
        self.assertEqual(abs(point.u), gain)
        self.assertEqual(eta, h)

    def test_bounds_keep_unknown_polarity(self):
        first = check.necessary_bounds(Q(2, 5), (Q(-1, 10), Q(1, 20)))
        flipped = check.necessary_bounds(Q(2, 5), (Q(-1, 20), Q(1, 10)))
        for name in ("eta_lower", "lambda_max_lower", "eta_times_lambda_max_lower", "area_lower_squared"):
            self.assertEqual(first[name], flipped[name])
        self.assertFalse(first["click_polarity_selected"])

    def test_integer_sqrt_exact_floor(self):
        for value in (Q(0), Q(1), Q(2, 7), Q(4, 25)):
            lower = check.square_root_lower(value)
            self.assertLessEqual(lower ** 2, value)
            self.assertGreater((lower + Q(1, 1 << 80)) ** 2, value)

    def test_raw_cap_monotone_and_zero_controls(self):
        self.assertEqual(check.hardware_gain_cap(Q(0), Q(1), Q(1)), 0)
        self.assertEqual(check.hardware_gain_cap(Q(1), Q(0), Q(1)), 0)
        self.assertEqual(check.hardware_gain_cap(Q(1), Q(4, 7), Q(0)), 1)
        for eta, area, bias in product((Q(0), Q(1, 4), Q(3, 4)), (Q(0), Q(1, 10), Q(1, 2)),
                                      (Q(0), Q(1, 4), Q(3, 4))):
            lower = check.hardware_gain_cap(eta, area, bias)
            self.assertLessEqual(lower, check.hardware_gain_cap(eta + Q(1, 4), area, bias))
            self.assertLessEqual(lower, check.hardware_gain_cap(eta, area + Q(1, 4), bias))
            self.assertLessEqual(lower, check.hardware_gain_cap(eta, area, bias + Q(1, 4)))

    def test_raw_cap_rejects_insufficient_hardware_joint_box(self):
        g = Q(2, 5)
        caps = [check.hardware_gain_cap(Q(1, 2), Q(1, 7), Q(1, 10)),
                check.hardware_gain_cap(Q(1, 10), Q(1), Q(1, 10))]
        self.assertTrue(all(cap < g for cap in caps))

    def test_joint_group_uses_its_own_bias_bound(self):
        report = check.confidence_domain(*self.confidence_fixture())
        self.assertEqual(len(report["individual_hardware_constraints"]), 4)
        self.assertEqual(len(report["joint_hardware_constraints"]), 3)
        uniform, alice, bob = report["joint_hardware_constraints"]
        self.assertEqual(uniform["group_bias_absolute_upper"], "1/2")
        self.assertEqual(alice["group_bias_absolute_upper"], "1/10")
        self.assertEqual(bob["group_bias_absolute_upper"], "1/2")
        self.assertGreater(Q(alice["maximum_eta_times_lambda_max_strict_lower"]),
                           Q(uniform["maximum_eta_times_lambda_max_strict_lower"]))

    def test_confidence_source_identity_and_strictness(self):
        shared, bias, joint = self.confidence_fixture()
        cases = []
        wrong_run = copy.deepcopy(bias); wrong_run["run"] = "different"
        cases.append((shared, wrong_run, joint))
        wrong_order = copy.deepcopy(bias); wrong_order["bias_envelopes"].reverse()
        cases.append((shared, wrong_order, joint))
        nonstrict = copy.deepcopy(joint); nonstrict["joint_response_rays"][0]["entire_lower_orthant_excluded"] = 1
        cases.append((shared, bias, nonstrict))
        lost = copy.deepcopy(shared); lost["shared_response_envelopes"].pop()
        cases.append((lost, bias, joint))
        boolean = copy.deepcopy(shared); boolean["shared_response_envelopes"][0]["setting"] = False
        cases.append((boolean, bias, joint))
        for inputs in cases:
            with self.assertRaises(ValueError):
                check.confidence_domain(*inputs)

    def test_old_gain_cap_raw_hardware_pullback_is_exact(self):
        for old_cap, absolute in product((Q(0), Q(1, 10), Q(2, 5), Q(3, 4), Q(1)),
                                         (Q(0), Q(1, 20), Q(1, 4), Q(1))):
            exposure = Q(4, 7) * (2 * old_cap / (1 + absolute + old_cap))
            self.assertEqual(check.hardware_gain_cap(Q(1), exposure, absolute), old_cap)

    def test_no_readout_and_weak_response_excluded(self):
        for bright, dark in (((Q(0), Q(0)), (Q(0), Q(0))),
                             ((Q(1, 10), Q(1, 5)), (Q(1, 10), Q(1, 5)))):
            report = check.atomic_detector_polygons(Q(2, 5), (Q(-1, 10), Q(1, 10)), bright, dark)
            self.assertTrue(report["entire_atomic_response_box_excluded"])
            self.assertTrue(all(branch["vertices"] == [] for branch in report["branches"]))

    def test_high_response_polygon_nonempty_and_preserves_scope(self):
        report = check.atomic_detector_polygons(Q(2, 5), (Q(-1, 10), Q(1, 10)),
                                               (Q(9, 10), Q(19, 20)), (Q(1, 20), Q(1, 10)))
        self.assertFalse(report["entire_atomic_response_box_excluded"])
        self.assertFalse(report["click_polarity_selected"])
        self.assertTrue(report["necessary_projection_only"])
        for branch in report["branches"]:
            rows = [tuple(map(Q, row)) for row in branch["constraints"]]
            for d, k in (tuple(map(Q, vertex)) for vertex in branch["vertices"]):
                self.assertTrue(all(a * d + b * k <= c for a, b, c in rows))

    def test_degenerate_closed_segment_and_point_retained(self):
        segment = check.atomic_detector_polygons(Q(2, 5), (Q(0), Q(0)), (Q(1), Q(1)), (Q(0), Q(0)))
        for branch in segment["branches"]:
            self.assertEqual(branch["vertices"], [["0", "1"], ["3/10", "2/5"]])
        point = check.atomic_detector_polygons(Q(1), (Q(0), Q(0)), (Q(1), Q(1)), (Q(0), Q(0)))
        self.assertTrue(all(branch["vertices"] == [["0", "1"]] for branch in point["branches"]))

    def test_response_polarity_flip_swaps_branches(self):
        a = check.atomic_detector_polygons(Q(2, 5), (Q(-1, 5), Q(1, 10)),
                                          (Q(4, 5), Q(9, 10)), (Q(1, 10), Q(1, 5)))
        b = check.atomic_detector_polygons(Q(2, 5), (Q(-1, 10), Q(1, 5)),
                                          (Q(4, 5), Q(9, 10)), (Q(1, 10), Q(1, 5)))
        self.assertEqual(a["branches"][0]["vertices"], b["branches"][1]["vertices"])
        self.assertEqual(a["branches"][1]["vertices"], b["branches"][0]["vertices"])

    def test_unphysical_bounds_and_response_box_rejected(self):
        for gain, bias in ((Q(0), (Q(0), Q(0))), (Q(2), (Q(0), Q(0))),
                           (Q(1, 2), (Q(1), Q(-1)))):
            with self.assertRaises(ValueError):
                check.necessary_bounds(gain, bias)
        with self.assertRaises(ValueError):
            check.atomic_detector_polygons(Q(1, 2), (Q(0), Q(0)), (Q(0), Q(2)), (Q(0), Q(0)))

    def test_primary_not_imported(self):
        source = inspect.getsource(check)
        self.assertNotIn("import detector_fiber\n", source)
        self.assertNotIn("from detector_fiber import", source)


if __name__ == "__main__":
    unittest.main()
