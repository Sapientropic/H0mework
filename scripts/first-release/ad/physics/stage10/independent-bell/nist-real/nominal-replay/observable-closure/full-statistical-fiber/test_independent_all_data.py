"""All-CI provenance, shared-phase, and positive-Born source controls."""
import copy
from fractions import Fraction as F
import json
import unittest

import independent_all_data as all_data

base = all_data.base


class IndependentAllDataTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.config = all_data.configuration()[0]
        cls.const = base.constants(cls.config)
        cls.box = [base.I(".0015"), base.I(".0005"), base.I(0), base.I(1), base.I(".75")]

    def source_CI(self, k=None, tolerance=F(1, 10**8)):
        k = base.I(0) if k is None else k
        pop = base.population(self.box)
        cells = [base.cell_readout(base.geometry(self.box, pop, self.const, row), k, self.const) for row in range(4)]
        original = {}
        for field, row in all_data.ALL_FIELDS:
            name = {"sA_cell":"sA", "sB_cell":"sB", "j":"j"}[field]
            center = cells[row][name].midpoint()
            original[field+"["+str(row)+"]"] = {"exact_lower":str(center-tolerance), "exact_upper":str(center+tolerance)}
        return original

    def test_all_twelve_CI_are_parsed_and_changed_row_is_consumed(self):
        packets = [{"exact_lower":"1/10000", "exact_upper":"2/10000"} for _ in range(4)]
        report = {"common_mean_confidence":{name:copy.deepcopy(packets) for name in ("sA_cell", "sB_cell", "j")}}
        first = all_data.parse_all_CI(json.dumps(report))
        self.assertEqual(len(first), 12)
        report["common_mean_confidence"]["j"][1]["exact_upper"] = "3/10000"
        self.assertNotEqual(first, all_data.parse_all_CI(json.dumps(report)))

    def test_exact_single_intersections_preserve_both_original_sources(self):
        original = self.source_CI()
        original["sA_cell[0]"] = {"exact_lower":"1/7", "exact_upper":"2/7"}
        original["sA_cell[1]"] = {"exact_lower":"1/6", "exact_upper":"1/4"}
        selected, provenance = all_data.single_intersections(original)
        self.assertEqual(selected["A0"], {"exact_lower":"1/6", "exact_upper":"1/4"})
        self.assertEqual(provenance["A0"]["source_rows"], [0, 1])
        self.assertEqual(provenance["A0"]["source_CI"], [original["sA_cell[0]"], original["sA_cell[1]"]])

    def test_empty_single_intersection_is_a_true_compatibility_rejection(self):
        original = self.source_CI()
        original["sA_cell[0]"] = {"exact_lower":"1/10", "exact_upper":"1/5"}
        original["sA_cell[1]"] = {"exact_lower":"1/4", "exact_upper":"1/3"}
        stage = all_data.source_stage(original, self.config)
        self.assertEqual(stage["status"], "ORIGINAL_SINGLE_CI_INTERSECTION_EMPTY")
        self.assertTrue(stage["all_data_fiber_empty_certified"])
        self.assertFalse(stage["nonempty_all_data_fiber_certified"])
        self.assertFalse(stage["old_uniform_prediction_counterexample_retracted"])
        self.assertEqual(stage["statistical_role"], all_data.ROLE)

    def test_all_four_joint_slabs_preserve_a_common_phase(self):
        original = self.source_CI()
        selected, _ = all_data.single_intersections(original)
        means = all_data.all_means(original, selected, self.config)
        common, slabs = all_data.phase_slabs_all(self.box, base.population(self.box), self.const, means, self.config)
        self.assertIsNotNone(common)
        self.assertTrue(common.contains(0))
        self.assertEqual([slab["cell"] for slab in slabs], [0, 1, 2, 3])

    def test_individually_physical_joint_rows_cannot_select_different_phases(self):
        T = base.population(self.box)["T2"].sqrt()
        plus = self.source_CI(T/2, F(1, 10**10))
        minus = self.source_CI(-T/2, F(1, 10**10))
        selected, _ = all_data.single_intersections(plus)
        plus_means = all_data.all_means(plus, selected, self.config)
        plus_common, _ = all_data.phase_slabs_all(self.box, base.population(self.box), self.const, plus_means, self.config)
        self.assertIsNotNone(plus_common)
        mixed = copy.deepcopy(plus)
        mixed["j[1]"] = minus["j[1]"]
        mixed_means = all_data.all_means(mixed, selected, self.config)
        common, _ = all_data.phase_slabs_all(self.box, base.population(self.box), self.const, mixed_means, self.config)
        self.assertIsNone(common)

    def test_member_requires_all_twelve_actual_positive_Born_probabilities(self):
        original = self.source_CI()
        selected, _ = all_data.single_intersections(original)
        means = all_data.all_means(original, selected, self.config)
        member = all_data.legal_member(original, means, [], [], self.box[:-1], F(3, 4), "midpoint", F(0), self.const, self.config)
        self.assertTrue(member["all_twelve_original_CI_contained"])
        self.assertEqual(len(member["all_twelve_checks"]), 12)
        self.assertEqual(len(member["Gaussian_positive_Fock_cross"]), 12)
        self.assertTrue(member["all_four_joints_share_one_k"])
        self.assertFalse(member["actual_positive_Fock_readout"]["finite_prefix_renormalized"])
        altered = copy.deepcopy(original)
        altered["j[1]"] = {"exact_lower":"1/100", "exact_upper":"1/50"}
        with self.assertRaises(ValueError):
            all_data.legal_member(altered, means, [], [], self.box[:-1], F(3, 4), "midpoint", F(0), self.const, self.config)

    def test_paired_readout_and_contrasts_respect_all_source_constraints(self):
        original = self.source_CI()
        selected, _ = all_data.single_intersections(original)
        means = all_data.all_means(original, selected, self.config)
        projection = all_data.paired_readout_all(self.box, base.I(0), base.population(self.box), self.const, means, original)
        self.assertTrue(projection["all_four_joints_use_the_same_k"])
        for field, row in all_data.ALL_FIELDS:
            name = {"sA_cell":"sA", "sB_cell":"sB", "j":"j"}[field]
            self.assertTrue(projection["cells"][row][name].within_exact(original[field+"["+str(row)+"]"]))
        natural_sum = projection["cells"][1]["j"]+projection["cells"][2]["j"]
        self.assertTrue(projection["joint_sum"].contained(natural_sum))

    def test_retrospective_scope_and_original_budget_stay_fixed(self):
        self.assertEqual(self.config["alpha"], "1/20")
        self.assertEqual(self.config["statistical_role"], "retrospective_all_public_CI_intersection")
        self.assertEqual(self.config["member_limit"], 64)
        self.assertFalse(all_data.SCOPE["heldout_prediction_claimed"])
        self.assertFalse(all_data.SCOPE["old_uniform_prediction_counterexample_retracted"])
        self.assertFalse(all_data.SCOPE["apparatus_optimum_verified"])


if __name__ == "__main__":
    unittest.main()
