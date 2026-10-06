"""Same-source controls for the complete retrospective CI intersection."""
import copy
from fractions import Fraction as F
import unittest

import primary_all_data as p
import primary_fiber as base


class AllDataPrimaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.c = p.configuration()
        cls.I = cls.c["I"]

    def generated(self, phase=F(1, 1000)):
        nh, nv, ea, eb, delta = F(1, 2500), F(1, 25000), F(3, 4), F(153, 200), F(2)
        trig = self.c["utility"].trig_deg
        vectors = [trig(F(a)-delta, self.c["spec"], self.c["gauss"]) for a in self.c["spec"]["angles_deg"]]
        means = [eta*(nh*sa.square()+nv*ca.square()) for (sa, ca), eta in zip(vectors, (ea, ea, eb, eb))]
        box = [means[0], means[2], means[1], means[3], self.I.point(ea)]
        model = base.covariance(box)
        cells = base.coefficients(model)
        K = (1-2*phase)*self.c["gauss"].square_root(model["T2"])
        windows = [base.window_readout(cell, K) for cell in cells]
        margin = F(1, 10**6)
        originals = {field: [self.I(max(F(0), row[key].lo-margin), row[key].hi+margin) for row in windows]
                     for key, field in (("sA", "sA_cell"), ("sB", "sB_cell"), ("j", "j"))}
        report = {"common_mean_confidence": {field: [base.pack(value) for value in rows]
                                              for field, rows in originals.items()}}
        return box, model, cells, K, windows, report, p.all_ci_view(report)

    def test_all_local_rows_are_intersected_with_original_provenance(self):
        _, _, _, _, _, report, _ = self.generated()
        changed = copy.deepcopy(report)
        row = changed["common_mean_confidence"]["sA_cell"][1]
        row["exact_lower"] = str((F(row["exact_lower"])+F(row["exact_upper"]))/2)
        ci = p.all_ci_view(changed)
        self.assertEqual(ci["A0"].lo, F(row["exact_lower"]))
        self.assertEqual(len(ci["originals"]["sA_cell"]), 4)
        self.assertEqual(len(ci["joint"]), 4)

    def test_incompatible_same_setting_CI_rejects_without_dropping_row(self):
        _, _, _, _, _, report, _ = self.generated()
        report["common_mean_confidence"]["sA_cell"][1] = {"exact_lower": "1/2", "exact_upper": "3/4"}
        with self.assertRaisesRegex(ValueError, "incompatible_same_local_setting_CI:A0"):
            p.all_ci_view(report)

    def test_all_four_phase_slabs_keep_the_generated_phase(self):
        _, model, cells, K, _, _, ci = self.generated()
        common, slabs = p.common_phase(model, cells, ci)
        self.assertIsNotNone(common)
        self.assertEqual([row["cell"] for row in slabs], list(range(4)))
        self.assertLessEqual(common.lo, K.lo)
        self.assertGreaterEqual(common.hi, K.hi)

    def test_different_cell_phases_do_not_form_one_source(self):
        _, model, cells, _, _, _, ci = self.generated()
        T = self.c["gauss"].square_root(model["T2"])
        ci["joint"] = [self.I(0, 1) for _ in range(4)]
        for row, k in ((0, T), (1, -T)):
            j = base.window_readout(cells[row], k)["j"]
            ci["joint"][row] = self.I(j.lo-F(1, 10**15), j.hi+F(1, 10**15))
        common, _ = p.common_phase(model, cells, ci)
        self.assertIsNone(common)

    def test_Bernstein_contrast_matches_same_phase_point_readouts(self):
        for phase in (F(0), F(1, 2), F(1)):
            _, _, cells, K, windows, _, _ = self.generated(phase)
            actual = p.paired_contrasts(cells, windows, K)
            expected = {"joint_sum": windows[1]["j"]+windows[2]["j"],
                        "joint_difference": windows[1]["j"]-windows[2]["j"],
                        "CH_N5": windows[0]["j"]+windows[1]["j"]+windows[2]["j"]-windows[3]["j"]-windows[0]["sA"]-windows[0]["sB"]}
            for field in expected:
                self.assertIsNotNone(base.intersect(actual[field], expected[field]))
                self.assertLess(actual[field].hi-actual[field].lo, F(1, 10**12))

    def test_Bernstein_encloses_interior_phase_values(self):
        _, model, cells, _, _, _, _ = self.generated()
        T = self.c["gauss"].square_root(model["T2"])
        domain = self.I(-T.hi, T.hi)
        bounds = [p.polynomial_bound(p.joint_polynomial(cell), domain) for cell in cells]
        for weight in (F(0), F(1, 4), F(1, 2), F(3, 4), F(1)):
            K = self.I.point(domain.lo+weight*(domain.hi-domain.lo))
            for cell, bound in zip(cells, bounds):
                value = base.window_readout(cell, K)["j"]
                self.assertLessEqual(bound.lo, value.lo)
                self.assertGreaterEqual(bound.hi, value.hi)

    def test_positive_Fock_member_pays_all_twelve_original_CI(self):
        box, _, _, _, _, _, ci = self.generated()
        candidates = p.point_members(box, ci)
        self.assertTrue(candidates)
        self.assertTrue(candidates[0]["actual_positive_Fock"]["all_twelve_original_CI_contained"])
        self.assertTrue(candidates[0]["actual_positive_Fock"]["readout"]["phase_mixture_before_window"])
        self.assertFalse(candidates[0]["actual_positive_Fock"]["readout"]["finite_prefix_renormalized"])

    def test_loss_zero_stays_outer_and_never_becomes_finite_member(self):
        box, _, _, _, _, _, ci = self.generated()
        box[4] = self.I.point(0)
        self.assertEqual(p.point_members(box, ci), [])

    def test_cap_retains_full_partition_and_unresolved_cells(self):
        _, _, _, _, _, _, ci = self.generated()
        tree = p.cover(ci, base.training_domain(ci), cap=4)
        self.assertEqual(len(tree["nodes"]), 2*tree["split_count"]+1)
        self.assertEqual(len(tree["leaves"]), tree["split_count"]+1)
        self.assertTrue(tree["all_leaves_preserved"])
        volume = F(0)
        for leaf in tree["leaves"]:
            volume += F(1, 2**(len(leaf["path"])//2))
        self.assertEqual(volume, 1)
        self.assertTrue(any(leaf["classification"] == "retained_boundary" for leaf in tree["leaves"]))


if __name__ == "__main__":
    unittest.main()
