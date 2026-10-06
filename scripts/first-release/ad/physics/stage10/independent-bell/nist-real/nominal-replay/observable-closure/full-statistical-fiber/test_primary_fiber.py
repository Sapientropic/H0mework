"""Synthetic optical controls for complete-fibre arithmetic and retained boundaries."""
from fractions import Fraction as F
import copy
import unittest

import primary_fiber as p


class FullFiberPrimaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.c = p.context()
        cls.I = cls.c["I"]

    def source(self, nh=F(1, 2500), nv=F(1, 25000), ea=F(3, 4), eb=F(153, 200),
               delta=F(2), lam=F(1, 1000)):
        c, I = self.c, self.I
        angles = list(map(F, c["spec"]["angles_deg"]))
        vectors = [c["utility"].trig_deg(a - delta, c["spec"], c["gauss"]) for a in angles]
        means = [eta * (nh * sa.square() + nv * ca.square())
                 for (sa, ca), eta in zip(vectors, (ea, ea, eb, eb))]
        box = [means[0], means[2], means[1], means[3], I.point(ea)]
        model = p.covariance(box)
        cells = p.coefficients(model)
        K = (1 - 2 * lam) * c["gauss"].square_root(model["T2"])
        ba, bb = map(F, c["spec"]["background_per_pulse"])
        th, tv = nh / (1 + nh), nv / (1 + nv)
        native = []
        for a, b in ((angles[0], angles[2]), (angles[0], angles[3]),
                     (angles[1], angles[2]), (angles[1], angles[3])):
            branches = []
            for sign in (1, -1):
                src = c["gauss"].Source(c["gauss"].parameter_packet((th, tv), (ea, ea), (eb, eb), F(sign)))
                branches.append(src.pulse(a - delta, b - delta, c["spec"]))
            qa = (1 - ba) * branches[0]["no_click_A"]
            qb = (1 - bb) * branches[0]["no_click_B"]
            qab = ((1 - ba) * (1 - bb) *
                   ((1 - lam) * branches[0]["no_click_AB"] + lam * branches[1]["no_click_AB"]))
            native.append({"sA": 1 - p.powi(qa, 5), "sB": 1 - p.powi(qb, 5),
                           "j": 1 - p.powi(qa, 5) - p.powi(qb, 5) + p.powi(qab, 5)})
        return box, model, cells, K, native

    def close_intervals(self, a, b):
        self.assertLessEqual(max(F(0), a.lo - b.hi, b.lo - a.hi), F(1, 10**12))

    def test_stable_formula_matches_independent_native_vacuum_windows(self):
        for delta, lam in ((F(0), F(0)), (F(2), F(1, 1000)), (F(-3), F(2, 3))):
            _, _, cells, K, native = self.source(delta=delta, lam=lam)
            for cell, expected in zip(cells, native):
                actual = p.window_readout(cell, K)
                for key in ("sA", "sB", "j"):
                    self.close_intervals(actual[key], expected[key])

    def test_phase_mixture_occurs_before_five_pulse_window(self):
        _, _, cells, K, native = self.source(lam=F(1, 2))
        actual = p.window_readout(cells[0], K)["j"]
        self.close_intervals(actual, native[0]["j"])
        _, _, _, _, plus = self.source(lam=F(0))
        _, _, _, _, minus = self.source(lam=F(1))
        wrong = (plus[0]["j"] + minus[0]["j"]) / 2
        self.assertGreater(max(F(0), wrong.lo - actual.hi, actual.lo - wrong.hi), F(1, 10**12))

    def test_shared_phase_interval_contains_actual_generated_phase(self):
        box, model, cells, K, native = self.source()
        margin = F(1, 10**6)
        ci = {name: self.I(value.lo - margin, value.hi + margin)
              for name, value in zip(p.NAMES, (native[0]["sA"], native[0]["sB"],
                    native[3]["sA"], native[3]["sB"], native[0]["j"], native[3]["j"]))}
        phase, _ = p.phase_domain(model, cells, ci)
        self.assertIsNotNone(phase)
        self.assertLessEqual(phase.lo, K.lo)
        self.assertGreaterEqual(phase.hi, K.hi)

    def test_zero_coupling_keeps_or_rejects_constant_slab_without_division(self):
        K = self.I(-1, 1)
        self.assertEqual(p.affine_phase_clip(K, self.I.point(0), self.I(-1, 0), self.I(0, 1)), K)
        self.assertIsNone(p.affine_phase_clip(K, self.I.point(0), self.I(1, 2), self.I(3, 4)))

    def test_coupling_crossing_zero_retains_outer_phase(self):
        K = self.I(-1, 1)
        self.assertEqual(p.affine_phase_clip(K, self.I(-1, 1), self.I(-1, 0), self.I(0, 1)), K)

    def test_binomial_root_contains_exact_algebraic_root(self):
        for u in (F(0), F(1, 10000), F(-1, 10000), F(1, 100)):
            actual = p.root1p_minus1(self.I.point(u))
            expected = (self.c["utility"].nth_root(1 + u, 5, 50, self.I) - 1 if u <= 0 else
                        1 / self.c["utility"].nth_root(1 / (1 + u), 5, 50, self.I) - 1)
            self.assertLessEqual(actual.lo, expected.lo)
            self.assertGreaterEqual(actual.hi, expected.hi)

    def test_single_inverse_is_monotone_and_reads_interval_endpoints(self):
        box, _, _, _, native = self.source()
        ba = F(self.c["spec"]["background_per_pulse"][0])
        inverse = p.inverse_single(native[0]["sA"], ba)
        self.close_intervals(inverse, box[0])

    def test_scalar_loss_zero_is_not_a_finite_member(self):
        box, _, _, _, native = self.source()
        box[4] = self.I.point(0)
        ci = {name: self.I(0, 1) for name in p.NAMES}
        self.assertEqual(p.point_member(box, ci), [])

    def test_source_input_view_excludes_all_heldout_values(self):
        row = {"exact_lower": "1/10000", "exact_upper": "1/1000"}
        q = {name: [copy.deepcopy(row) for _ in range(4)] for name in ("j", "sA_cell", "sB_cell")}
        report = {"common_mean_confidence": q}
        a = p.ci_view(report)
        for feature in q.values():
            feature[1]["exact_lower"] = "0"; feature[2]["exact_upper"] = "1"
        self.assertEqual(p.ci_view(report), a)

    def test_cap_retains_every_partition_leaf(self):
        box, _, _, _, native = self.source()
        margin = F(1, 10**6)
        ci = {name: self.I(max(F(0), value.lo - margin), value.hi + margin)
              for name, value in zip(p.NAMES, (native[0]["sA"], native[0]["sB"],
                   native[3]["sA"], native[3]["sB"], native[0]["j"], native[3]["j"]))}
        domain = p.training_domain(ci)
        tree = p.cover(ci, domain, cap=8)
        self.assertEqual(len(tree["leaves"]), tree["split_count"] + 1)
        self.assertTrue(tree["all_leaves_preserved"])
        volume = F(0)
        split_map = {v["path"]: v["axis"] for v in tree["splits"]}
        for leaf in tree["leaves"]:
            factors = [F(1)] * 5
            path = leaf["path"]
            for index in range(0, len(path), 2):
                parent = path[:index]
                self.assertEqual(int(path[index]), split_map[parent])
                factors[int(path[index])] /= 2
            v = F(1)
            for factor in factors: v *= factor
            volume += v
        self.assertEqual(volume, 1)


if __name__ == "__main__":
    unittest.main()
