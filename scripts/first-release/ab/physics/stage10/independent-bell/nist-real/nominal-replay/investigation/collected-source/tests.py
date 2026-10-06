import copy
import math
import unittest

from verify import freeze_check, distance
from model import OpticalSource, frozen, analyzer, expectation, click_table, family_report, encode
import independent


class SourceControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        freeze_check()
        cls.spec = frozen()
        cls.recipes = {r["name"]: r for r in cls.spec["fixtures"]}

    def source(self, name):
        return OpticalSource(self.recipes[name])

    def close(self, a, b):
        self.assertLessEqual(abs(a-b), self.spec["tolerance"])

    def test_independent_full_family(self):
        self.assertLessEqual(distance(family_report(), independent.generate()), self.spec["tolerance"])

    def test_branch_norm_and_positive_objects(self):
        for recipe in self.recipes.values():
            source = OpticalSource(recipe)
            stats = source.statistics()
            for branch in stats["branches"]:
                self.close(sum(sum(row) for row in branch), 1)
            self.assertLessEqual(abs(stats["Z"])**2, stats["C"][0]*stats["C"][1]+2e-12)
            for r in self.spec["r_values"]:
                state = independent.full_state(recipe, r, 0.5)
                self.close(sum(abs(z)**2 for z in state.values()), 1)
                o = source.objects(r, 0.5)
                for p, k in enumerate((0, 3)):
                    self.assertGreaterEqual(o["A"][p][p].real-o["AB"][k][k].real, -2e-12)
                    self.assertGreaterEqual(o["B"][p][p].real-o["AB"][k][k].real, -2e-12)
                    self.close(o["A"][p][1-p], 0)
                    self.close(o["B"][p][1-p], 0)

    def test_all_click_outcomes_and_no_signal(self):
        for recipe in self.recipes.values():
            source = OpticalSource(recipe)
            for r in self.spec["r_values"]:
                for a in self.spec["analyzers"]:
                    prior = None
                    for b in self.spec["analyzers"]:
                        read = source.read(r, 0.5, a, b, **self.spec["rates"])
                        table = click_table(read)
                        self.close(sum(table), 1)
                        self.assertGreaterEqual(min(table), -2e-12)
                        if prior is not None:
                            self.close(read["sA"], prior)
                        prior = read["sA"]
                        # Sum the two orthogonal collected B polarizations: CC-only A marginal.
                        other_b = (b[0]+0.5, b[1])
                        marginal = source.read(r, 0.5, a, b)["j"]+source.read(r, 0.5, a, other_b)["j"]
                        o = source.objects(r, 0.5)
                        cc_a = [[o["AB"][0][0], 0], [0, o["AB"][3][3]]]
                        self.close(marginal, expectation(cc_a, analyzer(*a)))

    def test_uniform_scalar_reduction(self):
        source = self.source("uniform")
        a, b = source.statistics()["A"][0], source.statistics()["B"][0]
        ideal = self.source("all_collected")
        for r in self.spec["r_values"]:
            rate = source.rates(r, **self.spec["rates"])
            self.close(rate["q_eff"], self.spec["rates"]["Q"])
            self.close(rate["etaA_K"], a*self.spec["rates"]["uA"])
            self.close(rate["etaB_K"], b*self.spec["rates"]["uB"])
            for x in self.spec["analyzers"]:
                for y in self.spec["analyzers"]:
                    actual = source.read(r, 0, x, y)
                    pure = ideal.read(r, 0, x, y)
                    self.close(actual["sA"], a*pure["sA"])
                    self.close(actual["sB"], b*pure["sB"])
                    self.close(actual["j"], a*b*pure["j"])

    def test_uniform_override_and_path_filter(self):
        source = self.source("path_filter")
        self.assertGreater(abs(source.collected_shape(0.5)["A_proportional_residual"]), 0.01)
        recipe = copy.deepcopy(self.recipes["path_filter"])
        recipe["beta_A"][1] = recipe["beta_A"][0][:]
        recipe["beta_B"][1] = recipe["beta_B"][0][:]
        recipe["phase_A"][1] = recipe["phase_A"][0][:]
        override = OpticalSource(recipe)
        self.close(override.collected_shape(0.5)["r_col_population"], 0.5)
        self.close(override.collected_shape(0.5)["A_proportional_residual"], 0)

    def test_joint_partial_trace_is_not_singles(self):
        o = self.source("calibration_II").objects(0.5)
        self.assertGreater(o["A"][0][0].real-o["AB"][0][0].real, 0.1)
        self.assertGreater(o["B"][1][1].real-o["AB"][3][3].real, 0.01)

    def test_same_balanced_calibration_distinct_unbalanced_singles(self):
        one, two = self.source("calibration_I"), self.source("calibration_II")
        for r in self.spec["r_values"]:
            for rows in zip(one.objects(r)["AB"], two.objects(r)["AB"]):
                for a, b in zip(*rows):
                    self.close(a, b)
        self.close(distance(one.rates(1, **self.spec["rates"]), two.rates(1, **self.spec["rates"])), 0)
        r1, r2 = (x.rates(0.5, **self.spec["rates"]) for x in (one, two))
        self.close(r2["Pa"], 59/100)
        self.close(r2["Pb"], 41/100)
        self.assertGreater(abs(r1["etaA_K"]-r2["etaA_K"]), 0.05)
        # Full balanced polarization-resolved singles WOULD distinguish them.
        self.assertGreater(abs(one.objects(1)["A"][0][0]-two.objects(1)["A"][0][0]), 0.05)

    def test_complex_overlap_and_y_sensitive_control(self):
        source = self.source("unread_tag")
        self.assertGreater(abs(source.statistics()["Z"].imag), 0.01)
        self.assertLess(abs(source.collected_shape(1)["coherence"]), 0.99)
        first = source.read(0.5, 0, (0.25, 0), (0.25, 0.5))["j"]
        second = source.read(0.5, 0, (0.25, 0), (0.25, -0.5))["j"]
        self.assertGreater(abs(first-second), 0.001)

    def test_endpoints_and_zero_denominators(self):
        source = self.source("all_lost")
        self.assertEqual(source.rates(1, **self.spec["rates"])["q_eff"], None)
        for name in self.recipes:
            s = self.source(name)
            self.close(s.objects(0)["AB"][3][3], 0)
            self.close(s.objects(0)["A"][1][1], 0)
            self.assertEqual(s.rates(1, 0, 1, 1)["q_eff"], None)
            for amplitudes in ((1, 0), (0, 1)):
                state = independent.state_from_preparation(self.recipes[name], amplitudes)
                self.close(distance(encode(s.objects_from_preparation(*amplitudes)),
                                    independent.serial(independent.density_objects(state))), 0)
        self.assertEqual(self.source("uniform").rates(1, 1, 0, 1)["q_eff"], None)

    def test_invalid_upstream_inputs(self):
        for changed in ({"power_H": [[0.5]]}, {"power_H": []}, {"beta_A": [[float("nan")],[0]]}):
            bad = dict(self.recipes["all_collected"], **changed)
            with self.assertRaises(ValueError):
                OpticalSource(bad)
        for r in (-1, float("nan"), float("inf")):
            with self.assertRaises(ValueError):
                self.source("uniform").objects(r)

    def test_bucket_binomial_loss_reduction(self):
        control = self.spec["four_mode_control"]
        admitted = 0
        for n in control["n"]:
            for t in control["T"]:
                for u in control["u"]:
                    for d in control["d"]:
                        # The historical additive effect is only admitted if every occupancy is <=1.
                        if any(1-(1-u)**k+d > 1 for k in range(4)):
                            continue
                        actual = sum(math.comb(n,k)*t**k*(1-t)**(n-k)*(1-(1-u)**k+d)
                                     for k in range(n+1))
                        self.close(actual, 1-(1-u*t)**n+d)
                        admitted += 1
        self.assertEqual(admitted, 60)


if __name__ == "__main__":
    unittest.main()
