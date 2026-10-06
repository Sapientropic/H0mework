"""Observable closure controls: actual source recovery, root retention and input separation."""
from fractions import Fraction as F
import unittest

import primary


class ClosureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        primary.frozen(__file__)
        cls.config, _, cls.g, cls.utility, _, _ = primary.configuration()
        cls.training, cls.expected = cls.control()

    @classmethod
    def control(cls):
        g, cfg, fw = cls.g, cls.config, cls.utility
        nH, nV, eA, eB, lam = F(1, 1000), F(1, 15000), F(13, 20), F(4, 5), F(1, 25)
        sr, cr = fw.trig_deg(F(-3, 5), cfg, g)
        ba, bb = map(F, cfg["background_per_pulse"])
        vectors = []
        for angle in cfg["angles_deg"]:
            s, c = fw.trig_deg(F(angle), cfg, g)
            vectors.append((s*cr-c*sr, s*sr+c*cr))
        cells = []
        for a in range(2):
            for b in range(2):
                ah, av = vectors[a]
                bh, bv = vectors[2+b]
                ma, mb = eA*(nH*ah.square()+nV*av.square()), eB*(nH*bh.square()+nV*bv.square())
                kh, kv = g.square_root(nH*(1+nH)*eA*eB), g.square_root(nV*(1+nV)*eA*eB)
                d0 = (1+ma)*(1+mb)-(kh*ah*bh+kv*av*bv).square()
                d1 = (1+ma)*(1+mb)-(kh*ah*bh-kv*av*bv).square()
                qa, qb = g.power((1-ba)/(1+ma), 5), g.power((1-bb)/(1+mb), 5)
                qab = g.power((1-ba)*(1-bb)*((1-lam)/d0+lam/d1), 5)
                cells.append({"sA": 1-qa, "sB": 1-qb, "j": 1-qa-qb+qab})
        training = {str(i): {k: v.midpoint() for k, v in cells[i].items()} for i in (0, 3)}
        return training, cells

    def test_positive_actual_source_recovery(self):
        source = primary.generate(self.training, self.config, self.g, self.utility)
        legal = [b for b in source["branches"] if b["status"] == "LEGAL_EXACT_ROOT_BRANCH"]
        self.assertEqual(len(legal), 1)
        branch = legal[0]
        self.assertLess(abs(branch["etaA"].midpoint()-F(13, 20)), F(1, 10**8))
        self.assertLess(abs(branch["etaB"].midpoint()-F(4, 5)), F(1, 10**8))
        self.assertLess(abs(branch["lambda"].midpoint()-F(1, 25)), F(1, 10**8))
        for actual, expected in zip(branch["cells"], self.expected):
            for feature in ("sA", "sB", "j"):
                self.assertLess(abs(actual[feature].midpoint()-expected[feature].midpoint()), F(1, 10**12))

    def test_complete_heldout_changes_leave_source_inputs_identical(self):
        counts = [[10, 2, 3, 10000], [5, 4, 6, 1000], [8, 1, 2, 2000], [1, 20, 25, 9000]]
        view = primary.training_view(counts)
        counts[1], counts[2] = [999, 2, 1, 10], [777, 33, 66, 77]
        self.assertEqual(view, primary.training_view(counts))

    def test_nontraining_lookalike_rejected(self):
        with self.assertRaisesRegex(ValueError, "NONTRAINING"):
            primary.generate({**self.training, "1": self.training["0"]}, self.config, self.g, self.utility)

    def test_unknown_calibration_override_rejected(self):
        altered = {k: dict(v) for k, v in self.training.items()}
        altered["0"]["Klyshko_A"] = F(747, 1000)
        with self.assertRaisesRegex(ValueError, "NONTRAINING"):
            primary.generate(altered, self.config, self.g, self.utility)

    def test_complete_counts_reject_boolean(self):
        with self.assertRaisesRegex(ValueError, "INVALID_COMPLETE"):
            primary.training_view([[True, 1, 1, 4], [0]*4, [0]*4, [1, 1, 1, 4]])

    def test_quadratic_keeps_both_roots(self):
        p = self.g.I.point
        status, roots = primary.quadratic_roots([p(2), p(-3), p(1)], self.g)
        self.assertEqual(status, "QUADRATIC_TWO_REAL_ROOTS")
        self.assertEqual(sorted(r["e"].midpoint() for r in roots), [1, 2])

    def test_repeated_linear_and_continuous_fibers(self):
        p = self.g.I.point
        status, roots = primary.quadratic_roots([p(1), p(-2), p(1)], self.g)
        self.assertEqual((status, len(roots), roots[0]["multiplicity"]), ("QUADRATIC_REPEATED", 1, 2))
        status, roots = primary.quadratic_roots([p(-2), p(1), p(0)], self.g)
        self.assertEqual((status, roots[0]["e"].midpoint()), ("LINEAR", 2))
        self.assertEqual(primary.quadratic_roots([p(0)]*3, self.g), ("CONTINUOUS_FIBER", []))

    def test_uncertain_leading_term_does_not_drop_quadratic(self):
        p = self.g.I.point
        status, roots = primary.quadratic_roots([p(1), p(1), self.g.I(-F(1, 10**20), F(1, 10**20))], self.g)
        self.assertEqual((status, roots), ("COEFFICIENT_UNRESOLVED", []))

    def test_no_real_center_roots(self):
        p = self.g.I.point
        self.assertEqual(primary.quadratic_roots([p(1), p(0), p(1)], self.g), ("NO_REAL_CENTER_ROOT", []))


if __name__ == "__main__":
    unittest.main(verbosity=2)
