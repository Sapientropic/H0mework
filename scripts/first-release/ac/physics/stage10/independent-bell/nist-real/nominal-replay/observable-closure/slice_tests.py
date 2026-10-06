"""Controls for complete loss coverage, source inputs and unresolved boundaries."""
import copy
from fractions import Fraction as F
import json
import unittest

import primary
import slice as scalar


def partition_contract(partition, source, config):
    rows = partition["segments"]
    primary.require(rows and rows[0]["lower"] == partition["domain"][0] and
                    rows[-1]["upper"] == partition["domain"][1], "MISSING_PARTITION_ENDPOINT")
    primary.require(all(row["lower"] < row["upper"] for row in rows) and
                    all(a["upper"] == b["lower"] for a, b in zip(rows, rows[1:])), "PARTITION_GAP_OR_DUPLICATE")
    for row in rows:
        bounds = row["bounds"]
        if row["classification"] == "inside":
            primary.require(row["lower"] > 0 and row["upper"] <= min(F(1), source["r"].lo) and
                            bounds["phase"].hi <= 0 and bounds["low"].lo >= 0 and bounds["high"].lo >= 0 and
                            bounds["denominator"].lo > 0, "UNCERTIFIED_INSIDE")
        elif row["classification"] == "excluded":
            primary.require(bounds["phase"].lo > 0 or bounds["low"].hi < 0 or bounds["high"].hi < 0 or
                            row["lower"] > source["r"].hi or bounds["denominator"].hi <= 0,
                            "UNJUSTIFIED_EXCLUSION")
        else:
            primary.require(row["classification"] == "boundary", "UNKNOWN_PARTITION_CLASS")
            primary.require(row["upper"]-row["lower"] <= F(config["scalar_cover_width"]) or
                            partition["cap_reached"], "PREMATURE_BOUNDARY")


class ScalarTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        primary.frozen(__file__)
        cls.cfg, _, cls.g, cls.fw, _, _ = scalar.load()
        cls.counts = json.loads((scalar.HERE/cls.cfg["public_counts"]).read_text())["counts"]
        cls.ci = json.loads((scalar.HERE/cls.cfg["public_confidence_report"]).read_text())["common_mean_confidence"]
        cls.training = scalar.training_view(cls.counts)
        cls.j11 = scalar.interval_from_receipt(cls.ci["j"][3], cls.g.I)
        cls.result = scalar.generate(cls.training, cls.j11, cls.cfg, cls.g, cls.fw)

    def test_positive_full_cover_and_member(self):
        result = self.result
        partition_contract(result["partition"], result["source"], self.cfg)
        self.assertFalse(result["partition"]["cap_reached"])
        self.assertTrue(any(x["classification"] == "boundary" for x in result["partition"]["segments"]))
        member = result["canonical_member"]
        self.assertIsNotNone(member)
        included = scalar.compare_cells(member["cells"], self.ci)
        self.assertTrue(all(all(x) for x in included.values()))
        self.assertFalse(result["full_statistical_fiber_certified"])

    def test_fixed_exposure_heldout_outcomes_do_not_change_source(self):
        altered = copy.deepcopy(self.counts)
        for index in (1, 2):
            total = sum(altered[index])
            altered[index] = [total//8, total//4, total//16, total-total//8-total//4-total//16]
        training = scalar.training_view(altered)
        self.assertEqual(training, self.training)
        generated = scalar.generate(training, self.j11, self.cfg, self.g, self.fw)
        self.assertEqual(primary.serial(generated, self.g.I), primary.serial(self.result, self.g.I))

    def test_joint11_center_is_not_a_source_input(self):
        altered = copy.deepcopy(self.counts)
        altered[3] = [altered[3][0]+10, altered[3][1]-10, altered[3][2]-10, altered[3][3]+10]
        self.assertEqual(scalar.training_view(altered), self.training)

    def test_heldout_confidence_changes_do_not_change_training_selector(self):
        altered = copy.deepcopy(self.ci)
        for key in altered:
            for index in (1, 2):
                altered[key][index] = {"exact_lower": "1/2", "exact_upper": "3/4"}
        self.assertEqual(scalar.interval_from_receipt(altered["j"][3], self.g.I), self.j11)

    def test_lookalike_source_input_rejected(self):
        training = copy.deepcopy(self.training)
        training["3"]["j"] = F(106, sum(self.counts[3]))
        with self.assertRaisesRegex(ValueError, "NONSLICE"):
            scalar.shape(training, self.j11, self.cfg, self.g, self.fw)

    def test_split_override_preserves_unresolved_domain(self):
        config = {**self.cfg, "scalar_cover_split_cap": 0}
        result = scalar.generate(self.training, self.j11, config, self.g, self.fw)
        self.assertTrue(result["partition"]["cap_reached"])
        self.assertIsNone(result["canonical_member"])
        self.assertEqual(len(result["partition"]["segments"]), 1)
        self.assertEqual(result["partition"]["segments"][0]["classification"], "boundary")
        self.assertEqual(len(result["paired_predictions"]), 1)
        partition_contract(result["partition"], result["source"], config)

    def test_zero_loss_cannot_be_a_finite_source_member(self):
        with self.assertRaisesRegex(ValueError, "ILLEGAL_CANONICAL"):
            scalar.member(self.result["source"], F(0), self.cfg, self.g, self.fw)

    def test_missing_partition_segment_rejected(self):
        partition = copy.deepcopy(self.result["partition"])
        del partition["segments"][10]
        with self.assertRaisesRegex(ValueError, "PARTITION_GAP"):
            partition_contract(partition, self.result["source"], self.cfg)

    def test_duplicate_partition_segment_rejected(self):
        partition = copy.deepcopy(self.result["partition"])
        partition["segments"].insert(11, partition["segments"][10])
        with self.assertRaisesRegex(ValueError, "PARTITION_GAP"):
            partition_contract(partition, self.result["source"], self.cfg)

    def test_discarded_boundary_rejected(self):
        partition = copy.deepcopy(self.result["partition"])
        partition["segments"] = [x for x in partition["segments"] if x["classification"] != "boundary"]
        with self.assertRaisesRegex(ValueError, "PARTITION_GAP|MISSING_PARTITION"):
            partition_contract(partition, self.result["source"], self.cfg)

    def test_invalid_joint_interval_rejected(self):
        with self.assertRaisesRegex(ValueError, "INVALID_TRAINING_INTERVAL"):
            scalar.shape(self.training, self.g.I(-2, -1), self.cfg, self.g, self.fw)

    def test_bernstein_bounds_cover_polynomial_controls(self):
        I = self.g.I
        for coefficients in ([F(1), F(-3), F(2)], [F(-1, 7), F(2), F(-5), F(1), F(3)]):
            p = [I.point(x) for x in coefficients]
            bound = scalar.bernstein_range(p, F(-1, 2), F(3, 2), I)
            for i in range(33):
                x = F(-1, 2)+F(i, 16)
                self.assertTrue(bound.contains(sum(c*x**k for k, c in enumerate(coefficients))))


if __name__ == "__main__":
    unittest.main(verbosity=2)
