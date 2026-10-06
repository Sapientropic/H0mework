"""Complete-domain, original-CI, and immutable-consumer controls."""
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify_all_data as v


def positive_header():
    return {"schema": v.SCHEMA, "version": v.VERSION, "status": "certified", "statistical_role": v.ROLE,
        **{key: True for key in v.POSITIVE_FIELDS}, **{key: False for key in v.FALSE_SCOPE},
        "all_data_fibre_empty": False, "retrospective": True, "bell_event_files_read": 0,
        "foreign_source_fields_used_as_forward_inputs": False,
        "old_training_uniform_prediction_counterexample_retracted": False,
        "crossing_zero_outer_proves_negative_source": False,
        "uniform_CH_N5_strictly_positive": False, "uniform_CH_N5_sign": "unresolved",
        "all_data_fibre_has_certified_source_ambiguity": True,
        "firsts": {kind: {"logical_sha256": sha, "storage_bindings": []} for kind, sha in v.FIRST_SHA.items()},
        "source_bindings": [], "execution_bindings": [], "Lean_certificates": {},
        "production_eligible_role": "sealed conditional public source-family mathematical evidence"}


def toy_primary():
    unit = [["0", "1"] for _ in range(5)]
    left, right = deepcopy(unit), deepcopy(unit)
    left[4], right[4] = ["0", "1/2"], ["1/2", "1"]
    return {"all_leaves_preserved": True, "split_count": 1, "split_cap": 1, "cap_reached": True,
        "splits": [{"path": "", "axis": 4, "midpoint": "1/2"}],
        "nodes": [{"path": ""}, {"path": "4L"}, {"path": "4R"}],
        "leaves": [{"path": "4L", "classification": "retained_boundary", "unit_box": left},
                   {"path": "4R", "classification": "retained_boundary", "unit_box": right}]}


def toy_independent():
    I = v.ind.I
    root = [I(0, 1)] * 5
    left, right = list(root), list(root)
    left[0], right[0] = I(0, "1/2"), I("1/2", 1)
    return v.ind.serial({"initial_source_box": root,
        "cover_tree": [
            {"id": 0, "parent": None, "depth": 0, "input_box": root, "contracted_box": root,
             "status": "split", "split_axis": "m", "children": [1, 2]},
            {"id": 1, "parent": 0, "depth": 1, "input_box": left, "contracted_box": left, "status": "retained_boundary"},
            {"id": 2, "parent": 0, "depth": 1, "input_box": right, "contracted_box": right, "status": "retained_boundary"}],
        "paired_regions": [{"node_id": 1}, {"node_id": 2}]})


class AllDataControls(unittest.TestCase):
    def test_conditional_complete_certificate_positive(self):
        self.assertTrue(v.validate_result(positive_header()))

    def test_readout_integer_one_is_not_certification(self):
        packet = positive_header(); packet["readout_certified"] = 1
        with self.assertRaisesRegex(ValueError, "inconsistent"):
            v.validate_result(packet)

    def test_retrospective_cannot_be_heldout_validation(self):
        packet = positive_header(); packet["heldout_prediction_claimed"] = True
        with self.assertRaisesRegex(ValueError, "inflated"):
            v.validate_result(packet)

    def test_actual_hardware_admission_is_rejected(self):
        for field in ("source_mapping_identified", "actual_epoch_identified", "apparatus_optimum_verified", "production_admitted"):
            packet = positive_header(); packet[field] = True
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "inflated"):
                v.validate_result(packet)

    def test_training_counterexample_cannot_be_retracted(self):
        packet = positive_header(); packet["old_training_uniform_prediction_counterexample_retracted"] = True
        with self.assertRaisesRegex(ValueError, "inflated"):
            v.validate_result(packet)

    def test_crossing_outer_is_not_negative_source(self):
        packet = positive_header(); packet["crossing_zero_outer_proves_negative_source"] = True
        with self.assertRaisesRegex(ValueError, "inflated"):
            v.validate_result(packet)

    def test_source_and_force_overrides_rejected(self):
        for field in ("source_overrides", "force_pass"):
            packet = positive_header(); packet[field] = True
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "override_forbidden"):
                v.validate_result(packet)

    def test_wrong_scientific_first_rejected(self):
        packet = positive_header(); packet["firsts"]["primary"]["logical_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "first_identity"):
            v.validate_result(packet)

    def test_immutable_consumer_positive_and_location_override(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "certificate.json"
            path.write_text(json.dumps(positive_header()))
            binding = {"path": "canonical.json", "sha256": v.sha(path.read_bytes()), "commit": "fixture"}
            with patch.object(v, "frozen", return_value=binding), patch.object(v, "check_bindings", return_value=True):
                result = v.consume(path)
            self.assertTrue(result["readout_certified"])
            self.assertFalse(result["production_admitted"])
            self.assertEqual(result["statistical_role"], v.ROLE)

    def test_lookalike_positive_flags_do_not_open_consumer(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "lookalike.json"
            path.write_text(json.dumps(positive_header()))
            with patch.object(v, "frozen", return_value={"sha256": "0" * 64}):
                result = v.consume(path)
            self.assertFalse(result["evidence_valid"])
            self.assertIn("lookalike", result["reason"])

    def test_disable_precedes_missing_certificate(self):
        result = v.consume(Path("/nonexistent/receipt.json"), disabled=True)
        self.assertFalse(result["readout_certified"])
        self.assertEqual(result["reason"], "explicit_disable")

    def test_disable_requires_boolean(self):
        with self.assertRaisesRegex(ValueError, "boolean"):
            v.consume(disabled=1)

    def test_full_capped_primary_partition(self):
        _, _, leaves, units = v.primary_structure(toy_primary())
        self.assertEqual(len(leaves), 2)
        self.assertEqual(units["4R"][4], (F(1, 2), F(1)))

    def test_dropped_primary_boundary_rejected(self):
        tree = toy_primary(); tree["leaves"].pop()
        with self.assertRaisesRegex(ValueError, "missing_leaf"):
            v.primary_structure(tree)

    def test_duplicate_primary_leaf_rejected(self):
        tree = toy_primary(); tree["leaves"].append(deepcopy(tree["leaves"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            v.primary_structure(tree)

    def test_false_inside_label_rejected(self):
        tree = toy_primary(); tree["leaves"][0]["classification"] = "inside"
        with self.assertRaisesRegex(ValueError, "false_inside"):
            v.primary_structure(tree)

    def test_independent_contracted_parent_partition(self):
        _, nodes, regions = v.independent_partition(toy_independent())
        self.assertEqual(len(nodes), 3)
        self.assertEqual(set(regions), {1, 2})

    def test_independent_gap_rejected(self):
        tree = toy_independent()
        tree["cover_tree"][2]["input_box"][0] = v.ind.I("3/4", 1).packet()
        tree["cover_tree"][2]["contracted_box"][0] = v.ind.I("3/4", 1).packet()
        with self.assertRaisesRegex(ValueError, "gap_or_overlap"):
            v.independent_partition(tree)

    def test_independent_missing_projection_rejected(self):
        tree = toy_independent(); tree["paired_regions"].pop()
        with self.assertRaisesRegex(ValueError, "terminal_projection"):
            v.independent_partition(tree)

    def test_audited_halfspace_retains_legal_points(self):
        I = v.ind.I
        initial = [I(-1, 1), I(-1, 1), I(0), I("1/4", 1), I(0, 1)]
        rows = [{"name": "m_plus_z", "coefficients": [I(1), I(1), I(0), I(0), I(0)], "lower": I("3/2").lo, "upper": None}]
        contracted, audit = v.audited_contract(initial, rows)
        generated, trace = v.ind.linear_contract(initial, rows)
        v.same(contracted, generated, "contractor"); v.same(audit, trace, "trace")
        for m in (F(1, 2), F(3, 4), F(1)):
            for z in (F(1, 2), F(3, 4), F(1)):
                if m + z >= F(3, 2):
                    self.assertTrue(contracted[0].contains(m) and contracted[1].contains(z))

    def test_negative_coefficient_outer_projection(self):
        I = v.ind.I
        rows = [{"name": "minus_m", "coefficients": [I(-1), I(0), I(0), I(0), I(0)], "lower": I("-1/2").lo, "upper": None}]
        box, _ = v.audited_contract([I(0, 1), I(0), I(0), I(1), I(0, 1)], rows)
        self.assertEqual(box[0], I(0, "1/2"))

    def test_zero_coupling_never_divides(self):
        I = v.ind.I
        initial = [I(0, 1), I(0), I(0), I(1), I(0, 1)]
        rows = [{"name": "zero", "coefficients": [I(0)] * 5, "lower": 0, "upper": 0}]
        box, _ = v.audited_contract(initial, rows)
        self.assertEqual(box, initial)

    def test_full_twelve_CI_and_same_local_intersections(self):
        report = (v.HERE.parent.parent / "observable-prediction/public-comparison-po0003.json").read_text()
        config, _, _ = v.independent.configuration()
        _, original, selected, provenance = v.public_domain(report, config)
        self.assertEqual(len(original), 12)
        self.assertEqual(set(selected), {"A0", "B0", "A1", "B1"})
        for axis, packet in selected.items():
            rows = provenance[axis]["source_CI"]
            self.assertEqual(F(packet["exact_lower"]), max(F(r["exact_lower"]) for r in rows))
            self.assertEqual(F(packet["exact_upper"]), min(F(r["exact_upper"]) for r in rows))

    def test_complete_domain_is_not_center_slice(self):
        with self.assertRaisesRegex(ValueError, "incomplete_inverse"):
            v.monotone_inverse_cover({"exact_lower": "1/1000", "exact_upper": "1/1000"},
                                     {"exact_lower": "0", "exact_upper": "1/100"}, F(0))

    def test_ci_separated_sources_are_identifiability_counterexample(self):
        points = [{"source": {"etaA": {"exact_lower": "1/4", "exact_upper": "1/4"}}},
                  {"source": {"etaA": {"exact_lower": "1/2", "exact_upper": "1/2"}}}]
        self.assertTrue(v.source_ambiguity(points)["certified"])
        self.assertFalse(v.source_ambiguity(points[:1])["certified"])


if __name__ == "__main__":
    unittest.main()
