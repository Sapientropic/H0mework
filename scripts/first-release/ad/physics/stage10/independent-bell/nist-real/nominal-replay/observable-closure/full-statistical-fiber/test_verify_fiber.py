"""Focused controls for complete-tree certification and evidence-only admission."""
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import tempfile
import unittest

import verify_fiber as v


def positive_header():
    return {"schema": v.SCHEMA, "version": v.VERSION, "status": "certified",
            **{key: True for key in v.POSITIVE_FIELDS}, **{key: False for key in v.FALSE_SCOPE},
            "production_admitted": False, "uniform_heldout_contained": False,
            "whole_source_family_rejected": False, "retrospective": True, "bell_event_files_read": 0,
            "foreign_source_fields_used_as_forward_inputs": False,
            "actual_Born_uniform_counterexamples": [{"member": 0, "all_six_training_CI_recomputed": True}]}


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
    nodes = [{"id": 0, "parent": None, "depth": 0, "input_box": root, "contracted_box": root,
              "status": "split", "split_axis": "m", "children": [1, 2]},
             {"id": 1, "parent": 0, "depth": 1, "input_box": left, "contracted_box": left, "status": "retained_boundary"},
             {"id": 2, "parent": 0, "depth": 1, "input_box": right, "contracted_box": right, "status": "retained_boundary"}]
    return v.ind.serial({"cover_tree": nodes, "initial_source_box": root,
                         "paired_regions": [{"node_id": 1}, {"node_id": 2}]})


class FiberVerificationControls(unittest.TestCase):
    def test_positive_conditional_certificate(self):
        self.assertTrue(v.validate_result(positive_header()))

    def test_uniform_counterexample_is_required(self):
        value = positive_header()
        value["actual_Born_uniform_counterexamples"] = []
        with self.assertRaisesRegex(ValueError, "missing_uniform_counterexample"):
            v.validate_result(value)

    def test_integer_one_is_not_boolean_certification(self):
        value = positive_header()
        value["readout_certified"] = 1
        with self.assertRaisesRegex(ValueError, "inconsistent"):
            v.validate_result(value)

    def test_uniform_inside_lookalike_rejected(self):
        value = positive_header()
        value["uniform_heldout_contained"] = True
        with self.assertRaisesRegex(ValueError, "inconsistent"):
            v.validate_result(value)

    def test_actual_hardware_identity_not_minted(self):
        value = positive_header()
        value["source_mapping_identified"] = True
        with self.assertRaisesRegex(ValueError, "inflated"):
            v.validate_result(value)

    def test_hardware_production_admission_rejected(self):
        value = positive_header()
        value["production_admitted"] = True
        with self.assertRaisesRegex(ValueError, "inflated"):
            v.validate_result(value)

    def test_source_script_override_rejected(self):
        value = positive_header()
        value["source_overrides"] = {"primary_fiber.py": "/tmp/foreign-script.py"}
        with self.assertRaisesRegex(ValueError, "override_forbidden"):
            v.validate_result(value)

    def test_force_pass_rejected(self):
        value = positive_header()
        value["force_pass"] = True
        with self.assertRaisesRegex(ValueError, "override_forbidden"):
            v.validate_result(value)

    def test_disable_is_immediate_override(self):
        result = v.consume(Path("/nonexistent/receipt.json"), disabled=True)
        self.assertFalse(result["evidence_valid"])
        self.assertEqual(result["reason"], "explicit_disable")

    def test_disable_requires_exact_boolean(self):
        with self.assertRaisesRegex(ValueError, "boolean"):
            v.consume(disabled=1)

    def test_production_rejects_schema_lookalike(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "cross-verification.json"
            path.write_text(json.dumps(positive_header()))
            self.assertFalse(v.consume(path)["production_eligible"])

    def test_capped_full_tree_preserves_entire_domain(self):
        _, _, leaves, units = v.primary_structure(toy_primary())
        self.assertEqual(len(leaves), 2)
        self.assertEqual(units["4R"][4], (F(1, 2), F(1)))

    def test_dropped_cap_leaf_cannot_claim_complete(self):
        tree = toy_primary()
        tree["leaves"].pop()
        with self.assertRaisesRegex(ValueError, "missing_leaf"):
            v.primary_structure(tree)

    def test_duplicate_boundary_leaf_rejected(self):
        tree = toy_primary()
        tree["leaves"].append(deepcopy(tree["leaves"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            v.primary_structure(tree)

    def test_false_inside_label_rejected(self):
        tree = toy_primary()
        tree["leaves"][0]["classification"] = "inside"
        with self.assertRaisesRegex(ValueError, "false_inside"):
            v.primary_structure(tree)

    def test_false_unit_box_rejected(self):
        tree = toy_primary()
        tree["leaves"][0]["unit_box"][4] = ["0", "1/3"]
        with self.assertRaisesRegex(ValueError, "terminal_box"):
            v.primary_structure(tree)

    def test_unreachable_tree_node_rejected(self):
        tree = toy_primary()
        tree["nodes"].append({"path": "rogue"})
        with self.assertRaisesRegex(ValueError, "missing_leaf"):
            v.primary_structure(tree)

    def test_independent_children_partition_contracted_parent(self):
        nodes, regions = v.independent_structure(toy_independent())
        self.assertEqual(len(nodes), 3)
        self.assertEqual(set(regions), {1, 2})

    def test_independent_split_gap_rejected(self):
        tree = toy_independent()
        tree["cover_tree"][2]["input_box"][0] = v.ind.I("3/4", 1).packet()
        tree["cover_tree"][2]["contracted_box"][0] = v.ind.I("3/4", 1).packet()
        with self.assertRaisesRegex(ValueError, "gap_or_overlap"):
            v.independent_structure(tree)

    def test_independent_missing_projection_rejected(self):
        tree = toy_independent()
        tree["paired_regions"].pop()
        with self.assertRaisesRegex(ValueError, "retained_projection"):
            v.independent_structure(tree)

    def test_halfspace_contractor_retains_all_legal_points(self):
        I = v.ind.I
        original = [I(-1, 1), I(-1, 1), I(0), I("1/4", 1), I(0, 1)]
        constraints = [{"name": "m_plus_z", "coefficients": [I(1), I(1), I(0), I(0), I(0)],
                        "lower": I("3/2").lo, "upper": None}]
        box, audit = v.audited_contract(original, constraints)
        comparison, independent = v.ind.linear_contract(original, constraints)
        v.same(box, comparison, "contractor")
        v.same(audit, independent, "trace")
        self.assertTrue(box[0].contains("3/4") and box[1].contains("3/4"))
        self.assertGreater(box[0].lo, original[0].lo)

    def test_negative_coefficient_projection_is_outer(self):
        I = v.ind.I
        original = [I(0, 1), I(0), I(0), I(1), I(0, 1)]
        constraints = [{"name": "minus_m", "coefficients": [I(-1), I(0), I(0), I(0), I(0)],
                        "lower": I("-1/2").lo, "upper": None}]
        box, _ = v.audited_contract(original, constraints)
        self.assertEqual(box[0], I(0, "1/2"))

    def test_zero_coefficient_never_divides(self):
        I = v.ind.I
        original = [I(0, 1), I(0), I(0), I(1), I(0, 1)]
        constraints = [{"name": "zero", "coefficients": [I(0)] * 5, "lower": 0, "upper": 0}]
        box, _ = v.audited_contract(original, constraints)
        self.assertEqual(box, original)

    def test_whole_halfspace_exclusion_has_strict_range(self):
        I = v.ind.I
        original = [I(0, 1), I(0), I(0), I(1), I(0, 1)]
        constraints = [{"name": "m_at_least_two", "coefficients": [I(1), I(0), I(0), I(0), I(0)],
                        "lower": I(2).lo, "upper": None}]
        box, proof = v.audited_contract(original, constraints)
        self.assertIsNone(box)
        self.assertEqual(proof["reason"], "strict_single_halfspace_violation")

    def test_all_training_CI_have_positive_width(self):
        report = v.read_json(v.HERE.parent.parent / "observable-prediction/public-comparison-po0003.json")
        ci = v.primary.ci_view(report)
        self.assertTrue(all(value.lo < value.hi for value in ci.values()))
        self.assertTrue(all(value.lo < value.hi for value in v.primary.training_domain(ci)))

    def test_heldout_does_not_change_training_view(self):
        report = v.read_json(v.HERE.parent.parent / "observable-prediction/public-comparison-po0003.json")
        before = v.ind.parse_training(json.dumps(report))
        for field in ("j", "sA_cell", "sB_cell"):
            for index in (1, 2):
                report["common_mean_confidence"][field][index]["exact_lower"] = "0"
                report["common_mean_confidence"][field][index]["exact_upper"] = "1/2"
        self.assertEqual(before, v.ind.parse_training(json.dumps(report)))

    def test_inverse_mean_center_cannot_cover_full_interval(self):
        with self.assertRaisesRegex(ValueError, "incomplete_inverse"):
            v.monotone_inverse_cover({"exact_lower": "1/1000", "exact_upper": "1/1000"},
                                     {"exact_lower": "0", "exact_upper": "1/100"}, F(0))


if __name__ == "__main__":
    unittest.main()
