"""Focused source, phase, coverage, and information-role controls for ef0003."""
import copy
from fractions import Fraction as F
import gzip
import json
import unittest

import independent_fiber as m


class IndependentFiberTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.config = m.configuration()[0]
        cls.const = m.constants(cls.config)

    def test_directed_integer_arithmetic_contains_exact_values(self):
        a, b = m.I(F(1, 3)), m.I(F(-2, 7))
        self.assertTrue((a+b).contains(F(1, 21)))
        self.assertTrue((a*b).contains(F(-2, 21)))
        self.assertTrue((a/b).contains(F(-7, 6)))
        self.assertTrue(m.I(-2, 3).square().contains(0))
        self.assertTrue(m.I(2).sqrt().square().contains(2))
        with self.assertRaisesRegex(ValueError, "division_through_zero"):
            a/m.I(-1, 1)

    def test_exact_confidence_endpoint_is_not_rounded_outward_for_acceptance(self):
        packet = {"exact_lower":"1/3", "exact_upper":"2/3"}
        self.assertFalse(m.unpack(packet).within_exact(packet))
        self.assertTrue(m.I(F(1, 2)).within_exact(packet))

    def test_binomial_fifth_root_and_remainder(self):
        for value in (F(-1, 1000), F(1, 1000), F(0)):
            root = 1+m.fifth_root_delta(m.I(value), self.config)
            self.assertTrue(root.power(5).contains(1+value))
        with self.assertRaisesRegex(ValueError, "binomial_input_outside"):
            m.fifth_root_delta(m.I(F(1, 10)), self.config)

    def test_training_parser_never_decodes_heldout_probability_values(self):
        packet = {"exact_lower":"1/10000", "exact_upper":"2/10000"}
        nonsense = {"exact_lower":"never decode", "exact_upper":"also unread"}
        report = {"common_mean_confidence":{key:[packet, nonsense, nonsense, packet] for key in ("sA_cell", "sB_cell", "j")}}
        first = m.parse_training(json.dumps(report))
        for key in report["common_mean_confidence"]:
            report["common_mean_confidence"][key][1] = {"arbitrary_heldout_structure":[1, 2, 3]}
        self.assertEqual(first, m.parse_training(json.dumps(report)))
        self.assertEqual(len(first), 6)

    def test_halfspace_contractor_is_outer_and_preserves_a_valid_source(self):
        box = [m.I(0, 1), m.I(0, 1), m.I(0, 1), m.I(1, 2), m.I(F(1, 10), F(9, 10))]
        constraints = [{"name":"m interval", "coefficients":[m.I(1), m.I(0), m.I(0), m.I(0), m.I(0)],
                        "lower":m.I(F(1, 5)).lo, "upper":m.I(F(2, 5)).hi}]
        contracted, certificate = m.linear_contract(box, constraints)
        self.assertTrue(contracted[0].contains(F(1, 3)))
        self.assertTrue(all(a.contained(b) for a, b in zip(contracted, box)))
        self.assertGreater(certificate["update_count"], 0)
        constraints[0]["lower"] = m.I(2).lo
        self.assertIsNone(m.linear_contract(box, constraints)[0])

    def sample_tree(self):
        root = [m.I(0, 1)]*5
        left, right = list(root), list(root)
        left[0], right[0] = m.I(0, F(1, 2)), m.I(F(1, 2), 1)
        nodes = [{"id":0, "parent":None, "depth":0, "input_box":root, "contracted_box":root,
                  "status":"split", "split_axis":"m", "children":[1, 2]},
                 {"id":1, "parent":0, "depth":1, "input_box":left, "contracted_box":left, "status":"retained_boundary"},
                 {"id":2, "parent":0, "depth":1, "input_box":right, "contracted_box":right, "status":"retained_boundary"}]
        return root, nodes, [{"node_id":1}, {"node_id":2}]

    def test_complete_tree_positive_and_missing_leaf_negative(self):
        root, nodes, regions = self.sample_tree()
        self.assertTrue(m.verify_tree(nodes, root, regions))
        with self.assertRaisesRegex(ValueError, "missing_cover_child"):
            m.verify_tree(nodes[:-1], root, regions)

    def test_duplicate_boundary_and_nonsplit_axis_negative(self):
        root, nodes, regions = self.sample_tree()
        with self.assertRaisesRegex(ValueError, "missing_or_duplicate_retained_projection"):
            m.verify_tree(nodes, root, regions+[regions[0]])
        altered = copy.deepcopy(nodes)
        altered[2]["input_box"][1] = m.I(0, F(9, 10))
        with self.assertRaisesRegex(ValueError, "changed_nonsplit_axis"):
            m.verify_tree(altered, root, regions)

    def test_zero_coupling_and_pure_mode_are_not_divided_out(self):
        control_config = {**self.config, "angles_deg":["0", "90", "0", "90"]}
        const = m.constants(control_config)
        box = [m.I(".001"), m.I(".001"), m.I(0), m.I(1), m.I(".75")]
        pop = m.population(box)
        geo = m.geometry(box, pop, const, 0)
        self.assertEqual(geo["g"], m.I(0))
        source = m.physical_source(box, m.I(0))
        self.assertTrue(source["pure_mode_phase_equivalence"])
        self.assertEqual(source["coherence"], m.I(-1, 1))

    def test_positive_occupation_Born_matches_full_law(self):
        box = [m.I(".0015"), m.I(".0005"), m.I(0), m.I(1), m.I(".75")]
        source = m.physical_source(box, m.I(0))
        actual = m.fock_readout(source, self.const)
        pop = m.population(box)
        for row in range(4):
            expected = m.cell_readout(m.geometry(box, pop, self.const, row), m.I(0), self.const)
            for field in ("sA", "sB", "j"):
                self.assertIsNotNone(actual["cells"][row][field].intersect(expected[field]))
        self.assertTrue(actual["vacuum_clicked_Born_exactly_zero"])
        self.assertFalse(actual["finite_prefix_renormalized"])

    def test_same_source_no_signaling_readout(self):
        box = [m.I(".0015"), m.I(".0005"), m.I(0), m.I(1), m.I(".75")]
        pop = m.population(box)
        rows = [m.cell_readout(m.geometry(box, pop, self.const, i), m.I(0), self.const) for i in range(4)]
        self.assertEqual(rows[0]["sA"], rows[1]["sA"])
        self.assertEqual(rows[2]["sA"], rows[3]["sA"])
        self.assertEqual(rows[0]["sB"], rows[2]["sB"])
        self.assertEqual(rows[1]["sB"], rows[3]["sB"])

    def test_phase_after_window_is_a_different_model(self):
        control_config = {**self.config, "angles_deg":["45", "45", "45", "45"]}
        const = m.constants(control_config)
        box = [m.I(".0015"), m.I(".0005"), m.I(0), m.I(1), m.I(".75")]
        source = m.physical_source(box, m.I(0))
        correct = m.fock_readout(source, const)
        wrong = m.fock_readout(source, const, phase_after_window=True)
        self.assertIsNone(correct["cells"][0]["j"].intersect(wrong["cells"][0]["j"]))
        self.assertFalse(wrong["phase_mixture_before_window"])

    def test_illegal_loss_and_phase_rejected(self):
        box = [m.I(".0015"), m.I(".0005"), m.I(0), m.I(1), m.I("1.01")]
        with self.assertRaisesRegex(ValueError, "member_loss_not_legal"):
            m.physical_source(box, m.I(0))
        box[-1] = m.I(".75")
        with self.assertRaisesRegex(ValueError, "member_phase_not_legal"):
            m.physical_source(box, m.I(1))

    def test_six_CI_member_and_wrong_joint_control(self):
        box = [m.I(".0015"), m.I(".0005"), m.I(0), m.I(1), m.I(".75")]
        pop = m.population(box)
        cells = [m.cell_readout(m.geometry(box, pop, self.const, i), m.I(0), self.const) for i in range(4)]
        training = {}
        for field, row in m.FIELDS:
            name = {"sA_cell":"sA", "sB_cell":"sB", "j":"j"}[field]
            center = cells[row][name].midpoint()
            training[field+"["+str(row)+"]"] = {"exact_lower":str(center-F(1, 10**8)), "exact_upper":str(center+F(1, 10**8))}
        means = m.training_means(training, self.config)
        member = m.legal_member(training, means, [], [], box[:-1], F(3, 4), "midpoint", F(0), self.const, self.config)
        self.assertTrue(member["all_six_training_CI_contained"])
        self.assertEqual(len(member["Gaussian_positive_Fock_cross"]), 12)
        training["j[3]"] = {"exact_lower":"1/2", "exact_upper":"3/4"}
        with self.assertRaisesRegex(ValueError, "member_actual_Born_training_CI_not_contained"):
            m.legal_member(training, means, [], [], box[:-1], F(3, 4), "midpoint", F(0), self.const, self.config)

    def test_first_qualified_members_survive_retained_source_and_phase_cover(self):
        path = m.HERE/"independent-ef0003.json.gz"
        if not path.exists():
            self.skipTest("first science receipt is not available")
        report = json.loads(gzip.decompress(path.read_bytes()))
        stage = report["source_stage"]
        regions = [(list(map(m.unpack, region["source_box"])), m.unpack(region["common_k"]))
                   for region in stage["paired_regions"]]
        self.assertEqual(len(regions), stage["coverage"]["retained_leaf_count"])
        for member in stage["members"]:
            box = list(map(m.unpack, member["source_box"]))
            phase = m.unpack(member["source"]["common_k"])
            survives = any(all(a.intersect(b) is not None for a, b in zip(box, region)) and phase.intersect(k) is not None
                           for region, k in regions)
            self.assertTrue(survives, "qualified source was removed from cover: "+str(member["id"]))


if __name__ == "__main__":
    unittest.main()
