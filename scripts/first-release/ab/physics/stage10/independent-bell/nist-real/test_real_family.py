"""Synthetic-only regressions. No experimental event or count files are opened."""
import copy
import json
import math
import random
import subprocess
import sys
import unittest
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import predict
import real_family as rf
from checks import matrix_born, control_loop

BASELINE_BLOB = "1871b5768c7a7c1fdc49dc3fd79eaad0412b75d2"


class RealFamilyTests(unittest.TestCase):
    def setUp(self):
        self.instrument = json.loads((HERE / "instrument.json").read_text())

    def test_generic_matrix_and_marginals(self):
        rng = random.Random(20260918)
        for _ in range(200):
            t, a, b = [rng.uniform(-math.pi, math.pi) for _ in range(3)]
            c, s, d, k = rf.parameters(math.cos(t), math.sin(t))
            ax, bx = (math.sin(2*a), math.cos(2*a)), (math.sin(2*b), math.cos(2*b))
            p = rf.born_probabilities(ax, bx, d, k)
            for u, v in zip(p, matrix_born(c, s, a, b)):
                self.assertAlmostEqual(u, v, places=13)
            self.assertAlmostEqual(p[0]+p[1], (1+d*ax[1])/2, places=13)
            self.assertAlmostEqual(p[0]+p[2], (1+d*bx[1])/2, places=13)
            self.assertAlmostEqual(sum(p), 1, places=13)
            self.assertGreaterEqual(min(p), -1e-14)

    def test_v1_exact_regression(self):
        code = subprocess.check_output(["git", "show", BASELINE_BLOB], cwd=HERE, text=True)
        baseline = {}
        exec(compile(code, "legacy-predict.py", "exec"), baseline)
        fixture = {"alice_axes_xz": [[0, 1], [1, 0]],
                   "bob_axes_xz": [[0.6, 0.8], [-0.8, 0.6]]}
        self.assertEqual(predict.tables(fixture), baseline["tables"](fixture))
        fixture["independent_calibration"] = {"provenance": "synthetic-only",
            "test_events_disjoint": True, "visibility": 0.8,
            "F0_A": 0.9, "F1_A": 0.7, "F0_B": 0.8, "F1_B": 0.95}
        self.assertEqual(predict.tables(fixture), baseline["tables"](fixture))

    def test_maximal_legacy_frame(self):
        a, b = (0.6, 0.8), (-0.8, 0.6)
        p = rf.born_probabilities(a, (b[0], -b[1]), 0, 1)
        expected = [(1+x*y*(a[0]*b[0]-a[1]*b[1]))/4 for x, y in rf.OUTCOMES]
        for u, v in zip(p, expected):
            self.assertAlmostEqual(u, v, places=14)

    def test_nist_control_loop(self):
        report = control_loop(self.instrument, nominal_replay_enabled=False)
        for name in ("matrix_matches_all_cells", "mirror_geometry", "real_shape",
                     "rare_vertical_transmission", "primed_destructive_structure",
                     "wrong_basis_rejected", "wrong_bob_sign_rejected"):
            self.assertTrue(report[name], name)
        self.assertFalse(report["apparatus_optimum_verified"])
        self.assertEqual(predict.tables(self.instrument), rf.tables(self.instrument))

    def test_wrong_schemas_rejected(self):
        mutations = [("claim_scope", "source_theory"), ("detector_geometry", "two_ports")]
        for key, value in mutations:
            bad = copy.deepcopy(self.instrument)
            bad[key] = value
            with self.assertRaises(ValueError):
                rf.tables(bad)
        bad = copy.deepcopy(self.instrument)
        bad["preparation"]["basis_order"] = ["H", "V"]
        with self.assertRaises(ValueError):
            rf.tables(bad)
        with self.assertRaises(ValueError):
            rf.born_probabilities((0, 1), (1, 0), 0.5, 0.5)
        with self.assertRaises(ValueError):
            rf.parameters(0, 0)
        with self.assertRaises(ValueError):
            rf.parameters(float("nan"), 1)

    def test_loss_extends_assignment(self):
        for u in (-1, 1):
            k = rf.loss_assignment(u, eta_plus=1, eta_minus=1, F0=0.8, F1=0.7)
            self.assertAlmostEqual(k[u], 0.8 if u == 1 else 0.7)
            self.assertAlmostEqual(sum(k.values()), 1)
            self.assertAlmostEqual(k[0], 0)
        single = dict(eta_plus=0.75, eta_minus=0, F0=1, F1=1, background=0)
        self.assertEqual(rf.binary_assignment(-1, single), {1: 0, -1: 1})
        self.assertEqual(rf.binary_assignment(1, single), {1: 0.75, -1: 0.25})
        zero = dict(eta_plus=0, eta_minus=0, F0=0.4, F1=0.2, background=0)
        self.assertEqual(rf.binary_assignment(1, zero), {1: 0, -1: 1})

    def test_trial_mass_vacuum_and_pair(self):
        side = dict(eta_plus=1, eta_minus=1, F0=1, F1=1, background=0)
        channel = dict(pair_probability=1, visibility=1, alice=side, bob=side)
        ideal = rf.born_probabilities((0, 1), (0.6, 0.8), -7/25, 24/25)
        self.assertEqual(rf.trial_probabilities(ideal, channel), ideal)
        channel["pair_probability"] = 0
        self.assertEqual(rf.trial_probabilities(ideal, channel), [0, 0, 0, 1])
        rng = random.Random(13)
        for _ in range(100):
            channel = {"pair_probability": rng.random(), "visibility": rng.random()}
            for name in ("alice", "bob"):
                channel[name] = {k: rng.random() for k in side}
            observed = rf.trial_probabilities(ideal, channel)
            self.assertAlmostEqual(sum(observed), 1, places=13)
            self.assertGreaterEqual(min(observed), 0)

    def test_budget_and_transport(self):
        request = json.loads((HERE / "request.json").read_text())
        budget = rf.error_budget(request["error_budget"])
        self.assertEqual(budget["covered_total"], "7/200")
        self.assertEqual(budget["reserve_unused"], "3/200")
        bounds = {k: "1/1000" for k in rf.RADIUS_KEYS}
        self.assertEqual(rf.transport_radius(bounds), Fraction(len(bounds), 1000))
        bounds["state_tv"] = "-1/10"
        with self.assertRaises(ValueError):
            rf.transport_radius(bounds)
        with self.assertRaises(ValueError):
            rf.transport_radius({})

    def test_channel_does_not_signal(self):
        a = (0.6, 0.8)
        channel = dict(pair_probability=0.4, visibility=0.9,
            alice=dict(eta_plus=0.7, eta_minus=0, F0=0.8, F1=0.9, background=0.01),
            bob=dict(eta_plus=0.6, eta_minus=0, F0=0.7, F1=0.8, background=0.02))
        outputs = [rf.trial_probabilities(rf.born_probabilities(a, b, -7/25, 24/25), channel)
                   for b in ((0, 1), (1, 0))]
        self.assertAlmostEqual(sum(outputs[0][:2]), sum(outputs[1][:2]), places=13)


if __name__ == "__main__":
    unittest.main()
