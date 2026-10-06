"""Synthetic protocol checks; no new archival outcomes are used."""

import itertools
import math
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from analyze import analyze
from predict import tables


INSTRUMENT = {"alice_axes_xz": [[0, 1], [1, 0]],
              "bob_axes_xz": [[1/math.sqrt(2), 1/math.sqrt(2)],
                              [-1/math.sqrt(2), 1/math.sqrt(2)]]}
TRIAL = {"herald": -1, "a": 0, "b": 0, "x": 1, "y": -1}


class FamilyTests(unittest.TestCase):
    def test_ideal_matches_closed_bell_correlations(self):
        models = tables(INSTRUMENT)["models"]
        self.assertEqual([m["id"] for m in models], ["ideal_source"])
        for row in models[0]["table"]:
            ax, az = INSTRUMENT["alice_axes_xz"][row["a"]]
            bx, bz = INSTRUMENT["bob_axes_xz"][row["b"]]
            correlation = (row["herald"]*ax*bx-az*bz)
            p = row["probabilities"]
            self.assertAlmostEqual(sum(p), 1)
            self.assertAlmostEqual(p[0]+p[3]-p[1]-p[2], correlation)
            self.assertAlmostEqual(p[0]+p[1], .5)

    def test_explicit_independent_calibration_and_alpha(self):
        instrument = {**INSTRUMENT, "independent_calibration": {
            "visibility": 0, "F0_A": 1, "F1_A": 1, "F0_B": 1, "F1_B": 1,
            "provenance": "synthetic independent calibration fixture",
            "test_events_disjoint": True}}
        result = analyze([TRIAL], instrument)
        self.assertEqual(len(result["models"]), 2)
        self.assertEqual(result["models"][1]["alpha"], .025)
        for row in result["predictions"]["models"][1]["table"]:
            self.assertEqual(row["probabilities"], [.25]*4)
        self.assertEqual(analyze([TRIAL], INSTRUMENT)["models"][0]["alpha"], .025)

    def test_target_fitted_calibration_is_rejected(self):
        instrument = {**INSTRUMENT, "independent_calibration": {
            "visibility": .99, "provenance": "target fit", "test_events_disjoint": False}}
        with self.assertRaises(ValueError):
            tables(instrument)

    def test_invalid_axis_is_rejected(self):
        with self.assertRaises(ValueError):
            tables({**INSTRUMENT, "alice_axes_xz": [[0, 2], [1, 0]]})

    def test_cap_does_not_read_following_outcome(self):
        def stream():
            yield from itertools.repeat(TRIAL, 3)
            raise AssertionError("read beyond the predeclared cap")
        with patch("analyze.TRIAL_CAP", 3):
            result = analyze(stream(), INSTRUMENT)
        self.assertEqual(result["models"][0]["n_trials"], 3)

    def test_empty_and_invalid_streams_do_not_get_verdict(self):
        with self.assertRaises(ValueError):
            analyze([], INSTRUMENT)
        with self.assertRaises(ValueError):
            analyze([{**TRIAL, "x": 0}], INSTRUMENT)


if __name__ == "__main__":
    unittest.main()
