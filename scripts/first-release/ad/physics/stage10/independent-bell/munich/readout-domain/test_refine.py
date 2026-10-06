"""The candidate revision preserves exact prefix inference and exclusive receipts."""
from fractions import Fraction
import itertools
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from model import Effect, Instrument, encode
import refine
import refine_independent


def admitted():
    trials = [SimpleNamespace(row=n, time_ms=Fraction(n), row_a=n, row_b=n, h=h, a=a, b=b, x=x, y=y)
              for n, (h, a, b, x, y) in enumerate(itertools.product((0, 1), repeat=5), 1)]
    return SimpleNamespace(run=refine.RUNS[0], trials=trials, token_dictionaries={},
                           audit={"pair_records": 32, "original_pair_order_preserved": True,
                                  "all_pairs_joined": True, "additional_outcome_selection": False})


class RefinementControls(unittest.TestCase):
    def test_candidate_is_still_scored_by_complete_exact_prefix_checker(self):
        event_run = admitted()
        summary = refine.baseline.summarize(event_run)
        point = Instrument((Effect(0, 0, 0),) * 2, (Effect(0, 0, 0),) * 2)
        with patch.object(refine.candidate, "search_terminal", return_value=({"primitive": encode(point)},)):
            result = refine.certify_run(event_run, summary)
        self.assertTrue(result["all_prefixes_below_threshold_certified"])
        self.assertEqual(result["prefix_check"]["trials"], 32)
        self.assertEqual(result["candidate_revision"], "c0002")

    def test_terminal_candidate_does_not_sign_bad_point(self):
        event_run = admitted()
        point = Instrument((Effect("9/10", 0, 0),) * 2, (Effect("9/10", 0, 0),) * 2)
        with patch.object(refine.candidate, "search_terminal", return_value=({"primitive": encode(point)},)):
            result = refine.certify_run(event_run, refine.baseline.summarize(event_run))
        self.assertFalse(result["all_prefixes_below_threshold_certified"])
        self.assertEqual(result["status"], "unresolved")
        self.assertFalse(result["global_domain_rejection_claimed"])

    def test_primary_override_cannot_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / "primary-first-c0002.json").write_text("preserved")
            with patch.object(refine, "snapshot", side_effect=AssertionError("source access")), self.assertRaises(ValueError):
                refine.execute(path, "abcdef0", path)
            self.assertEqual((path / "primary-first-c0002.json").read_text(), "preserved")

    def test_independent_override_cannot_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / "independent-first-c0002.json").write_text("preserved")
            with patch.object(refine_independent.checker, "execution_provenance", side_effect=AssertionError("source access")), self.assertRaises(ValueError):
                refine_independent.execute(path, path / "witness.json", "abcdef0", path)
            self.assertEqual((path / "independent-first-c0002.json").read_text(), "preserved")


if __name__ == "__main__":
    unittest.main()
