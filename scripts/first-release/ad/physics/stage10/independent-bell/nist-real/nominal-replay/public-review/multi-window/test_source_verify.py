"""Frozen source-cross structural and certificate intake controls."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import source_verify as check


class SourceCrossControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cfg, _, _ = check.configuration()
        cls.a, _ = check.load_first("primary")
        cls.b, _ = check.load_first("independent")

    def test_full_shapes_positive(self):
        check.primary_shape(self.a, self.cfg)
        check.independent_shape(self.b, self.cfg)

    def test_wrong_count_lookalike(self):
        bad = {**self.b, "cover": {**self.b["cover"], "node_count": self.b["cover"]["node_count"] - 1}}
        with self.assertRaisesRegex(ValueError, "wrong_node_split_or_leaf_count"):
            check.independent_shape(bad, self.cfg)

    def test_primary_leaf_drop(self):
        bad = {**self.a, "cover": {**self.a["cover"], "leaves": self.a["cover"]["leaves"][:-1]}}
        with self.assertRaisesRegex(ValueError, "wrong_node_split_or_leaf_count"):
            check.primary_shape(bad, self.cfg)

    def test_independent_paired_leaf_drop(self):
        bad = {**self.b, "cover": {**self.b["cover"], "paired_regions": self.b["cover"]["paired_regions"][:-1]}}
        with self.assertRaisesRegex(ValueError, "missing_leaf_projection_or_wrong_count"):
            check.independent_shape(bad, self.cfg)

    def test_phase_after_window_flag_rejected(self):
        packet = self.a["members"][0]["native_Fock"]
        check.native_born_flags(packet)
        with self.assertRaisesRegex(ValueError, "wrong_phase_order"):
            check.native_born_flags({**packet, "phase_mixture_before_window": False})

    def test_source_first_copy_override(self):
        with tempfile.TemporaryDirectory() as directory:
            copy_path = Path(directory) / "copied.xz"
            copy_path.write_bytes((check.HERE / "source-primary-first.json.xz").read_bytes())
            report, _ = check.load_first("primary", copy_path)
            check.primary_shape(report, self.cfg)

    def test_source_first_lookalike_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            bad = Path(directory) / "lookalike.xz"
            bad.write_bytes(b"same plausible schema different bytes")
            with self.assertRaisesRegex(ValueError, "lookalike_source_first"):
                check.load_first("primary", bad)

    def test_readonly_intake_default_copy_disable_lookalike_from_NIST(self):
        nist = check.HERE.parents[2]
        driver = str(check.HERE / "source_verify.py")
        canonical = check.HERE / "source-cross-verification.json"
        with tempfile.TemporaryDirectory() as directory:
            copied = Path(directory) / "copied.json"; copied.write_bytes(canonical.read_bytes())
            bad = Path(directory) / "lookalike.json"
            value = json.loads(canonical.read_text()); value["trees"]["primary"]["nodes_recomputed"] -= 1
            bad.write_text(json.dumps(value))
            for flags, code, valid in (([], 0, True), (["--certificate", str(copied)], 0, True),
                (["--certificate", str(bad)], 1, False), (["--disabled", "--certificate", str(Path(directory)/"missing.json")], 0, False)):
                process = subprocess.run([sys.executable, driver, "--check-only", *flags], cwd=nist, text=True, capture_output=True)
                self.assertEqual(process.returncode, code, process.stderr)
                row = json.loads(process.stdout)
                self.assertIs(row["evidence_valid"], valid)
                self.assertEqual(row["schema"], check.EVIDENCE_SCHEMA)
                if valid:
                    self.assertIs(row["no_tree_Fock_statistics_or_search_rerun"], True)
                else:
                    self.assertTrue(row["reason"])


if __name__ == "__main__":
    unittest.main()
