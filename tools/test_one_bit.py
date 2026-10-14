import gzip
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

import one_bit


class OneBitIdentityTests(unittest.TestCase):
    def document(self, claims):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "docs").mkdir()
            (root / one_bit.MAP).write_text(json.dumps({"schema": one_bit.SCHEMA, "claims": claims}))
            return one_bit.document(root)

    def test_complete_selection_and_similar_or_missing_claim(self):
        claims = [{"id": f"OB{i}"} for i in range(1, 12)]
        self.assertEqual(len(self.document(claims)["claims"]), 11)
        for changed in (claims[:-1], [{"id": "OB01"}, *claims[1:]], [claims[0], *claims[:-1]]):
            with self.assertRaises(one_bit.release.ReleaseError):
                self.document(changed)

    def test_compressed_receipt_checks_stored_and_complete_payload_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            raw = b'{"status":"passed","result":17}\n'
            stored = gzip.compress(raw, mtime=0)
            (root / "receipt.json.gz").write_bytes(stored)
            reference = {"path": "receipt.json.gz", "compression": "gzip",
                         "sha256": one_bit.release.sha(stored), "payload_sha256": one_bit.release.sha(raw)}
            self.assertEqual(one_bit.artifact(root, reference)["result"], 17)
            for key in ("sha256", "payload_sha256"):
                with self.assertRaises(one_bit.release.ReleaseError):
                    one_bit.artifact(root, {**reference, key: "0" * 64})

    def test_diagnostic_metadata_cannot_replace_complete_trust(self):
        run = {"exit_code": 0, "audit": {"full_metadata": True, "unsafe": 0,
                                         "partial": 0, "axioms": ["propext"]}}
        one_bit.trusted(run)
        for change in ({"full_metadata": False}, {"unsafe": 1}, {"partial": 1},
                       {"axioms": ["sorryAx"]}):
            with self.assertRaises(one_bit.release.ReleaseError):
                one_bit.trusted({**run, "audit": {**run["audit"], **change}})
        with self.assertRaises(one_bit.release.ReleaseError):
            one_bit.trusted({**run, "exit_code": 1})


@unittest.skipUnless(shutil.which("make"), "Reader commands require make")
class OneBitReaderCommandsTests(unittest.TestCase):
    def outputs(self, *arguments):
        run = subprocess.run(["make", "-n", *arguments], cwd=one_bit.release.ROOT,
                             text=True, capture_output=True, check=True)
        return re.findall(r"--output\s+([^\s]+)", run.stdout)

    def test_default_run_and_explicit_override_share_four_steps(self):
        outputs = self.outputs("check-one-bit-full")
        self.assertEqual(len(outputs), 4)
        self.assertEqual(len({p.rsplit("/", 1)[0] for p in outputs}), 1)
        self.assertEqual(self.outputs("check-one-bit-full", "ONE_BIT_RUN=.local/explicit-one-bit"),
                         [".local/explicit-one-bit/" + step for step in ("entry", "build", "trust", "types")])

    def test_whole_ledger_command_keeps_its_original_edition(self):
        outputs = self.outputs("check-whole-ledger-full", "WLA_RUN=.local/existing-ledger",
                               "ONE_BIT_RUN=.local/explicit-one-bit")
        self.assertEqual(outputs, [".local/existing-ledger/" + step
                                   for step in ("entry", "build", "trust", "types")])


if __name__ == "__main__":
    unittest.main()
