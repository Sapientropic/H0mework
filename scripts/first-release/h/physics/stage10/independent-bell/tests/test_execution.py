import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
from zipfile import ZipFile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import run
from predict import tables
from reader import MEMBER


INSTRUMENT = {"alice_axes_xz": [[0,1],[1,0]], "bob_axes_xz": [[0,1],[1,0]]}


class ExecutionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.base = Path(self.temporary.name)
        self.lock = {"code_commit":"synthetic", "archive":{"local_path":"raw.zip","sha256":"synthetic"},
                     "claim_scope":"synthetic", "outcome_role":"L0 fixture"}
        for name, value in (("instrument.json",INSTRUMENT),("predictions.json",tables(INSTRUMENT))):
            (self.base/name).write_text(json.dumps(value))
        self.patches = [patch.object(run.freeze,"BASE",self.base),
                        patch.object(run.freeze,"REPO",self.base),
                        patch.object(run.freeze,"verify",return_value=self.lock)]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.temporary.cleanup()

    def test_failed_first_open_preserves_exposure(self):
        with self.assertRaises(FileNotFoundError):
            run.execute("fixture")
        path = self.base/"evidence/access.json"
        first = path.read_bytes()
        with self.assertRaises(FileExistsError):
            run.execute("fixture")
        self.assertEqual(path.read_bytes(),first)

    def test_wrong_prediction_table_blocks_before_access(self):
        (self.base/"predictions.json").write_text('{}')
        with self.assertRaises(ValueError):
            run.execute("fixture")
        self.assertFalse((self.base/"evidence/access.json").exists())

    def test_invalid_lock_blocks_before_access(self):
        with patch.object(run.freeze,"verify",side_effect=ValueError("bad lock")):
            with self.assertRaises(ValueError):
                run.execute("fixture")
        self.assertFalse((self.base/"evidence/access.json").exists())

    def test_complete_result_replays_without_overwrite(self):
        with ZipFile(self.base/"raw.zip","w") as archive:
            archive.writestr(MEMBER,"synthetic\ncolumns\n\n0,1,0,-1\n1,1,1,-1")
        result = run.execute("fixture")
        path = self.base/"evidence/results.json"
        first = path.read_bytes()
        self.assertEqual(run.execute("fixture"),result)
        self.assertEqual(path.read_bytes(),first)
        self.assertEqual(result["models"][0]["n_trials"],2)


if __name__ == "__main__":
    unittest.main()
