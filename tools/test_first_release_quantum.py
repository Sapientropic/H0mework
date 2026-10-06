"""Verify strict scientific comparison and original-main/source isolation."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import first_release_quantum as quantum
from first_release_replay import PublicInputs, ReplayError, sha


class QuantumResults(unittest.TestCase):
    def test_only_top_level_wall_clock_can_change(self):
        frozen = {"elapsed_seconds": 20.0, "time": [2, 0, 0, 0],
                  "verdict": "CERTIFIED", "nonzero_control": True,
                  "negative_result": False, "nested": {"elapsed_seconds": 3}}
        actual = copy.deepcopy(frozen)
        actual["elapsed_seconds"] = 99.0
        quantum.compare_results(frozen, actual)
        for pointer, replacement in [("time", [3, 0, 0, 0]),
                                     ("verdict", "FAILED"), ("negative_result", True),
                                     ("nonzero_control", 1),
                                     ("nested", {"elapsed_seconds": 4})]:
            changed = copy.deepcopy(actual)
            changed[pointer] = replacement
            with self.subTest(pointer=pointer), self.assertRaises(ReplayError):
                quantum.compare_results(frozen, changed)

    def fixture(self, directory, extra=""):
        root = directory / "view"
        root.mkdir()
        program = root / "independent.py"
        program.write_text("from pathlib import Path\nimport json\n"
                           "def main():\n" + extra +
                           "    Path(__file__).with_suffix('.json').write_text(json.dumps("
                           "{'verdict':'CERTIFIED','time':[2,0,0,0],"
                           "'negative_result':False,'elapsed_seconds':0.1}))\n")
        producer = root / "source.py"
        producer.write_text("def original_coefficient(): return 2\n")
        paths = {name: {"view_sha256": sha((root / name).read_bytes()),
                        "source_sha256": sha((root / name).read_bytes())}
                 for name in ("independent.py", "source.py")}
        check = {"id": "k3-scalar-gauss", "program": "independent.py",
                 "program_sha256": paths["independent.py"]["source_sha256"],
                 "producer": {"program": "source.py", "source_sha256": paths["source.py"]["source_sha256"]},
                 "output": "independent.json", "ref": quantum.REVISIONS["T"],
                 "subclaim": "K3", "expected_verdict": "CERTIFIED", "scope_fields": ["time", "negative_result"],
                 "frozen_sha256": "f" * 64}
        frozen = {"verdict": "CERTIFIED", "time": [2, 0, 0, 0],
                  "negative_result": False, "elapsed_seconds": 10.0}
        output = directory / "result"
        output.mkdir()
        return PublicInputs(root, paths), check, output, frozen

    def test_original_nullary_main_produces_fresh_result(self):
        with tempfile.TemporaryDirectory() as name:
            inputs, check, output, frozen = self.fixture(Path(name))
            result = quantum.execute_original(inputs, check, output, frozen)
            self.assertTrue(result["original_independent_main_executed"])
            self.assertEqual(result["actual_scope"]["time"], [2, 0, 0, 0])
            self.assertFalse(result["actual_scope"]["negative_result"])
            self.assertTrue((output / "result.json").is_file())

    def test_original_main_cannot_change_a_verified_source(self):
        with tempfile.TemporaryDirectory() as name:
            extra = "    Path(__file__).with_name('source.py').write_text('changed')\n"
            inputs, check, output, frozen = self.fixture(Path(name), extra)
            with self.assertRaisesRegex(ReplayError, "Source-view input changed"):
                quantum.execute_original(inputs, check, output, frozen)

    def test_worker_rejects_ambient_file_fallback(self):
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            task = directory / "task"
            task.mkdir()
            external = directory / "unregistered-input.txt"
            external.write_text("outside source view")
            extra = f"    Path({str(external)!r}).read_text()\n"
            inputs, check, _, frozen = self.fixture(task, extra)
            snapshot = task / "map.json"
            snapshot.write_text("{}")
            frozen_path = task / "frozen.json"
            frozen_path.write_text(json.dumps(frozen))
            check["frozen_sha256"] = sha(frozen_path.read_bytes())
            output = task / "worker-result"
            spec = task / "worker.json"
            spec.write_text(json.dumps({"check": check, "output": str(output),
                "view": {"root": str(inputs.root), "bindings": inputs.bindings},
                "map_snapshot": str(snapshot), "map_sha256": sha(snapshot.read_bytes()),
                "frozen_snapshot": str(frozen_path)}))
            result = subprocess.run([sys.executable, str(Path(quantum.__file__).resolve()),
                                     "_worker", str(spec)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 1, result.stderr)
            receipt = json.loads((output / "execution.json").read_text())
            self.assertEqual(receipt["status"], "failed")
            self.assertIn("outside its explicit public inputs", receipt["error"])


if __name__ == "__main__":
    unittest.main()
