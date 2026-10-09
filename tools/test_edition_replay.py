import hashlib
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest

import edition_replay as edition
import first_release_replay as replay


class BellReplayTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.epoch, self.freeze = "a" * 40, "b" * 40
        self.name = "Verification/source.py"
        self.raw = b"def mathematical_result(x):\n    return x * x\n"
        self.bindings = {}
        self.add(self.name, self.raw)
        self.receipt = "Verification/first.json"
        self.add(self.receipt, json.dumps({"scientific_freeze_commit": self.freeze,
                                         "source_bindings": {self.name: replay.sha(self.raw)}}).encode())
        self.provider = edition.BellBindings(replay.PublicInputs(self.root, self.bindings), set(self.bindings))

    def add(self, name, raw):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        digest = hashlib.sha256(raw).hexdigest()
        self.bindings[name] = {"view_sha256": digest, "source_sha256": digest,
                               "source_revision": self.epoch, "source_revisions": [self.epoch]}

    def command(self, commit=None, name=None):
        return ["git", "-C", str(self.root), "show", (commit or self.freeze) + ":" + (name or self.name)]

    def test_original_receipt_registers_its_exact_science_freeze(self):
        self.assertEqual(self.provider.git_blob(self.command()), self.raw)
        used = list(self.provider.used.values())
        self.assertEqual(used[0]["commit"], self.freeze)
        self.assertFalse(used[0]["Git_ancestry_replayed"])

    def test_head_reads_the_verified_export_epoch(self):
        self.assertEqual(self.provider.git_blob(self.command("HEAD")), self.raw)
        self.assertEqual(list(self.provider.used.values())[0]["commit"], self.epoch)

    def test_unknown_freeze_changed_bytes_and_unselected_path_are_rejected(self):
        for command in (self.command("c" * 40), self.command(name="Verification/unselected.py")):
            with self.assertRaises(replay.ReplayError):
                self.provider.git_blob(command)
        (self.root / self.name).write_bytes(self.raw + b"# changed\n")
        with self.assertRaises(replay.ReplayError):
            self.provider.git_blob(self.command())

    def test_no_git_ancestry_or_producer_process_is_supplied(self):
        for command in (["git", "-C", str(self.root), "merge-base", "--is-ancestor", self.freeze, "HEAD"],
                        ["python3", str(self.root / self.name)],
                        ["git", "-C", str(self.root.parent), "show", self.freeze + ":" + self.name]):
            with self.assertRaises(replay.ReplayError):
                self.provider.git_blob(command)

    def test_module_adapter_preserves_the_original_mathematical_function(self):
        function = lambda x: x * x
        module = SimpleNamespace(__file__=str(self.root / self.name), mathematical_result=function)
        self.provider.patch_module(module)
        self.assertIs(module.mathematical_result, function)
        self.assertEqual(module.mathematical_result(7), 49)

    def test_generated_resource_is_verified_without_parsing_it_as_provenance(self):
        resource = "ComputeNode/state/generated.json"
        self.add(resource, b"opaque original numerical resource")
        provider = edition.BellBindings(replay.PublicInputs(self.root, self.bindings), {self.name, self.receipt})
        self.assertEqual(provider.inputs.path(resource).read_bytes(), b"opaque original numerical resource")
        self.assertNotIn(self.bindings[resource]["view_sha256"], provider.raw_identities)

    def test_signed_source_fields_cannot_hide_in_volatile_metadata(self):
        old = {"seconds": 1, "source_identity": {"tick": 16}, "whole_price": "1/7"}
        edition.compare_receipt({**old, "seconds": 2}, old, {"seconds"})
        with self.assertRaises(replay.ReplayError):
            edition.compare_receipt({**old, "whole_price": "1/8"}, old, {"seconds"})

    def forcing_fixture(self):
        dag_name = "ComputeNode/state/forcing-DAG.json"
        dag = b'{"full_operator": [1,2], "price": "1/7"}\n'
        self.add(dag_name, dag)
        dag_binding = {"path": dag_name, "bytes": len(dag), "sha256": replay.sha(dag)}
        summary = {"scientific_freeze_commit": self.freeze, "forcing_DAG": dag_binding,
                   "source_identity": {"tick": 16}, "whole_price": "1/7", "seconds": 1,
                   "independent_report": {"all_rows_checked": True}}
        summary_name = "ComputeNode/state/summary.json"
        raw = json.dumps(summary).encode()
        self.add(summary_name, raw)
        receipt = {**summary, "producer_summary": {"path": summary_name, "bytes": len(raw), "sha256": replay.sha(raw)},
                   "status": "complete", "full_control_clock_record_square_certified": False,
                   "forcing_error_scope": "original atomic coimage"}
        output = self.root / "fresh"
        output.mkdir()
        (output / "forcing-DAG.json").write_bytes(dag)
        (output / "summary.json").write_text(json.dumps({**summary, "seconds": 2,
                "forcing_DAG": {**dag_binding, "path": "fresh/forcing-DAG.json"}}))
        return replay.PublicInputs(self.root, self.bindings), receipt, output

    def test_annotated_release_receipt_uses_its_actual_producer_summary(self):
        inputs, receipt, output = self.forcing_fixture()
        result = edition.compare_forcing_output(inputs, receipt, output)
        self.assertEqual(result["status"], "passed")
        self.assertFalse(receipt["full_control_clock_record_square_certified"])
        self.assertEqual(result["original_producer_summary_sha256"], receipt["producer_summary"]["sha256"])

    def test_annotations_do_not_allow_a_different_dag_or_wrong_summary_identity(self):
        inputs, receipt, output = self.forcing_fixture()
        original = (output / "forcing-DAG.json").read_bytes()
        (output / "forcing-DAG.json").write_text('{"full_operator": [1], "price": "1/7"}')
        with self.assertRaises(replay.ReplayError):
            edition.compare_forcing_output(inputs, receipt, output)
        (output / "forcing-DAG.json").write_bytes(original)
        receipt["producer_summary"]["sha256"] = "0" * 64
        with self.assertRaises(replay.ReplayError):
            edition.compare_forcing_output(inputs, receipt, output)


if __name__ == "__main__":
    unittest.main()
