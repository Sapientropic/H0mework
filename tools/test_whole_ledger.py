import gzip
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import whole_ledger


@unittest.skipUnless(shutil.which("make"), "make is required by the reader commands")
class ReaderRunDirectoryTests(unittest.TestCase):
    def outputs(self, *arguments):
        run = subprocess.run(["make", "-n", *arguments], cwd=whole_ledger.release.ROOT,
                             capture_output=True, text=True, check=True)
        return re.findall(r"--output\s+([^\s]+)", run.stdout)

    def test_default_full_command_keeps_all_four_steps_in_one_run(self):
        outputs = self.outputs("check-whole-ledger-full")
        self.assertEqual(len(outputs), 4)
        self.assertEqual(len({value.rsplit("/", 1)[0] for value in outputs}), 1)
        self.assertEqual([value.rsplit("/", 1)[1] for value in outputs],
                         ["entry", "build", "trust", "types"])

    def test_explicit_run_directory_is_preserved_across_recursive_make(self):
        outputs = self.outputs("check-whole-ledger-full", "WLA_RUN=.local/reader-explicit")
        self.assertEqual(outputs, [".local/reader-explicit/" + kind
                                   for kind in ("entry", "build", "trust", "types")])

    def test_other_edition_does_not_inherit_whole_ledger_output_directory(self):
        outputs = self.outputs("check-first-release-full", "FR_RUN=.local/original-edition",
                               "WLA_RUN=.local/reader-explicit")
        self.assertTrue(outputs)
        self.assertTrue(all(value.startswith(".local/original-edition/") for value in outputs))


class WholeLedgerContractTests(unittest.TestCase):
    def document(self):
        return {"schema": whole_ledger.SCHEMA,
                "claims": [{"id": f"WA{i}", "paper": "whole-ledger-accounting"} for i in range(1, 41)]}

    def read(self, data):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            (root / "docs").mkdir()
            (root / whole_ledger.MAP).write_text(json.dumps(data))
            return whole_ledger.document(root)

    def test_all_forty_claims_are_required(self):
        data = self.document()
        self.assertEqual(len(self.read(data)["claims"]), 40)
        data["claims"].pop()
        with self.assertRaises(whole_ledger.release.ReleaseError):
            self.read(data)

    def test_explicit_exclusion_does_not_silently_shrink_the_contract(self):
        data = self.document()
        data["claims"][0]["selected"] = False
        with self.assertRaises(whole_ledger.release.ReleaseError):
            self.read(data)

    def test_similar_claim_and_other_edition_are_rejected(self):
        data = self.document()
        data["claims"][0]["id"] = "WA01"
        with self.assertRaises(whole_ledger.release.ReleaseError):
            self.read(data)
        data = self.document()
        data["schema"] = "h0mework/second-edition-map@1"
        with self.assertRaises(whole_ledger.release.ReleaseError):
            self.read(data)


class RecordedTypeIdentityTests(unittest.TestCase):
    def fixture(self, root, *, compressed=False):
        (root / "Lean").mkdir(exist_ok=True)
        (root / "docs").mkdir(exist_ok=True)
        (root / "tools").mkdir(exist_ok=True)
        (root / "Lean/lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")
        (root / "Lean/lake-manifest.json").write_text('{"packages": []}\n')
        (root / "Lean/lakefile.toml").write_text(
            'name = "Fixture"\nmoreLeanArgs = ["--trust=0"]\n'
            '[[lean_lib]]\nname = "Proof"\nmoreLeanArgs = ["-DwarningAsError=true"]\n')
        (root / whole_ledger.MAP).write_text('{"bibliography": []}\n')
        (root / "tools/export-map.json").write_text('{"modules": [], "artifacts": []}\n')
        inputs = {"lakefile": "Lean/lakefile.toml", "toolchain": "Lean/lean-toolchain",
                  "manifest": "Lean/lake-manifest.json", "claim_map": whole_ledger.MAP,
                  "export_map": "tools/export-map.json"}
        input_identity = {"sha256": {key: whole_ledger.release.sha((root / path).read_bytes())
                                     for key, path in inputs.items()}}
        scope = {"source_scope_sha256": "selected-source", "modules": 2}
        row = {"package": "p", "module": "Proof.Root", "qualified_name": "Proof.result",
               "type": "Nat → Nat", "axioms": [], "universe_parameters": []}
        result = {"status": "passed", "inputs_unchanged": True, "source_scopes": {"p": scope},
                  "input_identity": input_identity, "input_identity_after": input_identity,
                  "declarations": [row]}
        raw = json.dumps(result).encode()
        stored = gzip.compress(raw, mtime=0) if compressed else raw
        path = "types.json.gz" if compressed else "types.json"
        (root / path).write_bytes(stored)
        reference = {"path": path, "sha256": whole_ledger.release.sha(stored),
                     "payload_sha256": whole_ledger.release.sha(raw)}
        if compressed:
            reference["compression"] = "gzip"
        data = {"acceptance": {"declaration_types": reference}, "claims": [{"id": "WA1",
                "paper": "whole-ledger-accounting", "producers": [{"kind": "lean",
                "public": {"module": "Proof.Root"}, "verification": {"proof_package": "p"},
                "declarations": [{"qualified_name": "Proof.result", "complete_type": {
                "declaration_index": 0, "type_sha256": whole_ledger.release.sha(row['type'].encode())}}]}]}]}
        return data, {"p": scope}

    def add_control_type(self, root, data, *, compressed=False):
        reference = data["acceptance"]["declaration_types"]
        path = root / reference["path"]
        result = json.loads(gzip.decompress(path.read_bytes()) if compressed else path.read_bytes())
        row = {"package": "p", "module": "Proof.Control", "qualified_name": "Proof.controlGroups",
               "type": "Inhabited Nat", "axioms": [], "universe_parameters": []}
        result["declarations"].append(row)
        raw = json.dumps(result).encode()
        stored = gzip.compress(raw, mtime=0) if compressed else raw
        path.write_bytes(stored)
        reference.update(sha256=whole_ledger.release.sha(stored), payload_sha256=whole_ledger.release.sha(raw))
        control = {"kind": "lean", "source_commit": "1" * 40, "source_path": "Lean/Original/Control.lean",
                   "source_sha256": "2" * 64, "public": {"path": "Lean/Proof/Control.lean", "module": "Proof.Control",
                   "sha256": "3" * 64, "variant": "fixture"}, "declarations": [{"qualified_name": row["qualified_name"],
                   "kind": "instance", "complete_type": {"declaration_index": 1,
                   "type_sha256": whole_ledger.release.sha(row["type"].encode())}}]}
        data["proof_packages"] = [{"id": "p", "paper": "whole-ledger-accounting", "source_commit": "1" * 40,
                                   "lean_target": "Proof.Package", "controls": [control]}]
        return control

    def test_named_control_has_a_complete_type_without_a_synthetic_producer(self):
        for compressed in (False, True):
            with self.subTest(compressed=compressed), tempfile.TemporaryDirectory() as name:
                root = Path(name)
                data, scopes = self.fixture(root, compressed=compressed)
                self.add_control_type(root, data, compressed=compressed)
                self.assertEqual(whole_ledger.verify_recorded_types(data, scopes, root=root), 2)
                self.assertEqual(len(data["claims"][0]["producers"]), 1)

    def test_named_control_missing_index_wrong_owner_and_other_epoch_are_rejected(self):
        for changed in ("missing_index", "wrong_owner", "other_epoch", "boolean_index"):
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as name:
                root = Path(name)
                data, scopes = self.fixture(root)
                control = self.add_control_type(root, data)
                if changed == "missing_index":
                    control["declarations"][0].pop("complete_type")
                elif changed == "wrong_owner":
                    control["public"].update(module="Proof.ControlExtra", path="Lean/Proof/ControlExtra.lean")
                elif changed == "other_epoch":
                    control["source_commit"] = "2" * 40
                else:
                    control["declarations"][0]["complete_type"]["declaration_index"] = True
                with self.assertRaises(whole_ledger.release.ReleaseError):
                    whole_ledger.verify_recorded_types(data, scopes, root=root)

    def test_similar_package_control_metadata_does_not_change_type_readiness(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            data, scopes = self.fixture(root)
            data["proof_packages"] = [{"id": "p", "paper": "whole-ledger-accounting", "source_commit": "1" * 40,
                                      "lean_target": "Proof.Package", "original_controls": [{"declarations": ["Wrong.name"]}]}]
            self.assertEqual(whole_ledger.verify_recorded_types(data, scopes, root=root), 1)

    def test_type_inspection_consumes_only_explicit_named_package_controls(self):
        for explicit in (True, False):
            with self.subTest(explicit=explicit), tempfile.TemporaryDirectory() as name:
                root = Path(name)
                data, _ = self.fixture(root)
                control = self.add_control_type(root, data)
                proof = data["claims"][0]["producers"][0]
                proof.update(source_commit="1" * 40, source_path="Lean/Original/Root.lean")
                exported = {"schema": 2, "modules": [], "artifacts": [], "paper_aggregators": {"Proof.Package": "Lean/Proof/Package.lean"}}
                for entry, body in ((proof, "namespace Proof\ndef result (n : Nat) : Nat := n\nend Proof\n"),
                                    (control, "namespace Proof\nlocal instance controlGroups : Inhabited Nat := ⟨0⟩\nend Proof\n")):
                    public = entry["public"]
                    public.setdefault("path", "Lean/" + public["module"].replace(".", "/") + ".lean")
                    public.setdefault("variant", "fixture")
                    file = root / public["path"]
                    file.parent.mkdir(parents=True, exist_ok=True)
                    file.write_text(body)
                    digest = whole_ledger.release.sha(file.read_bytes())
                    public["sha256"] = entry["source_sha256"] = digest
                    exported["modules"].append({"target": public["module"], "path": public["path"], "target_sha256": digest,
                        "source_path": entry["source_path"], "source_revision": "1" * 40, "source_revisions": ["1" * 40],
                        "source_sha256": digest, "variant": public["variant"]})
                package_file = root / "Lean/Proof/Package.lean"
                package_file.write_text("import Proof.Root\nimport Proof.Control\n")
                data["schema"] = whole_ledger.SCHEMA
                if not explicit:
                    package = data["proof_packages"][0]
                    package["original_controls"] = package.pop("controls")
                (root / whole_ledger.MAP).write_text(json.dumps(data))
                (root / "tools/export-map.json").write_text(json.dumps(exported))
                (root / "tools/whole_ledger.py").write_text("# inspection-program fixture\n")
                def new_output(repository, value):
                    directory = repository / value
                    directory.mkdir(parents=True)
                    return directory
                def run(command, repository, log, environment):
                    source = (repository / "Lean" / command[-1]).read_text()
                    self.assertEqual('"Proof.controlGroups"' in source, explicit)
                    self.assertEqual('"Proof.Control"' in source, explicit)
                    rows = [{"qualified_name": "Proof.result", "module": "Proof.Root", "kind": "definition",
                             "type": "Nat → Nat", "universe_parameters": [], "axioms": [], "unsafe": False, "partial": False}]
                    if explicit:
                        rows.append({"qualified_name": "Proof.controlGroups", "module": "Proof.Control", "kind": "definition",
                                     "type": "Inhabited Nat", "universe_parameters": [], "axioms": [], "unsafe": False, "partial": False})
                    log.write_text("".join("WHOLE_LEDGER_DECLARATION " + json.dumps(row) + "\n" for row in rows))
                    return {"command": command, "cwd": "Lean", "exit_code": 0, "error": None,
                            "log": log.relative_to(repository).as_posix(), "elapsed_seconds": 0}
                with patch.object(whole_ledger.release, "run_process", side_effect=run), \
                        patch.object(whole_ledger.release, "new_output", side_effect=new_output):
                    result = whole_ledger.types(".local/types-fixture", root=root)
                self.assertEqual(result["status"], "passed")
                self.assertEqual(len(result["declarations"]), 2 if explicit else 1)
    def test_exact_type_and_explicit_compressed_artifact(self):
        for compressed in (False, True):
            with self.subTest(compressed=compressed), tempfile.TemporaryDirectory() as name:
                root = Path(name)
                data, scopes = self.fixture(root, compressed=compressed)
                self.assertEqual(whole_ledger.verify_recorded_types(data, scopes, root=root), 1)

    def test_similar_owner_and_changed_source_scope_are_rejected(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            data, scopes = self.fixture(root)
            data["claims"][0]["producers"][0]["public"]["module"] = "Proof.RootExtra"
            with self.assertRaises(whole_ledger.release.ReleaseError):
                whole_ledger.verify_recorded_types(data, scopes, root=root)
            data, scopes = self.fixture(root)
            scopes["p"] = {"source_scope_sha256": "changed-source", "modules": 2}
            with self.assertRaises(whole_ledger.release.ReleaseError):
                whole_ledger.verify_recorded_types(data, scopes, root=root)

    def test_changed_type_environment_inputs_are_rejected(self):
        changes = {"Lean/lean-toolchain": "leanprover/lean4:v4.34.0\n",
                   "Lean/lake-manifest.json": '{"packages": [{"rev": "changed"}]}\n',
                   "Lean/lakefile.toml": 'name = "ChangedFixture"\n'}
        for path, changed in changes.items():
            with self.subTest(path=path), tempfile.TemporaryDirectory() as name:
                root = Path(name)
                data, scopes = self.fixture(root)
                (root / path).write_text(changed)
                with self.assertRaises(whole_ledger.release.ReleaseError):
                    whole_ledger.verify_recorded_types(data, scopes, root=root)

    def test_bibliography_and_registration_metadata_do_not_invalidate_types(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            data, scopes = self.fixture(root)
            data["bibliography"] = [{"title": "Updated bibliography"}]
            (root / whole_ledger.MAP).write_text(json.dumps(data))
            (root / "tools/export-map.json").write_text(
                '{"modules": [], "artifacts": [], "note": "Updated registration metadata"}\n')
            self.assertEqual(whole_ledger.verify_recorded_types(data, scopes, root=root), 1)


if __name__ == "__main__":
    unittest.main()

class TypeDagTests(unittest.TestCase):
    def row(self):
        graph = {'schema': 'lean-expr-dag@1', 'root': 1,
                 'nodes': [{'sort': {'zero': None}},
                           {'forallE': {'name': None, 'type': 0, 'body': 0, 'bi': 'default'}}]}
        return {'type': json.dumps(graph), 'type_format': 'lean-expr-dag@1', 'kernel_equivalent': True}

    def test_complete_kernel_checked_dag_and_legacy_type(self):
        whole_ledger.validate_complete_type(self.row())
        whole_ledger.validate_complete_type({'type': 'Nat'})

    def test_dag_root_and_references_cannot_be_missing_forward_or_boolean(self):
        row = self.row()
        for root in (True, -1, 2):
            graph = json.loads(row['type']); graph['root'] = root
            with self.assertRaises(whole_ledger.release.ReleaseError):
                whole_ledger.validate_complete_type({**row, 'type': json.dumps(graph)})
        for ref in (True, 1, 2, -1):
            graph = json.loads(row['type']); graph['nodes'][1]['forallE']['body'] = ref
            with self.assertRaises(whole_ledger.release.ReleaseError):
                whole_ledger.validate_complete_type({**row, 'type': json.dumps(graph)})

    def test_unknown_or_unresolved_node_and_unchecked_reconstruction_fail(self):
        row = self.row()
        with self.assertRaises(whole_ledger.release.ReleaseError):
            whole_ledger.validate_complete_type({**row, 'kernel_equivalent': False})
        for node in ({'mvar': None}, {'fvar': None}, {'cut': 0}):
            graph = json.loads(row['type']); graph['nodes'][0] = node
            with self.assertRaises(whole_ledger.release.ReleaseError):
                whole_ledger.validate_complete_type({**row, 'type': json.dumps(graph)})
