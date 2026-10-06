"""Public-view identity, output ownership and scientific acceptance contracts."""
from fractions import Fraction
import itertools
import json
from pathlib import Path
import sys
import tempfile
import subprocess
from types import ModuleType, SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import first_release_replay as replay
import source_view


class PublicViewTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / "tools").mkdir()
        (self.root / "evidence").mkdir()
        self.old, self.new = "a" * 40, "b" * 40
        self.raw = b'print("original mathematical source")\n'
        self.receipt = b'{"checks":{"signed":true},"all_pass":true}\n'
        (self.root / "source.py").write_bytes(self.raw)
        (self.root / "source-new.py").write_bytes(b'print("later source")\n')
        (self.root / "evidence/result.json").write_bytes(self.receipt)
        rows = []
        for source, target, revision in (("run/check.py", "source.py", self.old),
                                         ("run/check.py", "source-new.py", self.new),
                                         ("run/result.json", "evidence/result.json", self.old)):
            raw = (self.root / target).read_bytes()
            rows.append({"source": source, "source_revision": revision, "source_revisions": [revision],
                         "path": target, "target": target, "source_sha256": replay.sha(raw),
                         "target_sha256": replay.sha(raw)})
        self.map = {"schema": 2, "lean_directory": "Lean", "modules": [], "artifacts": rows,
                    "revisions": {"H": self.old, "AE": self.new}}
        (self.root / "tools/export-map.json").write_text(json.dumps(self.map))

    def tearDown(self):
        self.temp.cleanup()

    def test_fixed_epoch_and_fresh_output_omit_preserve_frozen_bytes(self):
        view = self.root / ".local/run/view"
        result = replay.prepare_view(self.root, view, {"ref": "H", "prefixes": ["run/"]}, ["run/result.json"])
        self.assertEqual((view / "run/check.py").read_bytes(), self.raw)
        self.assertFalse((view / "run/result.json").exists())
        self.assertEqual((self.root / "evidence/result.json").read_bytes(), self.receipt)
        self.assertEqual(result["source_revision"], self.old)

    def test_target_tampering_fails_before_any_program_runs(self):
        (self.root / "source.py").write_bytes(b'print("tampered source")\n')
        with self.assertRaises(source_view.ViewError):
            replay.prepare_view(self.root, self.root / ".local/new", {"ref": "H", "paths": ["run/check.py"]})

    def test_view_input_changed_after_preparation_is_rejected(self):
        view = self.root / ".local/view"
        meta = replay.prepare_view(self.root, view, {"ref": "H", "paths": ["run/check.py"]})
        inputs = replay.PublicInputs(view, meta["bindings"])
        inputs.verify_all()
        (view / "run/check.py").write_bytes(b"changed")
        with self.assertRaises(replay.ReplayError):
            inputs.verify_all()

    def test_existing_view_is_never_deleted(self):
        view = self.root / ".local/another-task"
        view.mkdir(parents=True)
        (view / "important.json").write_text("keep")
        with self.assertRaises(replay.ReplayError):
            replay.prepare_view(self.root, view, {"ref": "H", "paths": ["run/check.py"]})
        self.assertEqual((view / "important.json").read_text(), "keep")

    def test_explicit_input_missing_at_epoch_is_an_error(self):
        with self.assertRaises(replay.ReplayError):
            replay.prepare_view(self.root, self.root / ".local/missing", {"ref": "AE", "paths": ["run/result.json"]})

    def test_empty_selectors_do_not_reconstruct_the_entire_export(self):
        with self.assertRaisesRegex(replay.ReplayError, "nonempty selectors"):
            replay.prepare_view(self.root, self.root / ".local/all", {"ref": "H"})

    def test_public_upstream_source_is_an_explicit_exact_byte_overlay(self):
        source = self.root / "evidence/upstream.lean"
        source.write_bytes(b"official original source\n")
        row = {"path": "evidence/upstream.lean", "sha256": replay.sha(source.read_bytes()),
               "original_path": "Lean/.lake/packages/library/Library/Exact.lean",
               "source_repository": "https://github.com/upstream/library", "source_commit": "c" * 40}
        configuration = {"ref": "H", "paths": ["run/check.py"], "public_inputs": [row]}
        view = self.root / ".local/upstream"
        metadata = replay.prepare_view(self.root, view, configuration)
        self.assertEqual((view / row["original_path"]).read_bytes(), source.read_bytes())
        self.assertEqual(metadata["bindings"][row["original_path"]]["source_revision"], row["source_commit"])
        self.assertEqual(metadata["bindings"][row["original_path"]]["source_repository"], row["source_repository"])
        self.assertEqual((view / "run/check.py").read_bytes(), self.raw)
        source.write_bytes(b"changed upstream source")
        with self.assertRaisesRegex(replay.ReplayError, "public source input changed"):
            replay.prepare_view(self.root, self.root / ".local/changed", configuration)

    def test_public_upstream_overlay_rejects_cache_fallback_and_source_override(self):
        source = self.root / "evidence/upstream.lean"
        source.write_bytes(b"original source")
        row = {"path": "evidence/upstream.lean", "sha256": replay.sha(source.read_bytes()),
               "original_path": "Lean/Library/Exact.lean",
               "source_repository": "https://github.com/upstream/library", "source_commit": "c" * 40}
        for index, changed in enumerate(({"path": "Lean/.lake/packages/library/Exact.lean"},
                                          {"original_path": "run/check.py"}, {"path": "../private/source.lean"},
                                          {"original_path": "/tmp/foreign.lean"}, {"source_commit": "unregistered"},
                                          {"source_repository": "https://secret@example.org/library"})):
            with self.subTest(index=index), self.assertRaises(replay.ReplayError):
                replay.prepare_view(self.root, self.root / (".local/rejected-" + str(index)),
                                    {"ref": "H", "paths": ["run/check.py"], "public_inputs": [{**row, **changed}]})


class ScientificAcceptanceTests(unittest.TestCase):
    def test_exact_controls_need_executed_negative_witnesses(self):
        result = {"all_pass": True, "checks": {"same-source": True},
                  "effective_negative_controls": {"wrong-source": True}, "count": 1}
        replay.exact_controls(result, result)
        missing = {"all_pass": True, "checks": {"same-source": True}}
        with self.assertRaises(replay.ReplayError):
            replay.exact_controls(missing, missing)
        changed = {**result, "effective_negative_controls": {"wrong-source": False}}
        with self.assertRaises(replay.ReplayError):
            replay.exact_controls(changed, changed)

    def test_exact_controls_do_not_accept_status_only_or_changed_output(self):
        with self.assertRaises(replay.ReplayError):
            replay.exact_controls({"all_pass": True}, {"all_pass": True})
        good = {"all_pass": True, "checks": {"price": True}, "effective_negative_controls": {"omit-tail": True}}
        with self.assertRaises(replay.ReplayError):
            replay.exact_controls({**good, "changed_coefficient": 48}, good)

    def test_probability_carrier_preserves_bit_types_and_all_contexts(self):
        constructor = SimpleNamespace(Q2=lambda rational, root: Fraction(rational))
        records = [{"herald": h, "setting_a": a, "setting_b": b, "outcome_a": x, "outcome_b": y,
                    "probability": {"r": "1/4", "s": "0"}}
                   for h, a, b, x, y in itertools.product((False, True), (0, 1), (0, 1), (False, True), (False, True))]
        self.assertEqual(len(replay.table(records, constructor)), 32)
        with self.assertRaises(replay.ReplayError):
            replay.table(records[:-1], constructor)
        with self.assertRaises(replay.ReplayError):
            replay.table([records[0], *records[:-1]], constructor)
        wrong = [{**records[0], "herald": 0}, *records[1:]]
        with self.assertRaises(replay.ReplayError):
            replay.table(wrong, constructor)

    def test_physical_time_is_not_removed_as_runtime_metadata(self):
        with self.assertRaises(replay.ReplayError):
            replay.close_numbers({"time": 2.0, "pulse": {"duration": 4}},
                                 {"time": 1.0, "pulse": {"duration": 4}}, 1e-12)
        with self.assertRaises(replay.ReplayError):
            replay.close_numbers({"duration": 5}, {"duration": 4}, 1e-12)

    def test_nonfinite_numerical_readout_is_rejected(self):
        with self.assertRaises(replay.ReplayError):
            replay.close_numbers(float("nan"), 1.0, 1e-12)

    def test_status_only_cannot_stand_for_a_complete_nist_witness(self):
        for name in replay.NIST_CONSUMERS:
            with self.subTest(name=name), self.assertRaises(replay.ReplayError):
                replay.validate_nist_certificate(name, SimpleNamespace(), {"status": "certified"})
        with self.assertRaises(replay.ReplayError):
            replay.validate_nist_certificate("observable-closure/full-statistical-fiber/verify_fiber.py",
                SimpleNamespace(), {"schema": "full-fiber", "status": "certified", "evidence_valid": True})

    def test_paired_fiber_acceptance_preserves_the_negative_heldout_outcome(self):
        result = {"schema": "full-fiber", "status": "certified", "uniform_heldout_contained": False,
                  "tree_verification": {"primary": {}, "independent": {}},
                  "member_verification": {"primary": {}, "independent": {}},
                  "actual_Born_uniform_counterexamples": [{"implementation": name} for name in ("primary", "independent")]}
        replay.validate_nist_certificate("observable-closure/full-statistical-fiber/verify_fiber.py", SimpleNamespace(), result)
        with self.assertRaises(replay.ReplayError):
            replay.validate_nist_certificate("observable-closure/full-statistical-fiber/verify_fiber.py",
                SimpleNamespace(POSITIVE_FIELDS=("all_boundary_leaves_checked",)), result)


class ConfigurationAndProvenanceTests(unittest.TestCase):
    def test_runtime_file_scope_accepts_explicit_archive_and_rejects_ambient_or_archive_write(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            view, external = root / "view", root / "external"
            view.mkdir()
            external.mkdir()
            archive = external / "official.zip"
            archive.write_bytes(b"official")
            scope = replay.RuntimeInputs([view], files=[archive])
            scope.audit("open", (str(view / "source.py"), "r", 0))
            scope.audit("open", (str(archive), "r", 0))
            with self.assertRaises(replay.ReplayError):
                scope.audit("open", (str(external / "ambient.json"), "r", 0))
            with self.assertRaises(replay.ReplayError):
                scope.audit("open", (str(archive), "w", replay.os.O_WRONLY))

    def test_runtime_allows_only_declared_original_program_command_and_no_network(self):
        allowed = ["python", "/public/view/check.py", "--output", "/public/new/result.json"]
        scope = replay.RuntimeInputs([], processes=[allowed])
        scope.audit("subprocess.Popen", ("python", allowed, None, None))
        with self.assertRaises(replay.ReplayError):
            scope.audit("subprocess.Popen", ("git", ["git", "show", "HEAD:file"], None, None))
        with self.assertRaises(replay.ReplayError):
            scope.audit("socket.connect", ())

    def test_config_accepts_original_program_ids_and_rejects_nonstring_ids(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "runtime.json"
            check = {"id": "original_check-v1", "tier": "entry", "kind": "core-identities"}
            config = {"schema": replay.SCHEMA, "views": {}, "checks": [check]}
            path.write_text(json.dumps(config))
            self.assertEqual(replay.load_config(path)["checks"][0]["id"], check["id"])
            for bad in (1, [], "../escape"):
                path.write_text(json.dumps({**config, "checks": [{**check, "id": bad}]}))
                with self.subTest(bad=bad), self.assertRaises(replay.ReplayError):
                    replay.load_config(path)

    def test_python_override_keeps_virtualenv_symlink_and_resolves_repository_path(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            executable = root / ".local/venv/bin/python"
            executable.parent.mkdir(parents=True)
            executable.symlink_to(sys.executable)
            with patch.object(replay, "ROOT", root):
                self.assertEqual(replay.python_executable(".local/venv/bin/python"), str(executable))
                self.assertEqual(replay.python_executable(str(executable)), str(executable))
                with self.assertRaises(replay.ReplayError):
                    replay.python_executable(".local/missing/python")

    def test_core_script_runs_from_copy_because_output_follows_its_filename(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            original = root / "scripts/physics/common-source/check_core_identities.py"
            original.parent.mkdir(parents=True)
            raw = b"# Writes a result beside __file__\n"
            original.write_bytes(raw)
            frozen = {"status": "passed", "families": 20, "evaluations": 501,
                      "max_residual": 0.0, "absolute_tolerance": 1e-10, "generator_sha256": replay.sha(raw)}
            (root / "frozen.json").write_text(json.dumps(frozen))
            output = root / ".local/new/check"
            output.mkdir(parents=True)
            def producer(command, **kwargs):
                self.assertEqual(Path(command[1]), output / original.name)
                Path(command[1]).with_name("core-identity-checks.json").write_text(json.dumps(frozen))
                return SimpleNamespace(returncode=0, stdout="passed", stderr="")
            with patch.object(replay, "ROOT", root), patch.object(replay.subprocess, "run", side_effect=producer):
                replay.run_program(None, {"kind": "core-identities", "frozen": "frozen.json"}, output, "python")
            self.assertEqual(original.read_bytes(), raw)
            self.assertFalse(original.with_name("core-identity-checks.json").exists())

    def test_declared_output_must_match_the_original_writer(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "config.json"
            program = next(iter(replay.GAMMA_PROGRAMS))
            path.write_text(json.dumps({"schema": replay.SCHEMA, "views": {"ae": {"ref": "AE"}},
                "checks": [{"id": "gamma", "tier": "entry", "kind": "exact-source-controls", "view": "ae",
                            "program": program, "output": "evidence/frozen.json"}]}))
            with self.assertRaises(replay.ReplayError):
                replay.load_config(path)

    def test_frozen_receipt_changed_during_program_is_rejected(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            original = root / "scripts/physics/common-source/check_core_identities.py"
            original.parent.mkdir(parents=True)
            raw = b"# Native file-output checker\n"
            original.write_bytes(raw)
            frozen = {"status": "passed", "families": 20, "evaluations": 501,
                      "max_residual": 0.0, "absolute_tolerance": 1e-10, "generator_sha256": replay.sha(raw)}
            receipt = root / "frozen.json"
            receipt.write_text(json.dumps(frozen))
            output = root / ".local/run"
            output.mkdir(parents=True)
            def producer(command, **kwargs):
                Path(command[1]).with_name("core-identity-checks.json").write_text(json.dumps(frozen))
                receipt.write_text(json.dumps({**frozen, "evaluations": 0}))
                return SimpleNamespace(returncode=0, stdout="", stderr="")
            with patch.object(replay, "ROOT", root), patch.object(replay.subprocess, "run", side_effect=producer):
                with self.assertRaisesRegex(replay.ReplayError, "changed during execution"):
                    replay.run_program(None, {"kind": "core-identities", "frozen": "frozen.json"}, output, "python")

    def test_original_controls_really_execute_and_keep_their_failure_exit(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            relative = replay.BELL + "/nist-real/nominal-replay/observable-closure/slice_tests.py"
            program = root / relative
            program.parent.mkdir(parents=True)
            for code in (0, 1):
                raw = ('print("original-control-executed")\nraise SystemExit(' + str(code) + ')\n').encode()
                program.write_bytes(raw)
                bindings = {relative: {"view_sha256": replay.sha(raw), "source_sha256": replay.sha(raw),
                                      "source_revision": "a" * 40, "source_revisions": ["a" * 40]}}
                provider = replay.RecordedSourceBindings(replay.PublicInputs(root, bindings))
                result = provider.controls(["python3", str(program)])
                self.assertEqual(result.returncode, code)
                self.assertIn("original-control-executed", result.stdout)
            with self.assertRaises(replay.ReplayError):
                provider.controls(["python3", str(root / "unregistered.py")])

    def test_fresh_receipt_digest_is_allowed_only_in_its_declared_output(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            view, output = root / "view", root / "output"
            view.mkdir()
            output.mkdir()
            path = output / "fresh.json"
            path.write_text('{"fresh":true}')
            inputs = replay.PublicInputs(view, {})
            provider = replay.RecordedSourceBindings(inputs, fresh_root=output)
            self.assertEqual(provider.digest(path), replay.sha(path.read_bytes()))
            other = root / "other.json"
            other.write_text('{"fresh":false}')
            with self.assertRaises(replay.ReplayError):
                provider.digest(other)

    def test_no_archive_directory_fallback(self):
        with self.assertRaisesRegex(replay.ReplayError, "explicit --archive-dir"):
            replay.archive(None, "data.zip", {"bytes": 1, "sha256": "0" * 64})

    def test_archive_hash_and_path_checks(self):
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            (directory / "data.zip").write_bytes(b"raw input")
            path, row = replay.archive(directory, "data.zip", {"bytes": 9, "sha256": replay.sha(b"raw input")})
            self.assertEqual(path.name, "data.zip")
            self.assertEqual(row["sha256"], replay.sha(b"raw input"))
            with self.assertRaises(replay.ReplayError):
                replay.archive(directory, "data.zip", {"bytes": 9, "sha256": "0" * 64})
            with self.assertRaises(replay.ReplayError):
                replay.archive(directory, "../data.zip", {"bytes": 9, "sha256": "0" * 64})

    def test_source_paths_reject_escapes_and_machine_addresses(self):
        for path in ("../source.py", "/source.py", "C:\\source.py", "source/../data.json"):
            with self.subTest(path=path), self.assertRaises(replay.ReplayError):
                replay.relative(path)

    def test_missing_required_full_group_cannot_report_success(self):
        config = {"checks": [{"id": "quick", "tier": "entry"}], "required": {"full": ["full-tree"]}}
        with self.assertRaises(replay.ReplayError):
            replay.select_checks(config, "full")
        with self.assertRaises(replay.ReplayError):
            replay.select_checks(config, "bell")

    def test_recorded_epoch_is_not_invented_or_ancestor_simulated(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            source = b"source bytes"
            (root / "source.py").write_bytes(source)
            epoch = "a" * 40
            receipt = {"bindings": [{"path": "source.py", "commit": epoch, "sha256": replay.sha(source)}]}
            (root / "receipt.json").write_text(json.dumps(receipt))
            bindings = {key: {"view_sha256": replay.sha((root / key).read_bytes()),
                              "source_sha256": replay.sha((root / key).read_bytes()),
                              "source_revision": "b" * 40, "source_revisions": ["b" * 40]}
                        for key in ("source.py", "receipt.json")}
            provider = replay.RecordedSourceBindings(replay.PublicInputs(root, bindings))
            self.assertEqual(provider.binding(root / "source.py")["commit"], epoch)
            with self.assertRaises(replay.ReplayError):
                provider.binding(root / "source.py", "c" * 40)
            with self.assertRaises(replay.ReplayError):
                provider.check_binding({"path": "source.py", "sha256": replay.sha(source), "commit": "c" * 40})
            self.assertFalse(next(iter(provider.used.values()))["Git_ancestry_replayed"])
            with replay.original_source_metadata(provider):
                with self.assertRaisesRegex(replay.ReplayError, "subprocess"):
                    subprocess.run(["git", "merge-base", "--is-ancestor", epoch, "HEAD"])

    def test_frozen_group_registers_only_its_verified_source_identity(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            raw = b"original inverse producer\n"
            (root / "producer.py").write_bytes(raw)
            epoch = "c" * 40
            receipt = {"freeze_commit": epoch, "source_bindings": [
                {"path": "producer.py", "sha256": replay.sha(raw)}]}
            (root / "receipt.json").write_text(json.dumps(receipt))
            bindings = {path: {"view_sha256": replay.sha((root / path).read_bytes()),
                              "source_sha256": replay.sha((root / path).read_bytes()),
                              "source_revision": "a" * 40, "source_revisions": ["a" * 40]}
                        for path in ("producer.py", "receipt.json")}
            provider = replay.RecordedSourceBindings(replay.PublicInputs(root, bindings))
            self.assertEqual(provider.binding(root / "producer.py", epoch)["commit"], epoch)
            provider.collect({"freeze_commit": "d" * 40, "source_bindings": [
                {"path": "producer.py", "sha256": "0" * 64}]})
            with self.assertRaises(replay.ReplayError):
                provider.binding(root / "producer.py", "d" * 40)

    def test_anchor_contract_has_separate_original_inverse_and_controls(self):
        self.assertEqual(replay.MUNICH_CONTRACTS["hardware-anchors"],
            ("hardware_anchors_run.py", "test_hardware_anchors.py", "test_hardware_anchor_check.py", "test_hardware_anchors_run.py"))
        self.assertNotEqual(replay.MUNICH_CONTRACTS["hardware-anchors"][0],
                            replay.MUNICH_CONTRACTS["identification"][0])

    def test_anchor_controls_import_the_same_adapted_module_and_restore_previous_alias(self):
        parent = SimpleNamespace(frozen=object(), sha256=object(), require=replay.require)
        anchors = SimpleNamespace(consume=object())
        science = SimpleNamespace(parent=parent, anchors_certify=anchors, consume=object())
        provider = SimpleNamespace(digest=lambda value: "digest")
        old = ModuleType("previous_anchor_module")
        with patch.dict(sys.modules, {"hardware_anchors_run": old}):
            with replay.hardware_anchor_intake(None, provider, science):
                self.assertIs(sys.modules["hardware_anchors_run"], science)
            self.assertIs(sys.modules["hardware_anchors_run"], old)


class RecordedCommitPrefixTests(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory()
        self.root = Path(self.folder.name)
        self.full = "1234567890" + "a" * 30
        self.other = "1234567890" + "b" * 30
        raw = b"verified original source"
        (self.root / "source.py").write_bytes(raw)
        self.bindings = {"source.py": {"view_sha256": replay.sha(raw), "source_sha256": replay.sha(raw),
                         "source_revision": "c" * 40, "source_revisions": ["c" * 40]}}
        self.provider = replay.RecordedSourceBindings(replay.PublicInputs(self.root, self.bindings))
        self.provider.records["source.py"] = {(self.full, replay.sha(raw)), (self.full[:10], replay.sha(raw))}

    def tearDown(self):
        self.folder.cleanup()

    def test_unique_registered_full_and_short_are_one_identity(self):
        self.assertEqual(self.provider.binding(self.root / "source.py")["commit"], self.full)
        self.assertEqual(self.provider.binding(self.root / "source.py", self.full[:10])["commit"], self.full[:10])
        self.provider.check_binding({"path": "source.py", "commit": self.full[:10],
                                     "sha256": self.bindings["source.py"]["source_sha256"]})

    def test_two_registered_full_matches_stay_ambiguous(self):
        self.provider.records["source.py"].add((self.other, self.bindings["source.py"]["source_sha256"]))
        with self.assertRaises(replay.ReplayError):
            self.provider.binding(self.root / "source.py")

    def test_unknown_full_cannot_be_created_from_short_alone(self):
        self.provider.records["source.py"] = {(self.full[:10], self.bindings["source.py"]["source_sha256"])}
        with self.assertRaises(replay.ReplayError):
            self.provider.binding(self.root / "source.py", self.full)

    def test_wrong_digest_and_unregistered_prefix_stay_rejected(self):
        with self.assertRaises(replay.ReplayError):
            self.provider.check_binding({"path": "source.py", "commit": self.full[:10], "sha256": "0" * 64})
        with self.assertRaises(replay.ReplayError):
                self.provider.binding(self.root / "source.py", "9876543210")


class CompressedReceiptBindingsTests(unittest.TestCase):
    def fixture(self, root, compressed=None):
        raw = b"original source bytes"
        (root / "source.py").write_bytes(raw)
        record = {"path": "source.py", "sha256": replay.sha(raw), "commit": "a" * 40}
        logical = json.dumps({"bindings": [record]}).encode()
        names = ["source.py"]
        if compressed is not None:
            (root / "first.receipt").write_bytes(compressed(logical))
            names.append("first.receipt")
        bindings = {name: {"view_sha256": replay.sha((root / name).read_bytes()),
                           "source_sha256": replay.sha((root / name).read_bytes()),
                           "source_revision": "b" * 40, "source_revisions": ["b" * 40]}
                    for name in names}
        return replay.RecordedSourceBindings(replay.PublicInputs(root, bindings)), record, logical

    def test_verified_compressed_input_registers_its_original_labels_without_changing_bytes(self):
        for library in (replay.lzma, replay.gzip):
            with self.subTest(library=library.__name__), tempfile.TemporaryDirectory() as name:
                root = Path(name)
                provider, record, logical = self.fixture(root, library.compress)
                decoder = library.decompress
                with replay.original_source_metadata(provider):
                    decoded = library.decompress((root / "first.receipt").read_bytes())
                    self.assertEqual(decoded, logical)
                    json.loads(decoded)
                    provider.check_binding(record)
                self.assertIs(library.decompress, decoder)
                self.assertEqual(len(provider.adaptations), 1)
                self.assertFalse(next(iter(provider.adaptations.values()))["decoded_bytes_modified"])

    def test_unmapped_compressed_payload_cannot_register_a_source_epoch(self):
        with tempfile.TemporaryDirectory() as name:
            provider, record, logical = self.fixture(Path(name))
            with replay.original_source_metadata(provider):
                json.loads(replay.lzma.decompress(replay.lzma.compress(logical)))
                with self.assertRaisesRegex(replay.ReplayError, "not read from a verified receipt"):
                    provider.check_binding(record)
            self.assertFalse(provider.adaptations)


class ConfigurationSourceIdentityTests(unittest.TestCase):
    def test_legacy_repository_root_is_the_verified_view_for_relative_input_consumers(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            source = replay.BELL + "/nist-real/nominal-replay/public-review/source-compression/domain.py"
            path = root / source
            path.parent.mkdir(parents=True)
            raw = b"def evaluate():\n    return Fraction((ROOT / 'input.txt').read_text())\n"
            path.write_bytes(raw)
            (root / "input.txt").write_text("1/3")
            bindings = {value: {"view_sha256": replay.sha((root / value).read_bytes()),
                                "source_sha256": replay.sha((root / value).read_bytes()),
                                "source_revision": "a" * 40, "source_revisions": ["a" * 40]}
                        for value in (source, "input.txt")}
            module = ModuleType("original_relative_reader")
            module.__dict__.update(ROOT=root.parent, PROJECT=root.parent / "Lean", __file__=str(path), Fraction=Fraction)
            exec(compile(raw, str(path), "exec"), module.__dict__)
            provider = replay.RecordedSourceBindings(replay.PublicInputs(root, bindings))
            provider.patch_module(module)
            self.assertEqual(module.evaluate(), Fraction(1, 3))
            self.assertEqual(module.ROOT, root.resolve())
            self.assertEqual(module.PROJECT, root.resolve() / "Lean")
            self.assertEqual(path.read_bytes(), raw)
            self.assertFalse(provider.adaptations[(source, "ROOT")]["Git_ancestry_replayed"])

    def fixture(self, directory, guard):
        root = Path(directory)
        (root / "criterion.md").write_text("original contract")
        path = root / "primary.py"
        raw = ("def configuration():\n"
               "    freeze = frozen(ROOT / 'criterion.md')\n"
               "    executable = frozen(__file__)\n"
               "    " + guard + "\n"
               "    return Fraction(1, 3) + Fraction(1, 6)\n").encode()
        path.write_bytes(raw)
        bindings = {name: {"view_sha256": replay.sha((root / name).read_bytes()),
                           "source_sha256": replay.sha((root / name).read_bytes()),
                           "source_revision": "a" * 40, "source_revisions": ["a" * 40]}
                    for name in ("primary.py", "criterion.md")}
        provider = replay.RecordedSourceBindings(replay.PublicInputs(root, bindings))
        module = ModuleType("original_configuration")
        module.__dict__.update(ROOT=root, __file__=str(path), frozen=provider.binding,
                               Fraction=Fraction, subprocess=subprocess)
        exec(compile(raw, str(path), "exec"), module.__dict__)
        return provider, module, raw, path

    def test_only_the_exact_ancestry_statement_is_replaced_and_math_is_preserved(self):
        guard = 'subprocess.run(["git", "merge-base", "--is-ancestor", freeze["commit"], executable["commit"]], cwd=ROOT, check=True)'
        with tempfile.TemporaryDirectory() as name:
            provider, module, raw, path = self.fixture(name, guard)
            provider.configuration_identity(module, "primary.py")
            with patch.object(subprocess, "run", side_effect=AssertionError("Git must not be called")):
                self.assertEqual(module.configuration(), Fraction(1, 2))
            self.assertEqual(path.read_bytes(), raw)
            self.assertEqual(len(provider.used), 2)
            self.assertFalse(next(iter(provider.adaptations.values()))["Git_ancestry_replayed"])
            provider.configuration_identity(module, "primary.py")

    def test_changed_ancestry_guard_requires_review(self):
        guard = 'subprocess.run(["git", "merge-base", "--is-ancestor", freeze["commit"], executable["commit"]], cwd=ROOT, check=False)'
        with tempfile.TemporaryDirectory() as name:
            provider, module, _, _ = self.fixture(name, guard)
            with self.assertRaises(replay.ReplayError):
                provider.configuration_identity(module, "primary.py")


class ContrastKernelSourceIdentityTests(unittest.TestCase):
    def fixture(self, directory, mutate=None, changed_guard=False):
        root = Path(directory).resolve()
        name = replay.BELL + "/nist-real/nominal-replay/public-review/contrast-source/certify.py"
        original = Path(__file__).resolve().parents[1] / ("scripts/first-release/ad/" + name.removeprefix("Verification/"))
        raw = original.read_bytes()
        if changed_guard:
            raw = raw.replace(b"source_closure(closure['toolchain_source_root'],True)",
                              b"source_closure(closure['toolchain_source_root'],False)")
        path = root / name
        path.parent.mkdir(parents=True)
        path.write_bytes(raw)
        here, nominal = path.parent, path.parent.parents[1]
        fiber = nominal / "observable-closure/full-statistical-fiber"
        chain = [nominal / "gaussian-window/GaussianSource.lean", nominal / "observable-closure/ObservableClosure.lean",
                 nominal / "observable-closure/ClosureConsumer.lean", here / "ContrastSource.lean",
                 here / "ContrastConsumer.lean", here / "ContrastCertification.lean"]
        owned = [*chain, *[here / value for value in ("criterion.md", "sources.json", "certify.py", "tests.py", "lsp-status.json")],
                 fiber / "phase_certify.py", fiber / "covariance_source_certify.py",
                 root / "Lean/lean-toolchain", root / "Lean/lake-manifest.json"]
        for source in owned:
            source.parent.mkdir(parents=True, exist_ok=True)
            if source != path:
                source.write_bytes(b"{}\n" if source.suffix == ".json" else b"owned public source\n")
        historical = {"commit": "d" * 40, "sha256": "e" * 64}
        sources = {"inputs": [{"path": source.relative_to(root).as_posix(), "sha256": replay.sha(source.read_bytes())}
                              for source in (chain[0], root / "Lean/lean-toolchain")] +
                             [{"path": "Lean/lakefile.toml", "sha256": historical["sha256"]}]}
        (here / "sources.json").write_text(json.dumps(sources))
        module = ModuleType("original_contrast_kernel")
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        module.__dict__.update(__file__=str(path), HERE=here, ROOT=root.parent, PROJECT=root.parent / "Lean",
                               NOMINAL=nominal, FIBER=fiber, CHAIN=chain, ALLOWED=allowed,
                               CLAIMS={"source_generated_probability_law_all_N": True, "controller_advance": False},
                               SCOPES={"source": "original physical source"}, PUBLIC={"P23.OriginalSource.consumer"},
                               json=json, hashlib=replay.hashlib, Path=Path, subprocess=subprocess,
                               digest=lambda _: None, frozen=lambda _: None,
                               rel=lambda value: value.relative_to(module.ROOT).as_posix(),
                               source_closure=lambda *a, **k: (_ for _ in ()).throw(AssertionError("historical closure called")),
                               independent_registry_change=lambda *a, **k: (_ for _ in ()).throw(AssertionError("historical registry called")))
        functions = [node for node in replay.ast.parse(raw).body if isinstance(node, replay.ast.FunctionDef) and
                     node.name in {"owned_sources", "require", "evidence_row", "fastconsume"}]
        exec(compile(replay.ast.Module(body=functions, type_ignores=[]), str(path), "exec"), module.__dict__)
        cert = {"schema": "p23-source-contrast-lean-certification/v1", "status": "certified",
                "kernel_claims": module.CLAIMS, "mouth_scope": module.SCOPES,
                "authorized_axioms": sorted(allowed), "public_mouths": sorted(module.PUBLIC),
                "bindings": {source.relative_to(root).as_posix(): {"commit": "a" * 40, "sha256": replay.sha(source.read_bytes())}
                             for source in owned}, "historical_lake_binding": historical,
                "focused_verification": {"fresh_source_compilation": True, "trust_level": 0, "warning_as_error": True,
                                         "commands": [{"source": source.relative_to(root).as_posix(), "exit_code": 0} for source in chain]},
                "source_audit": {"axiom_declarations_checked": 2, "source_declarations": 1, "independent_declarations": 1,
                                 "public_axioms": {value: sorted(allowed) for value in module.PUBLIC}},
                "actual_import_closure": {"modules": 4381, "source_binding_sha256": "f" * 64, "unresolved": []}}
        if mutate:
            mutate(cert)
        canonical = here / "certification.json"
        canonical.write_text(json.dumps(cert))
        history = {**module.evidence_row(False), **module.CLAIMS, "evidence_valid": True,
                   "certificate_sha256": replay.sha(canonical.read_bytes()), "certificate_commit": "a" * 40,
                   "authorized_axioms": cert["authorized_axioms"], "public_mouths": cert["public_mouths"],
                   "lake_registry": {"registry_changed": True, "original_registrations_unchanged": True},
                   "new_source_or_solver_execution": False}
        history_path = here.parent / "source-compression/kernel-certification-first.json"
        history_path.parent.mkdir()
        history_path.write_text(json.dumps({"reused_CT_certificate": history}))
        inputs = [*owned, canonical, history_path]
        bindings = {source.relative_to(root).as_posix(): {"view_sha256": replay.sha(source.read_bytes()),
                    "source_sha256": replay.sha(source.read_bytes()), "source_revision": "a" * 40,
                    "source_revisions": ["a" * 40]} for source in inputs}
        provider = replay.RecordedSourceBindings(replay.PublicInputs(root, bindings))
        return provider, module, history, canonical, raw

    def test_owned_sources_and_full_kernel_scope_are_checked_without_private_history(self):
        with tempfile.TemporaryDirectory() as name:
            provider, module, history, canonical, raw = self.fixture(name)
            provider.patch_module(module)
            with patch.object(subprocess, "check_output", side_effect=AssertionError("Git must not be called")):
                self.assertEqual(module.fastconsume(), history)
                copy = Path(name) / "override.json"
                copy.write_bytes(canonical.read_bytes())
                self.assertEqual(module.fastconsume(copy), history)
            self.assertEqual(Path(module.__file__).read_bytes(), raw)
            adaptation = provider.adaptations[(provider.name(module.__file__), "fastconsume")]
            self.assertEqual(adaptation["owned_inputs_verified"], 15)
            self.assertFalse(adaptation["historical_dependency_closure_replayed"])
            self.assertFalse(adaptation["historical_lake_registry_replayed"])
            provider.patch_module(module)

    def test_disabled_preserves_original_no_read_behavior_and_lookalikes_are_rejected(self):
        with tempfile.TemporaryDirectory() as name:
            provider, module, _, canonical, _ = self.fixture(name)
            provider.patch_module(module)
            with patch.object(Path, "read_bytes", side_effect=AssertionError("disabled read")):
                self.assertFalse(module.fastconsume("/foreign", disabled=True)["evidence_valid"])
            copy = Path(name) / "lookalike.json"
            copy.write_bytes(canonical.read_bytes() + b"\n")
            with self.assertRaisesRegex(ValueError, "immutable original-byte copy"):
                module.fastconsume(copy)

    def test_original_scope_std3_source_and_historical_context_guards_stay_active(self):
        mutations = (lambda cert: cert.update(kernel_claims={"controller_advance": True}),
                     lambda cert: cert["source_audit"]["public_axioms"].update({"P23.OriginalSource.consumer": ["new_axiom"]}),
                     lambda cert: cert["bindings"][next(iter(cert["bindings"]))].update(sha256="0" * 64),
                     lambda cert: cert["historical_lake_binding"].update(sha256="0" * 64))
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index), tempfile.TemporaryDirectory() as name:
                provider, module, _, _, _ = self.fixture(name, mutate)
                provider.patch_module(module)
                with self.assertRaises((ValueError, replay.ReplayError)):
                    module.fastconsume()

    def test_changed_historical_guard_requires_review(self):
        with tempfile.TemporaryDirectory() as name:
            provider, module, _, _, _ = self.fixture(name, changed_guard=True)
            with self.assertRaisesRegex(replay.ReplayError, "provenance statements changed"):
                provider.patch_module(module)


class HistoricalSourceViewTests(unittest.TestCase):
    def fixture(self, directory, mathematical_change=False):
        root = Path(directory).resolve()
        name = replay.BELL + "/nist-real/nominal-replay/public-review/multi-window/source_verify.py"
        original = Path(__file__).resolve().parents[1] / ("scripts/first-release/ad/" + name.removeprefix("Verification/"))
        current = original.read_bytes()
        historical = current + b"\n"
        if mathematical_change:
            historical = historical.replace(b"def primary_tree(", b"def changed_primary_tree(", 1)
        views = []
        for label, commit, raw in (("current", "a" * 40, current), ("historical", "b" * 40, historical)):
            view_root = root / label
            path = view_root / name
            path.parent.mkdir(parents=True)
            path.write_bytes(raw)
            bindings = {name: {"view_sha256": replay.sha(raw), "source_sha256": replay.sha(raw),
                               "source_revision": commit, "source_revisions": [commit]}}
            views.append({"root": str(view_root), "bindings": bindings})
        inputs = replay.PublicInputs(Path(views[0]["root"]), views[0]["bindings"], views[1:])
        provider = replay.RecordedSourceBindings(inputs)
        module = ModuleType("original_source_audit")
        module.__dict__.update(__file__=str(inputs.path(name)), ROOT=inputs.root, hashlib=replay.hashlib,
                               Path=Path, subprocess=subprocess, frozen=lambda _: None, digest=lambda _: None)
        functions = [node for node in replay.ast.parse(current).body if isinstance(node, replay.ast.FunctionDef) and
                     node.name in {"require", "certificate_bindings", "bind_check"}]
        exec(compile(replay.ast.Module(body=functions, type_ignores=[]), module.__file__, "exec"), module.__dict__)
        report = {"bindings": [{"path": name, "commit": "b" * 40, "sha256": replay.sha(historical)}]}
        return provider, module, report, views

    def test_original_math_ast_and_its_mutation_control_use_real_historical_bytes(self):
        with tempfile.TemporaryDirectory() as name:
            provider, module, report, _ = self.fixture(name)
            provider.patch_module(module)
            with patch.object(subprocess, "check_output", side_effect=AssertionError("Git must not be called")):
                result = module.certificate_bindings(report)
            self.assertTrue(result["mathematical_source_audit_AST_unchanged"])
            self.assertTrue(result["mathematical_audit_change_negative_control_rejected"])
            self.assertNotEqual(result["historical_generation_driver"]["sha256"], result["current_readout_implementation"]["sha256"])
            provider.inputs.verify_all()

    def test_actual_changed_math_and_unregistered_epoch_are_rejected(self):
        with tempfile.TemporaryDirectory() as name:
            provider, module, report, _ = self.fixture(name, mathematical_change=True)
            provider.patch_module(module)
            with self.assertRaisesRegex(ValueError, "changed_mathematical_source_audit"):
                module.certificate_bindings(report)
        with tempfile.TemporaryDirectory() as name:
            provider, module, report, _ = self.fixture(name)
            provider.patch_module(module)
            report["bindings"][0]["commit"] = "c" * 40
            with self.assertRaisesRegex(replay.ReplayError, "no unambiguous verified byte supplier"):
                module.certificate_bindings(report)

    def test_history_tampering_and_undeclared_git_fallback_stay_rejected(self):
        with tempfile.TemporaryDirectory() as name:
            provider, _, report, views = self.fixture(name)
            row = report["bindings"][0]
            path = Path(views[1]["root"]) / row["path"]
            path.write_bytes(b"changed historical source")
            with self.assertRaisesRegex(replay.ReplayError, "Source-view input changed"):
                provider.historical_bytes(row)
            with self.assertRaises(replay.ReplayError):
                provider.inputs.verify_all()
            provider.inputs.historical = []
            with self.assertRaisesRegex(replay.ReplayError, "no unambiguous verified byte supplier"):
                provider.historical_bytes(row)

    def test_historical_views_require_an_explicit_nist_configuration(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "runtime.json"
            check = {"id": "nist-domain", "tier": "bell", "kind": "nist-witness-consumers", "view": "current"}
            config = {"schema": replay.SCHEMA, "views": {"current": {}, "historical": {}}, "checks": [check]}
            path.write_text(json.dumps(config))
            self.assertNotIn("historical_views", replay.load_config(path)["checks"][0])
            check["historical_views"] = ["historical"]
            path.write_text(json.dumps(config))
            self.assertEqual(replay.load_config(path)["checks"][0]["historical_views"], ["historical"])
            for invalid in (["unknown"], ["historical", "historical"], "historical"):
                check["historical_views"] = invalid
                path.write_text(json.dumps(config))
                with self.assertRaises(replay.ReplayError):
                    replay.load_config(path)
            check.update(kind="nist-nominal-replay", historical_views=["historical"])
            path.write_text(json.dumps(config))
            with self.assertRaises(replay.ReplayError):
                replay.load_config(path)


class OriginalControlImportIsolationTests(unittest.TestCase):
    def test_plain_import_reads_its_original_directory_and_parent_modules_are_restored(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            original = replay.BELL + "/nist-real/nominal-replay/public-review/source-compression/test_independent.py"
            dependency = str(Path(original).parent / "independent.py")
            source = root / original
            source.parent.mkdir(parents=True)
            source.write_text("import independent\nassert independent.original_value == 7\nraise SystemExit(0)\n")
            (root / dependency).write_text("original_value = 7\n")
            bindings = {value: {"view_sha256": replay.sha((root / value).read_bytes()),
                               "source_sha256": replay.sha((root / value).read_bytes()),
                               "source_revision": "a" * 40, "source_revisions": ["a" * 40]}
                        for value in (original, dependency)}
            provider = replay.RecordedSourceBindings(replay.PublicInputs(root, bindings))
            stale = ModuleType("independent")
            stale.__file__ = str(root / "prior-consumer/independent.py")
            stale.original_value = 99
            prior_path = sys.path[:]
            with patch.dict(sys.modules, {"independent": stale}):
                sys.path.insert(0, str(root / "prior-consumer"))
                try:
                    with replay.original_source_metadata(provider):
                        completed = provider.controls(["python3", str(source)])
                    self.assertEqual(completed.returncode, 0)
                    self.assertIs(sys.modules["independent"], stale)
                    self.assertEqual(stale.original_value, 99)
                finally:
                    sys.path[:] = prior_path

    def test_failed_original_control_keeps_its_exit_and_does_not_leak_loaded_source(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            original = replay.BELL + "/nist-real/nominal-replay/public-review/source-compression/test_domain.py"
            source = root / original
            source.parent.mkdir(parents=True)
            source.write_text("import _h0_control_local_source\nraise SystemExit(3)\n")
            dependency = str(Path(original).parent / "_h0_control_local_source.py")
            (root / dependency).write_text("original_value = 7\n")
            bindings = {value: {"view_sha256": replay.sha((root / value).read_bytes()),
                               "source_sha256": replay.sha((root / value).read_bytes()),
                               "source_revision": "a" * 40, "source_revisions": ["a" * 40]}
                        for value in (original, dependency)}
            provider = replay.RecordedSourceBindings(replay.PublicInputs(root, bindings))
            with replay.original_source_metadata(provider):
                completed = provider.controls(["python3", str(source)])
            self.assertEqual(completed.returncode, 3)
            self.assertNotIn("_h0_control_local_source", sys.modules)

    def test_munich_explicit_hardware_intake_override_remains_available_to_its_controls(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            original = replay.BELL + "/munich/readout-domain/test_hardware_anchors_run.py"
            dependency = str(Path(original).parent / "hardware_anchors_run.py")
            source = root / original
            source.parent.mkdir(parents=True)
            source.write_text("import hardware_anchors_run\nassert hardware_anchors_run.public_intake() == 7\n")
            (root / dependency).write_text("raise AssertionError('original private intake must remain adapted')\n")
            bindings = {value: {"view_sha256": replay.sha((root / value).read_bytes()),
                               "source_sha256": replay.sha((root / value).read_bytes()),
                               "source_revision": "a" * 40, "source_revisions": ["a" * 40]}
                        for value in (original, dependency)}
            provider = replay.RecordedSourceBindings(replay.PublicInputs(root, bindings))
            adapted = ModuleType("hardware_anchors_run")
            adapted.__file__ = str(root / dependency)
            adapted.public_intake = lambda: 7
            with patch.dict(sys.modules, {"hardware_anchors_run": adapted}), replay.original_source_metadata(provider):
                completed = provider.controls(["python3", str(source)])
                self.assertEqual(completed.returncode, 0)
                self.assertIs(sys.modules["hardware_anchors_run"], adapted)
            self.assertFalse(provider.adaptations[(original, "control-import-state")]["source_module_cache_isolated"])


class QuantumAggregateTests(unittest.TestCase):
    def setUp(self):
        import first_release_quantum as quantum
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'tools').mkdir()
        (self.root / 'tools/first_release_quantum.py').write_text('# public child CLI fixture\n')
        checks = []
        for name, (tag, stem) in quantum.CASES.items():
            program = replay.ECD + '/independent_source_' + stem + '.py'
            checks.append({'id': name, 'ref': quantum.REVISIONS[tag], 'program': program, 'function': 'main',
                           'output': program[:-3] + '.json',
                           'producer': {'program': replay.ECD + '/source_' + stem + '.py'},
                           'paths': ['fixture/source.py'], 'expected_source_sha256': {'fixture/source.py': '0' * 64}})
        self.config = {'schema': quantum.SCHEMA, 'ignored_result_pointers': ['/elapsed_seconds'],
                       'checks': checks, 'required': [row['id'] for row in checks]}
        self.path = self.root / 'checks/quantum.json'
        self.path.parent.mkdir()
        self.path.write_text(json.dumps(self.config))
        self.config_sha, self.map_sha = replay.sha(self.path.read_bytes()), 'f' * 64
        self.schema = quantum.REPORT_SCHEMA

    def tearDown(self):
        self.temp.cleanup()

    def child_run(self, adjust=None, ids=None, returncode=0, label='new'):
        check = {'kind': 'quantum-independent', 'quantum_config': 'checks/quantum.json',
                 'quantum_config_sha256': self.config_sha}
        if ids is not None:
            check['ids'] = ids
        output = self.root / '.local' / label
        output.mkdir(parents=True)
        selected = [row['id'] for row in self.config['checks'] if ids is None or row['id'] in ids]
        report = {'schema': self.schema, 'status': 'passed', 'exit_code': 0,
                  'selected': selected, 'config_sha256': self.config_sha, 'map_sha256': self.map_sha,
                  'complete_carrier_scope': len(selected) == len(self.config['checks']),
                  'checks': [{'id': name, 'status': 'passed', 'exit_code': 0, 'actual_process_exit_code': 0}
                             for name in selected]}
        if adjust:
            adjust(report)
        def producer(command, **kwargs):
            self.assertEqual(command, replay.quantum_command(check, output, 'python'))
            directory = output / 'quantum'
            directory.mkdir()
            (directory / 'report.json').write_text(json.dumps(report))
            return SimpleNamespace(returncode=returncode, stdout='native result', stderr='native failure evidence')
        with patch.object(replay, 'ROOT', self.root), patch.object(replay.subprocess, 'run', side_effect=producer):
            return replay.quantum_independent(check, output, 'python', self.map_sha), output

    def test_all_original_carriers_and_actual_exits_are_required_for_full_success(self):
        result, output = self.child_run()
        self.assertEqual(result['scope'], self.config['required'])
        self.assertTrue(result['complete_carrier_scope'])
        self.assertEqual(result['actual_process_exit_code'], 0)
        self.assertEqual(result['quantum_config']['sha256'], self.config_sha)
        self.assertEqual((output / 'quantum.stdout.log').read_text(), 'native result')

    def test_explicit_subset_keeps_its_actual_scope(self):
        names = self.config['required'][:2]
        result, _ = self.child_run(ids=names)
        self.assertEqual(result['scope'], names)
        self.assertFalse(result['complete_carrier_scope'])

    def test_missing_carrier_and_status_without_worker_exits_are_rejected(self):
        for label, adjust in (
            ('missing', lambda report: report['checks'].pop()),
            ('status-only', lambda report: [row.pop('actual_process_exit_code') for row in report['checks']])):
            with self.subTest(label=label), self.assertRaises(replay.ReplayError):
                self.child_run(adjust, label=label)

    def test_original_failure_exit_is_preserved(self):
        def failed(report):
            report.update(status='failed', exit_code=1)
            report['checks'][0].update(status='failed', exit_code=1, actual_process_exit_code=1)
        with self.assertRaisesRegex(replay.ReplayError, self.config['required'][0]):
            self.child_run(failed, returncode=1)
        self.assertEqual((self.root / '.local/new/quantum.stderr.log').read_text(), 'native failure evidence')
        self.assertEqual(json.loads((self.root / '.local/new/quantum/report.json').read_text())['exit_code'], 1)

    def test_config_and_export_identity_cannot_change_between_parent_and_child(self):
        for field in ('map_sha256', 'config_sha256'):
            with self.subTest(field=field), self.assertRaisesRegex(replay.ReplayError, 'different configuration'):
                self.child_run(lambda report: report.update({field: '0' * 64}), label=field)

    def test_runtime_accepts_the_quantum_cli_without_a_shared_source_view(self):
        path = self.root / 'runtime.json'
        check = {'id': 'quantum-independent', 'kind': 'quantum-independent', 'tier': 'full'}
        config = {'schema': replay.SCHEMA, 'views': {}, 'checks': [check]}
        path.write_text(json.dumps(config))
        loaded = replay.load_config(path)['checks'][0]
        self.assertEqual(loaded['quantum_config'], 'checks/first-release-quantum.json')
        override = {**check, 'quantum_config': 'checks/quantum.json', 'ids': self.config['required'][:2]}
        path.write_text(json.dumps({**config, 'checks': [override]}))
        self.assertEqual(replay.load_config(path)['checks'][0]['ids'], self.config['required'][:2])
        for bad in ([], [self.config['required'][0]] * 2, ['../source']):
            path.write_text(json.dumps({**config, 'checks': [{**check, 'ids': bad}]}))
            with self.subTest(ids=bad), self.assertRaises(replay.ReplayError):
                replay.load_config(path)


if __name__ == "__main__":
    unittest.main()
