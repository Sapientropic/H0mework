"""Public-map and run-receipt fixtures; no Lean build or scientific execution."""
import copy
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import first_release as f


class FirstReleaseTests(unittest.TestCase):
    def setUp(self):
        directory = f.ROOT / ".local" / "first-release-20261004"
        directory.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="tool-fixture-", dir=directory)
        self.root = Path(self.temp.name)
        (self.root / "Lean").mkdir()
        (self.root / "docs").mkdir()
        (self.root / "tools").mkdir()
        (self.root / ".gitignore").write_text(".local/\n")
        subprocess.run(["git", "init", "--quiet", str(self.root)], check=True, capture_output=True)
        (self.root / "Lean/lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")
        (self.root / "Lean/lake-manifest.json").write_text('{"packages":[]}\n')
        (self.root / "Lean/lakefile.toml").write_text(
            'name = "H0mework"\nmoreLeanArgs = ["--trust=0"]\n'
            '[[lean_lib]]\nname = "H0mework"\nmoreLeanArgs = ["-DwarningAsError=true"]\n')
        self.export = {"schema": 2, "modules": [], "artifacts": [], "paper_aggregators": {}}
        self.data = {"schema": f.SCHEMA, "claims": [], "proof_packages": [], "checks": []}
        self.add_package("A", "1" * 40)
        self.save()
        self.calls = []

    def tearDown(self):
        self.temp.cleanup()

    def add_package(self, label, commit):
        module = f"H0mework.Sample.{label}"
        path = f.module_path(module)
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text("namespace Example\ndef value : Nat := 1\nend Example\n")
        digest = f.sha(file.read_bytes())
        row = {"path": path, "source_path": f"Lean/Original/{label}.lean", "source_revision": commit,
               "source_revisions": [commit], "source_sha256": digest, "target_sha256": digest,
               "target": module, "variant": label}
        self.export["modules"].append(row)
        entry = {"source_commit": commit, "source_path": row["source_path"], "source_sha256": digest,
                 "declarations": [{"namespace": "Example", "name": "value", "kind": "def", "line": 2}],
                 "public": {"path": path, "module": module, "sha256": digest, "variant": label},
                 "verification": {"identity": "mapped", "kernel": "pending"}}
        self.data["claims"].append({"id": f"core.{label}", "paper": "core", "selection_status": "provisional",
                                    "producers": [entry], "direct_consumers": [], "resources": []})
        target = f"H0mework.Papers.Core{label}"
        target_path = f.module_path(target)
        (self.root / target_path).parent.mkdir(parents=True, exist_ok=True)
        (self.root / target_path).write_text(f"import {module}\n")
        self.export["paper_aggregators"][target] = target_path
        self.data["proof_packages"].append({"id": f"core-{label}", "paper": "core", "source_alias": label,
                                           "source_commit": commit, "lean_target": target})

    def save(self, path=f.MAP):
        (self.root / path).parent.mkdir(parents=True, exist_ok=True)
        (self.root / path).write_text(json.dumps(self.data))
        (self.root / f.EXPORT_MAP).write_text(json.dumps(self.export))

    @property
    def entry(self):
        return self.data["claims"][0]["producers"][0]

    def fake_run(self, command, root, log, environment):
        self.calls.append(command)
        output = "fixture execution only\n"
        if "lean" in command and command[-1].endswith(".lean"):
            scope = json.loads(log.with_name(log.stem + "-scope.json").read_text())
            report = {"token": scope["token"], "roots": len(scope["declarations"]), "constants": 3,
                      "edges": 2, "axioms": [], "unsafe": 0, "partial": 0, "full_metadata": True}
            output += "FIRST_RELEASE_TRUST " + json.dumps(report) + "\n"
        log.write_text(output)
        return {"command": command, "cwd": "Lean", "exit_code": 0, "elapsed_seconds": 0.001,
                "error": None, "log": log.relative_to(root).as_posix()}

    def add_artifact_producer(self):
        path = "scripts/replay.py"
        file = self.root / path
        file.parent.mkdir(parents=True)
        file.write_text("def verify():\n    return 7\n")
        digest = f.sha(file.read_bytes())
        self.export["artifacts"].append({"path": path, "source": "Verification/replay.py",
            "source_revision": "1" * 40, "source_revisions": ["1" * 40],
            "source_sha256": digest, "target_sha256": digest})
        entry = {"kind": "artifact", "source_commit": "1" * 40, "source_path": "Verification/replay.py",
            "source_sha256": digest, "public": {"path": path, "sha256": digest},
            "verification": {"identity": "mapped", "kernel": "passed"}}
        self.data["claims"][0]["producers"].append(entry)
        return entry

    def test_mapped_identity_does_not_certify_pending_kernel(self):
        result = f.verify_map(self.root)
        self.assertTrue(result["ok"])
        self.assertTrue(result["identity_ready"])
        self.assertFalse(result["ready_requirement_met"])
        self.assertEqual(result["pending"], {"identity": 0, "kernel": 1, "resources": 0, "runtime": 0})
        self.assertEqual(result["entries"][0]["identity"], "verified")
        self.assertEqual(result["publication_readiness"], "not_assessed")
        self.assertFalse(f.verify_map(self.root, require_ready=True)["ok"])

    def test_recorded_pass_remains_a_recorded_status(self):
        self.entry["verification"]["kernel"] = "passed"
        self.save()
        result = f.verify_map(self.root, require_ready=True)
        self.assertTrue(result["ok"])
        self.assertEqual(result["publication_readiness"], "not_assessed")
        self.assertIn("does not execute Lean", result["kernel_status_scope"])

    def test_null_public_is_explicit_pending(self):
        self.entry["public"] = None
        self.entry["source_sha256"] = None
        self.save()
        result = f.verify_map(self.root)
        self.assertTrue(result["ok"])
        self.assertFalse(result["identity_ready"])
        self.assertEqual(result["pending"]["identity"], 1)
        self.assertEqual(result["mapped"], 0)
        self.assertFalse(f.verify_map(self.root, require_ready=True)["ok"])

    def test_pending_resource_never_looks_ready(self):
        self.data["claims"][0]["resources"] = [{"source_commit": "1" * 40,
            "source_path": "Original receipt (historical).json", "public": None, "verification": "pending"}]
        self.save()
        result = f.verify_map(self.root)
        self.assertTrue(result["ok"])
        self.assertEqual(result["pending"]["resources"], 1)
        self.assertFalse(result["identity_ready"])

    def test_artifact_identity_never_counts_as_kernel_or_runtime_acceptance(self):
        self.add_artifact_producer()
        self.entry["verification"]["kernel"] = "passed"
        self.data["claims"][0]["scientific_verification"] = {"status": "pending", "check_ids": ["original-replay"]}
        self.save()
        result = f.verify_map(self.root)
        self.assertTrue(result["ok"])
        self.assertTrue(result["identity_ready"])
        self.assertEqual(result["pending"]["kernel"], 0)
        self.assertEqual(result["pending"]["runtime"], 1)
        self.assertNotIn("recorded_kernel", result["entries"][1])
        self.assertEqual(result["scientific_verification"][0]["check_ids"], ["original-replay"])
        self.assertFalse(f.verify_map(self.root, require_ready=True)["ok"])

    def test_artifact_uses_its_own_export_index_and_byte_hash(self):
        artifact = self.add_artifact_producer()
        self.save()
        self.assertTrue(f.verify_map(self.root)["ok"])
        artifact.pop("kind")
        self.save()
        self.assertIn("modules export row", f.verify_map(self.root)["errors"][0]["error"])
        artifact["kind"] = "artifact"
        artifact["public"]["sha256"] = "f" * 64
        self.save()
        self.assertIn("Public hash differs", f.verify_map(self.root)["errors"][0]["error"])

    def test_artifact_null_and_traversal_are_explicit(self):
        artifact = self.add_artifact_producer()
        artifact["public"] = None
        self.save()
        result = f.verify_map(self.root)
        self.assertTrue(result["ok"])
        self.assertEqual(result["pending"]["identity"], 1)
        self.assertEqual(result["pending"]["runtime"], 1)
        artifact["source_path"] = "../replay.py"
        self.save()
        self.assertIn("Unsafe repository path", f.verify_map(self.root)["errors"][0]["error"])

    def test_proof_package_selects_lean_entries_only(self):
        artifact = self.add_artifact_producer()
        artifact["public"] = None
        self.save()
        entries = f.package_entries(f.selected_claims(self.data), self.data["proof_packages"][0])
        self.assertEqual(len(entries), 1)
        self.assertIs(entries[0][3], self.entry)
        with patch.object(f, "run_process", side_effect=self.fake_run):
            result = f.execute("build", self.root, f.MAP, ".local/proof-only-build")
        self.assertTrue(result["ok"])
        self.assertFalse(f.verify_map(self.root, require_ready=True)["ok"])

    def test_lean_entry_cannot_be_reclassified_to_skip_its_kernel_gate(self):
        self.entry["kind"] = "artifact"
        self.save()
        self.assertIn("retain their kernel gate", f.verify_map(self.root)["errors"][0]["error"])
        with self.assertRaisesRegex(f.ReleaseError, "retain their kernel gate"):
            f.package_entries(f.selected_claims(self.data), self.data["proof_packages"][0])

    def test_altered_public_bytes_fail(self):
        (self.root / self.entry["public"]["path"]).write_text("namespace Example\ndef value := 2\nend Example\n")
        result = f.verify_map(self.root)
        self.assertFalse(result["ok"])
        self.assertIn("Public bytes differ", result["errors"][0]["error"])

    def test_altered_recorded_hash_fails(self):
        self.entry["public"]["sha256"] = "f" * 64
        self.save()
        self.assertIn("Public hash differs", f.verify_map(self.root)["errors"][0]["error"])

    def test_source_sha_and_commit_must_match_exact_export_row(self):
        original = copy.deepcopy(self.entry)
        for key, value, message in [("source_sha256", "f" * 64, "Source hash differs"),
                                    ("source_commit", "f" * 40, "Source revision is absent"),
                                    ("source_commit", "1234567", "complete 40-character")]:
            with self.subTest(key=key, value=value):
                self.entry.update(copy.deepcopy(original))
                self.entry[key] = value
                self.save()
                self.assertIn(message, f.verify_map(self.root)["errors"][0]["error"])

    def test_source_revision_reuse_is_explicit(self):
        self.export["modules"][0]["source_revisions"].append("2" * 40)
        self.entry["source_commit"] = "2" * 40
        self.save()
        self.assertTrue(f.verify_map(self.root)["ok"])

    def test_supplement_origin_must_match_the_export_record(self):
        origin = {"kind": "git-source-supplement", "source_commit": "2" * 40,
                  "source_path": "Lean/Original/A.lean", "source_sha256": self.entry["source_sha256"]}
        self.export["modules"][0]["source_origin"] = origin
        self.save()
        self.assertIn("Source origin differs", f.verify_map(self.root)["errors"][0]["error"])
        self.entry["source_origin"] = copy.deepcopy(origin)
        self.save()
        self.assertTrue(f.verify_map(self.root)["ok"])

    def test_runtime_check_does_not_close_an_unchecked_contract(self):
        self.add_artifact_producer()
        claim = self.data["claims"][0]
        claim["scientific_verification"] = {"status": "passed", "check_ids": ["partial-check"]}
        claim["runtime_contracts"] = [{"id": "complete-original-run", "verification": "pending"}]
        self.entry["verification"]["kernel"] = "passed"
        self.save()
        result = f.verify_map(self.root, require_ready=True)
        self.assertFalse(result["ok"])
        self.assertEqual(result["pending"]["runtime"], 1)
        self.assertEqual(result["scientific_verification"][0]["pending_contract_ids"], ["complete-original-run"])
        claim["runtime_contracts"][0]["verification"] = {"status": "passed", "receipt": "recorded-run.json"}
        self.save()
        recorded = f.verify_map(self.root, require_ready=True)
        self.assertTrue(recorded["ok"])
        self.assertEqual(recorded["publication_readiness"], "not_assessed")

    def test_missing_export_row_fails(self):
        self.export["modules"] = []
        self.save()
        self.assertIn("found 0", f.verify_map(self.root)["errors"][0]["error"])

    def test_missing_producer_or_declaration_roots_fail(self):
        self.entry["declarations"] = []
        self.save()
        self.assertIn("no declaration roots", f.verify_map(self.root)["errors"][0]["error"])
        self.data["claims"][0]["producers"] = []
        self.save()
        with self.assertRaisesRegex(f.ReleaseError, "no producer"):
            f.verify_map(self.root)

    def test_traversal_is_rejected_even_for_pending_entries(self):
        for path in ("../outside.lean", "/tmp/outside.lean", "Lean/../../outside.lean", "Lean\\..\\outside.lean"):
            with self.subTest(path=path):
                self.entry["public"] = None
                self.entry["source_path"] = path
                self.save()
                result = f.verify_map(self.root)
                self.assertFalse(result["ok"])
                self.assertIn("Unsafe repository path", result["errors"][0]["error"])

    def test_public_symlink_cannot_escape_repo(self):
        target = self.root.parent / (self.root.name + "-outside.lean")
        target.write_bytes((self.root / self.entry["public"]["path"]).read_bytes())
        self.addCleanup(target.unlink)
        path = self.root / self.entry["public"]["path"]
        path.unlink()
        path.symlink_to(target)
        self.assertIn("escapes repository", f.verify_map(self.root)["errors"][0]["error"])

    def test_public_module_and_variant_are_checked(self):
        self.entry["public"]["module"] = "H0mework.Other"
        self.save()
        self.assertIn("module/path differs", f.verify_map(self.root)["errors"][0]["error"])
        self.entry["public"]["module"] = "H0mework.Sample.A"
        self.entry["public"]["variant"] = "B"
        self.save()
        self.assertIn("variant differs", f.verify_map(self.root)["errors"][0]["error"])

    def test_duplicate_claim_or_package_is_rejected(self):
        self.data["claims"].append(copy.deepcopy(self.data["claims"][0]))
        self.save()
        with self.assertRaisesRegex(f.ReleaseError, "Duplicate claim"):
            f.verify_map(self.root)
        with self.assertRaisesRegex(f.ReleaseError, "Duplicate proof package"):
            f.packages({"proof_packages": self.data["proof_packages"] * 2})

    def test_all_independent_targets_run_in_one_build(self):
        self.add_package("B", "2" * 40)
        self.save()
        with patch.object(f, "run_process", side_effect=self.fake_run):
            result = f.execute("build", self.root, f.MAP, ".local/new-build")
        self.assertTrue(result["ok"])
        self.assertEqual(self.calls, [["lake", "build", "H0mework.Papers.CoreA", "H0mework.Papers.CoreB"]])
        self.assertTrue((self.root / ".local/new-build/result.json").is_file())
        self.assertFalse(result["cache"]["clean_clone"])
        self.assertEqual(result["input_identity"], result["input_identity_after"])

    def test_build_parallelism_uses_cpu_and_memory(self):
        with patch.dict(f.os.environ, {}, clear=True), patch.object(f.os, "cpu_count", return_value=18), \
                patch.object(f.os, "sched_getaffinity", return_value=set(range(18)), create=True), \
                patch.object(f.os, "sysconf", side_effect=[128 * 1024**3, 1]), \
                patch.object(f.Path, "read_text", side_effect=OSError):
            self.assertEqual(f.build_environment()["LEAN_NUM_THREADS"], "8")

    def test_build_parallelism_limits_small_machines(self):
        for cpus, gib, expected in ((2, 128, "2"), (18, 32, "2"), (18, 8, "1")):
            with self.subTest(cpus=cpus, gib=gib), patch.dict(f.os.environ, {}, clear=True), \
                    patch.object(f.os, "cpu_count", return_value=cpus), \
                    patch.object(f.os, "sched_getaffinity", return_value=set(range(cpus)), create=True), \
                    patch.object(f.os, "sysconf", side_effect=[gib * 1024**3, 1]), \
                    patch.object(f.Path, "read_text", side_effect=OSError):
                self.assertEqual(f.build_environment()["LEAN_NUM_THREADS"], expected)

    def test_build_parallelism_honors_explicit_override(self):
        with patch.dict(f.os.environ, {"LEAN_NUM_THREADS": "6", "UNRELATED_SETTING": "kept"}, clear=True), \
                patch.object(f.os, "cpu_count", side_effect=AssertionError("override needs no probes")):
            environment = f.build_environment()
        self.assertEqual(environment["LEAN_NUM_THREADS"], "6")
        self.assertEqual(environment["UNRELATED_SETTING"], "kept")

    def test_build_parallelism_unknown_memory_keeps_bounded_fallback(self):
        with patch.dict(f.os.environ, {}, clear=True), patch.object(f.os, "cpu_count", return_value=18), \
                patch.object(f.os, "sched_getaffinity", return_value=set(range(18)), create=True), \
                patch.object(f.os, "sysconf", side_effect=ValueError), \
                patch.object(f.Path, "read_text", side_effect=OSError):
            self.assertEqual(f.build_environment()["LEAN_NUM_THREADS"], "2")

    def test_build_parallelism_honors_container_memory_limit(self):
        with patch.dict(f.os.environ, {}, clear=True), patch.object(f.os, "cpu_count", return_value=18), \
                patch.object(f.os, "sched_getaffinity", return_value=set(range(18)), create=True), \
                patch.object(f.os, "sysconf", side_effect=[128 * 1024**3, 1]), \
                patch.object(f.Path, "read_text", side_effect=[str(8 * 1024**3), OSError()]):
            self.assertEqual(f.build_environment()["LEAN_NUM_THREADS"], "1")

    def test_build_parallelism_does_not_treat_other_settings_as_override(self):
        with patch.dict(f.os.environ, {"LAKE_NUM_THREADS": "1"}, clear=True), \
                patch.object(f.os, "cpu_count", return_value=18), \
                patch.object(f.os, "sched_getaffinity", return_value=set(range(18)), create=True), \
                patch.object(f.os, "sysconf", side_effect=[128 * 1024**3, 1]), \
                patch.object(f.Path, "read_text", side_effect=OSError):
            self.assertEqual(f.build_environment()["LEAN_NUM_THREADS"], "8")

    def test_invalid_build_parallelism_fails_before_creating_output(self):
        for value in ("", "0", "-1", "2.5", "auto"):
            with self.subTest(value=value), patch.dict(f.os.environ, {"LEAN_NUM_THREADS": value}, clear=True), \
                    patch.object(f, "run_process", side_effect=self.fake_run), \
                    self.assertRaisesRegex(f.ReleaseError, "positive integer"):
                f.execute("build", self.root, f.MAP, ".local/invalid-parallelism")
            self.assertFalse((self.root / ".local/invalid-parallelism").exists())
        self.assertFalse(self.calls)

    def test_build_parallelism_honors_cpu_affinity(self):
        with patch.dict(f.os.environ, {}, clear=True), patch.object(f.os, "cpu_count", return_value=18), \
                patch.object(f.os, "sched_getaffinity", return_value={0, 1}, create=True), \
                patch.object(f.os, "sysconf", side_effect=[128 * 1024**3, 1]), \
                patch.object(f.Path, "read_text", side_effect=OSError):
            self.assertEqual(f.build_environment()["LEAN_NUM_THREADS"], "2")

    def test_explicit_package_map_and_output_override(self):
        self.add_package("B", "2" * 40)
        # An independent package can be accepted while another declaration
        # map is incomplete; the receipt names only the requested package.
        self.entry["declarations"] = []
        self.save("docs/override.json")
        stream = io.StringIO()
        with patch.object(f, "run_process", side_effect=self.fake_run), redirect_stdout(stream):
            code = f.main(["build", "--map", "docs/override.json", "--package", "core-B",
                           "--output", ".local/custom-output"], root=self.root)
        self.assertEqual(code, 0)
        self.assertEqual(self.calls, [["lake", "build", "H0mework.Papers.CoreB"]])
        self.assertEqual(json.loads(stream.getvalue())["receipt"], ".local/custom-output/result.json")
        self.assertEqual(json.loads(stream.getvalue())["identity_scope"]["packages"], ["core-B"])

    def test_output_is_new_and_ignored(self):
        for directory in ("docs/output", ".local", ".local/../docs/output"):
            with self.subTest(directory=directory), self.assertRaises(f.ReleaseError):
                f.new_output(self.root, directory)
        output = f.new_output(self.root, ".local/owned")
        (output / "keep").write_text("old evidence")
        with self.assertRaisesRegex(f.ReleaseError, "already exists"):
            f.new_output(self.root, output)
        self.assertEqual((output / "keep").read_text(), "old evidence")

    def test_pending_package_is_not_built(self):
        self.entry["public"] = None
        self.save()
        with patch.object(f, "run_process", side_effect=self.fake_run), self.assertRaisesRegex(f.ReleaseError, "pending public"):
            f.execute("build", self.root, f.MAP, ".local/missing-build")
        self.assertEqual(self.calls, [])
        self.assertFalse((self.root / ".local/missing-build").exists())

    def test_package_target_must_actually_import_its_declaring_modules(self):
        (self.root / "Lean/H0mework/Papers/CoreA.lean").write_text("import Lean\n")
        with self.assertRaisesRegex(f.ReleaseError, "not consumed"):
            f.execute("build", self.root, f.MAP, ".local/wrong-package")

    def test_import_closure_tampering_is_checked(self):
        helper = self.root / "Lean/H0mework/Helper.lean"
        helper.write_text("def helper := 7\n")
        target = self.root / "Lean/H0mework/Papers/CoreA.lean"
        target.write_text(target.read_text() + "import H0mework.Helper\n")
        with self.assertRaisesRegex(f.ReleaseError, "not registered"):
            f.execute("build", self.root, f.MAP, ".local/unregistered")

    def test_two_epochs_are_audited_in_separate_lean_files(self):
        self.add_package("B", "2" * 40)
        self.save()
        with patch.object(f, "run_process", side_effect=self.fake_run):
            result = f.execute("trust", self.root, f.MAP, ".local/trust")
        self.assertTrue(result["ok"])
        self.assertEqual(len(self.calls), 3)
        self.assertEqual(self.calls[0], ["lake", "--no-build", "build", "H0mework.Papers.CoreA", "H0mework.Papers.CoreB"])
        first = (self.root / ".local/trust/audit-001.lean").read_text()
        second = (self.root / ".local/trust/audit-002.lean").read_text()
        self.assertIn("import H0mework.Papers.CoreA", first)
        self.assertNotIn("import H0mework.Papers.CoreB", first)
        self.assertIn("import H0mework.Papers.CoreB", second)
        self.assertIn("info.type.getUsedConstantsAsSet", first)
        self.assertIn("val.all ++ val.ctors", first)
        self.assertIn("val.rules", first)
        self.assertIn("WRONG_DECLARATION_MODULE", first)
        self.assertIn("--trust=0", self.calls[1])
        self.assertIn("-DwarningAsError=true", self.calls[1])
        self.assertIn("--root=..", self.calls[1])

    def test_unbuilt_targets_do_not_produce_a_trust_pass(self):
        def stale(command, root, log, environment):
            result = self.fake_run(command, root, log, environment)
            result["exit_code"] = 1
            log.write_text("error: target is not built\n")
            return result
        with patch.object(f, "run_process", side_effect=stale):
            result = f.execute("trust", self.root, f.MAP, ".local/unbuilt")
        self.assertFalse(result["ok"])
        self.assertEqual(result["preflight"]["exit_code"], 1)
        self.assertEqual(result["results"], [])
        self.assertEqual(len(self.calls), 1)

    def test_independent_trust_checks_overlap_and_keep_receipt_order(self):
        self.add_package("B", "2" * 40)
        self.save()
        together = threading.Barrier(2)
        def concurrent(command, root, log, environment):
            if "lean" in command:
                together.wait(timeout=5)
            return self.fake_run(command, root, log, environment)
        with patch.dict(f.os.environ, {"LEAN_NUM_THREADS": "2"}), \
                patch.object(f, "run_process", side_effect=concurrent):
            result = f.execute("trust", self.root, f.MAP, ".local/concurrent-trust")
        self.assertTrue(result["ok"])
        self.assertEqual(result["cache"]["trust_jobs"], 2)
        self.assertEqual([row["package"] for row in result["results"]], ["core-A", "core-B"])
        self.assertEqual(result["input_identity"], result["input_identity_after"])

    def test_serial_override_and_package_failure_preserve_other_results(self):
        self.add_package("B", "2" * 40)
        self.save()
        def failure(command, root, log, environment):
            run = self.fake_run(command, root, log, environment)
            if log.name == "audit-001.log":
                run["exit_code"] = 1
                log.write_text("error: missing declaration\n")
            return run
        with patch.dict(f.os.environ, {"LEAN_NUM_THREADS": "1"}), \
                patch.object(f, "run_process", side_effect=failure):
            result = f.execute("trust", self.root, f.MAP, ".local/serial-failure")
        self.assertFalse(result["ok"])
        self.assertEqual(result["cache"]["trust_jobs"], 1)
        self.assertEqual([row["status"] for row in result["results"]], ["failed", "passed"])
        self.assertTrue(self.calls[1][-1].endswith("audit-001.lean"))
        self.assertTrue(self.calls[2][-1].endswith("audit-002.lean"))

    def test_zero_exit_without_scope_result_is_not_a_trust_pass(self):
        def missing(command, root, log, environment):
            result = self.fake_run(command, root, log, environment)
            log.write_text("no scope result\n")
            return result
        with patch.object(f, "run_process", side_effect=missing):
            result = f.execute("trust", self.root, f.MAP, ".local/no-result")
        self.assertFalse(result["ok"])
        self.assertEqual(result["results"][0]["exit_code"], 0)
        self.assertIn("exactly one audit result", result["results"][0]["error"])

    def test_actual_missing_declaration_failure_is_preserved(self):
        def missing(command, root, log, environment):
            result = self.fake_run(command, root, log, environment)
            if "lean" in command:
                log.write_text("error: MISSING_DECLARATION Example.missing\n")
                result["exit_code"] = 1
            return result
        with patch.object(f, "run_process", side_effect=missing):
            result = f.execute("trust", self.root, f.MAP, ".local/missing-declaration")
        self.assertFalse(result["ok"])
        self.assertEqual(result["results"][0]["exit_code"], 1)
        self.assertEqual(result["results"][0]["status"], "failed")
        self.assertNotIn("audit", result["results"][0])

    def test_unsafe_partial_or_custom_axiom_report_is_rejected(self):
        for field, value in (("unsafe", 1), ("partial", 1), ("axioms", ["sorryAx"])):
            with self.subTest(field=field):
                def bad(command, root, log, environment):
                    result = self.fake_run(command, root, log, environment)
                    if "lean" in command:
                        text = log.read_text()
                        marker = text.split("FIRST_RELEASE_TRUST ")[1]
                        record = json.loads(marker)
                        record[field] = value
                        log.write_text("FIRST_RELEASE_TRUST " + json.dumps(record) + "\n")
                    return result
                with patch.object(f, "run_process", side_effect=bad):
                    result = f.execute("trust", self.root, f.MAP, f".local/bad-{field}")
                self.assertFalse(result["ok"])

    def test_map_mutation_during_build_invalidates_receipt(self):
        def mutate(command, root, log, environment):
            result = self.fake_run(command, root, log, environment)
            self.data["checks"].append({"unrelated_change": True})
            self.save()
            return result
        with patch.object(f, "run_process", side_effect=mutate):
            result = f.execute("build", self.root, f.MAP, ".local/changing-map")
        self.assertFalse(result["ok"])
        self.assertFalse(result["inputs_unchanged"])
        self.assertEqual(result["results"][0]["exit_code"], 0)


if __name__ == "__main__":
    unittest.main()
