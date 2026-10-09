from contextlib import redirect_stdout
import hashlib
import io
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import first_release_cache as cache


class FirstReleaseCacheTests(unittest.TestCase):
    def test_report_path_selects_the_declared_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "run" / "quantum"
            root.mkdir(parents=True)
            report = root / "report.json"
            report.write_text("{}")
            self.assertEqual(cache.report_path(Path(directory), "quantum"), report)
            self.assertIsNone(cache.report_path(Path(directory), "bell"))

    def test_verify_accepts_a_passed_report_when_science_inputs_are_unchanged(self):
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=cache.ROOT, text=True).strip()
        with tempfile.TemporaryDirectory() as directory:
            artifact = Path(directory) / "artifact" / "run" / "quantum"
            artifact.mkdir(parents=True)
            report = {
                "status": "passed",
                "config_sha256": cache.sha(cache.ROOT / cache.CONFIGS["quantum"]),
                "map_sha256": hashlib.sha256(cache.original_map(head)).hexdigest(),
                "checks": [{"status": "passed", "exit_code": 0} for _ in range(18)],
            }
            (artifact / "report.json").write_text(json.dumps(report))
            output = Path(directory) / "reuse"
            github_output = Path(directory) / "github-output"
            with patch.dict(os.environ, {"GITHUB_OUTPUT": str(github_output)}, clear=False):
                cache.verify("quantum", str(Path(directory) / "artifact"), head, str(output))
            self.assertIn("reused=true", github_output.read_text())
            self.assertEqual(json.loads((output / "reuse.json").read_text())["status"], "reused")

    def test_bell_archive_binding_uses_current_bytes(self):
        archive = cache.ROOT / "evidence/first-release/bell-inputs/storz-2023-rawData.zip"
        report = {"checks": [{"result": {"archive": {"name": archive.name, "sha256": cache.sha(archive)}}}]}
        self.assertTrue(cache.current_archives_match(report))
        report["checks"][0]["result"]["archive"]["sha256"] = "0" * 64
        self.assertFalse(cache.current_archives_match(report))


class ScientificViewCacheTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.root = self.directory / "repo"
        self.root.mkdir()
        self.revision = "a" * 40
        self.module_source = "Lean/Demo/Input.lean"
        self.program_source = "Verification/science/program.py"
        self.output_source = "Verification/science/output.json"
        self.exported = {"schema": 2, "lean_directory": "Lean", "revisions": {"PIN": self.revision},
                         "modules": [], "artifacts": []}
        raw = b"def input : Nat := 1\n"
        self.write("Lean/H0mework/Demo/Input.lean", raw)
        self.exported["modules"].append({
            "source": "Demo.Input", "source_path": self.module_source,
            "target": "H0mework.Demo.Input", "path": "Lean/H0mework/Demo/Input.lean",
            "source_revision": self.revision, "source_revisions": [self.revision],
            "source_sha256": self.digest(raw), "target_sha256": self.digest(raw)})
        self.add_artifact(self.program_source, "scripts/science/program.py", b"print('source')\n")
        self.add_artifact(self.output_source, "evidence/science/frozen.json", b'{"value": 1}\n')
        self.add_artifact("Verification/history/reader.py", "scripts/history/reader.py", b"historical reader\n", "d" * 40)
        self.exported["revisions"]["OLD"] = "d" * 40
        self.write("evidence/first-release/bell-inputs/example.zip", b"original archive")
        self.write("scripts/public-input.py", b"public source\n")
        for path in cache.SCIENCE_PATHS:
            if path != "evidence/first-release/bell-inputs":
                self.write(path, b"fixed replay definition\n")
        for path in cache.VIEW_ENGINES:
            self.write(path, (cache.ROOT / path).read_bytes())
        bell = {
            "views": {"science": {"ref": "PIN", "paths": [self.module_source],
                                    "prefixes": ["Verification/science/"],
                                    "public_inputs": [{"path": "scripts/public-input.py",
                                                       "original_path": "Verification/public.py",
                                                       "sha256": cache.sha(self.root / "scripts/public-input.py"),
                                                       "source_repository": "https://example.org/upstream",
                                                       "source_commit": "b" * 40}]},
                      "historical": {"ref": "OLD", "prefixes": ["Verification/history/"]}},
            "checks": [{"id": "demo", "tier": "bell", "kind": "nist-witness-consumers", "view": "science",
                        "historical_views": ["historical"]}],
            "required": {"bell": ["demo"]}}
        quantum = {"checks": [{
            "id": "demo", "ref": self.revision, "output": self.output_source,
            "expected_source_sha256": {self.module_source: self.exported["modules"][0]["source_sha256"],
                                       self.program_source: self.exported["artifacts"][0]["source_sha256"],
                                       self.output_source: self.exported["artifacts"][1]["source_sha256"]},
            "frozen": "evidence/science/frozen.json",
            "frozen_source_sha256": self.exported["artifacts"][1]["source_sha256"],
            "frozen_sha256": self.exported["artifacts"][1]["target_sha256"]}]}
        self.write(cache.CONFIGS["bell"], json.dumps(bell).encode())
        self.write(cache.CONFIGS["quantum"], json.dumps(quantum).encode())
        self.save_map()
        self.git("init", "-q")
        self.git("config", "user.name", "Cache Test")
        self.git("config", "user.email", "cache-test@example.invalid")
        self.git("add", ".")
        self.git("commit", "-qm", "original scientific inputs")
        self.commit = self.git("rev-parse", "HEAD").strip()
        self.original_map_sha = cache.sha(self.root / "tools/export-map.json")

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True, stderr=subprocess.DEVNULL)

    def write(self, name, raw):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)

    def digest(self, raw):
        return hashlib.sha256(raw).hexdigest()

    def add_artifact(self, source, path, raw, revision=None):
        self.write(path, raw)
        revision = revision or self.revision
        self.exported["artifacts"].append({"source": source, "path": path, "target": path,
                                           "source_revision": revision, "source_revisions": [revision],
                                           "source_sha256": self.digest(raw), "target_sha256": self.digest(raw)})

    def save_map(self):
        self.write("tools/export-map.json", json.dumps(self.exported).encode())

    def verify(self, kind, map_sha=None):
        artifact = self.directory / "artifact" / kind
        artifact.mkdir(parents=True, exist_ok=True)
        report = {"status": "passed", "config_sha256": cache.sha(self.root / cache.CONFIGS[kind]),
                  "map_sha256": map_sha or self.original_map_sha,
                  "checks": [{"status": "passed", "exit_code": 0}]}
        if kind == "bell":
            report["checks"][0]["result"] = {"archive": {
                "name": "example.zip", "sha256": cache.sha(self.root / "evidence/first-release/bell-inputs/example.zip")}}
        (artifact / "report.json").write_text(json.dumps(report))
        destination = self.directory / "receipt" / kind
        with patch.object(cache, "ROOT", self.root), patch.object(cache, "EXPECTED_CHECKS", {"bell": 1, "quantum": 1}), \
                patch.dict(os.environ, {"GITHUB_OUTPUT": ""}), redirect_stdout(io.StringIO()):
            cache.verify(kind, str(self.directory / "artifact"), self.commit, str(destination))
        return json.loads((destination / "reuse.json").read_text())

    def assert_scopes(self, status):
        for kind in ("bell", "quantum"):
            with self.subTest(kind=kind):
                self.assertEqual(self.verify(kind)["status"], status)

    def test_unchanged_actual_views_are_reused(self):
        self.assert_scopes("reused")

    def test_unrelated_exports_and_new_revision_labels_preserve_both_scopes(self):
        self.add_artifact("Verification/unrelated/new.py", "scripts/unrelated/new.py", b"new source\n", "c" * 40)
        self.exported["revisions"]["NEW"] = "c" * 40
        self.exported["modules"][0]["source_revisions"].append("c" * 40)
        self.exported["artifacts"][0]["source_revisions"].append("c" * 40)
        self.save_map()
        self.assert_scopes("reused")

    def test_new_byte_version_outside_the_selected_epoch_preserves_both_scopes(self):
        self.add_artifact(self.program_source, "scripts/versions/new/program.py", b"new program\n", "c" * 40)
        self.save_map()
        self.assert_scopes("reused")

    def test_prefix_addition_at_another_epoch_is_not_a_bell_input(self):
        self.add_artifact("Verification/science/new.py", "scripts/science/new.py", b"new source\n", "c" * 40)
        self.save_map()
        self.assertEqual(self.verify("bell")["status"], "reused")

    def test_prefix_addition_at_the_selected_epoch_invalidates_bell(self):
        self.add_artifact("Verification/science/new.py", "scripts/science/new.py", b"new source\n")
        self.save_map()
        self.assertEqual(self.verify("bell")["status"], "miss")

    def test_removed_selected_map_row_invalidates_both_scopes(self):
        self.exported["artifacts"].pop(0)
        self.save_map()
        self.assert_scopes("miss")

    def test_tampered_selected_file_even_with_rewritten_current_digests_is_rejected(self):
        row = self.exported["artifacts"][0]
        raw = b"changed scientific program\n"
        self.write(row["path"], raw)
        row.update(source_sha256=self.digest(raw), target_sha256=self.digest(raw))
        self.save_map()
        self.assert_scopes("miss")

    def test_deleted_selected_file_is_rejected(self):
        (self.root / self.exported["modules"][0]["path"]).unlink()
        self.assert_scopes("miss")

    def test_report_must_bind_the_producing_commit_map(self):
        self.add_artifact("Verification/unrelated/new.py", "scripts/unrelated/new.py", b"new source\n")
        self.save_map()
        for kind in ("bell", "quantum"):
            with self.subTest(kind=kind):
                self.assertEqual(self.verify(kind, cache.sha(self.root / "tools/export-map.json"))["status"], "miss")
                self.assertEqual(self.verify(kind, "0" * 64)["status"], "miss")

    def test_repointed_revision_alias_invalidates_bell(self):
        self.exported["revisions"]["PIN"] = "c" * 40
        self.save_map()
        self.assertEqual(self.verify("bell")["status"], "miss")

    def test_public_input_tampering_invalidates_bell(self):
        self.write("scripts/public-input.py", b"changed public source\n")
        self.assertEqual(self.verify("bell")["status"], "miss")

    def test_historical_view_tampering_invalidates_bell(self):
        self.write("scripts/history/reader.py", b"changed historical reader\n")
        self.assertEqual(self.verify("bell")["status"], "miss")
        self.assertEqual(self.verify("quantum")["status"], "reused")

    def test_frozen_comparison_tampering_invalidates_quantum(self):
        self.write("evidence/science/frozen.json", b'{"value": 2}\n')
        self.assertEqual(self.verify("quantum")["status"], "miss")

    def test_duplicate_frozen_comparison_mapping_invalidates_quantum(self):
        self.exported["artifacts"].append(dict(self.exported["artifacts"][1]))
        self.save_map()
        self.assertEqual(self.verify("quantum")["status"], "miss")

    def test_makefile_guard_still_invalidates_both_scopes(self):
        self.write("Makefile", b"changed replay commands\n")
        self.assert_scopes("miss")

    def test_compatible_view_extension_is_checked_against_independent_historical_code(self):
        path = self.root / "tools/source_view.py"
        path.write_bytes(path.read_bytes() + b"\ndef unrelated_extension():\n    return 'new capability'\n")
        for kind in ("bell", "quantum"):
            with self.subTest(kind=kind):
                receipt = self.verify(kind)
                self.assertEqual(receipt["status"], "reused")
                self.assertEqual(receipt["view_engine_comparison"], "historical-source-vs-current-source")
                self.assertNotEqual(receipt["historical_source_view_sha256"], receipt["current_source_view_sha256"])
                self.assertEqual(receipt["historical_view_inputs_sha256"], receipt["current_view_inputs_sha256"])

    def test_changed_view_semantics_cannot_reinterpret_both_old_and_current_maps(self):
        path = self.root / "tools/source_view.py"
        path.write_bytes(path.read_bytes() + (
            "\n_original_module_views = module_views\n"
            "def module_views(row, inverse):\n"
            "    public, original = _original_module_views(row, inverse)\n"
            "    return public.replace(b'Nat := 1', b'Nat := 2'), original\n").encode())
        receipt = self.verify("bell")
        self.assertEqual(receipt["status"], "miss")
        self.assertNotEqual(receipt["historical_view_inputs_sha256"], receipt["current_view_inputs_sha256"])
        self.assertEqual(self.verify("quantum")["status"], "reused")

    def test_scientific_execution_script_changes_still_require_replay(self):
        self.write("tools/first_release_quantum.py", b"changed execution algorithm\n")
        self.assert_scopes("miss")


if __name__ == "__main__":
    unittest.main()
