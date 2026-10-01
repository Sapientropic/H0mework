from pathlib import Path
import io
import json
import os
import shutil
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from ci_plan import build_part, changed_paths, closure, completed_setup_files, imports, make_plan, pack, requires_lean, unpack


class PlanTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.sources = {
            "H0mework": "import H0mework.Papers.Demo\n",
            "H0mework.Foundation.Shared": "def shared := 1\n",
            "H0mework.Physics.Independent": "import H0mework.Foundation.Shared\n",
            "H0mework.Arithmetic.Independent": "import H0mework.Foundation.Shared\n",
            "H0mework.Chemistry.SourceParsing": "import H0mework.Foundation.Shared\n",
            "H0mework.Chemistry.LAlanineBandCall001.Check": "import H0mework.Chemistry.SourceParsing\n",
            "H0mework.Chemistry.LAlanineBandCall002.Check": "import H0mework.Chemistry.SourceParsing\n",
            "H0mework.Papers.Demo": "import H0mework.Physics.Independent\nimport H0mework.Chemistry.LAlanineBandCall001.Check\n",
            "H0mework.Versions.Y.Broken": "this historical source fails\n",
        }
        for name, source in self.sources.items():
            self.write_module(name, source)
        (self.root / "Lean/lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")
        (self.root / "Lean/lake-manifest.json").write_text('{"packages": []}\n')
        (self.root / "evidence").mkdir()
        (self.root / "evidence/source.json").write_text('{"result": 1}\n')
        self.write_config()

    def write_module(self, name, text):
        path = self.root / "Lean" / (name.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def write_config(self):
        ordinary = [n for n in self.sources if n not in {"H0mework.Chemistry.SourceParsing", "H0mework.Versions.Y.Broken"}]
        (self.root / "Lean/lakefile.toml").write_text(
            'name = "H0mework"\ndefaultTargets = ["H0mework", "ResourceConsumers"]\n'
            'moreLeanArgs = ["--trust=0"]\n'
            '[[lean_lib]]\nname = "H0mework"\n'
            f'globs = {json.dumps(ordinary)}\nmoreLeanArgs = ["-DwarningAsError=true"]\n'
            '[[lean_lib]]\nname = "ResourceConsumers"\nroots = []\n'
            'globs = ["H0mework.Chemistry.SourceParsing"]\nneeds = ["ResourceInput"]\n'
            '[[lean_lib]]\nname = "Pinned"\nroots = []\n'
            'globs = ["H0mework.Versions.Y.Broken"]\n'
            '[[input_file]]\nname = "ResourceInput"\npath = "../evidence/source.json"\ntext = false\n'
        )

    def test_default_coverage_and_cross_part_dependencies(self):
        parts = make_plan(self.root)["parts"]
        all_modules = [n for p in parts.values() for n in p["modules"]]
        self.assertEqual(len(all_modules), len(set(all_modules)))
        self.assertEqual(set(all_modules), set(self.sources) - {"H0mework.Versions.Y.Broken"})
        dependencies = {n: [d for d in imports(self.sources[n]) if d in all_modules] for n in all_modules}
        for part in parts.values():
            roots = [n.removeprefix("+") for n in part["targets"]]
            self.assertTrue(set(part["modules"]) <= closure(roots, dependencies))
        self.assertIn("H0mework.Foundation.Shared", parts["base"]["modules"])
        self.assertIn("H0mework.Chemistry.SourceParsing", parts["base"]["modules"])
        self.assertIn("H0mework.Chemistry.LAlanineBandCall001.Check", parts["chemistry-1"]["modules"])

    def test_new_paper_does_not_invalidate_existing_parts(self):
        before = make_plan(self.root)
        name = "H0mework.Papers.NewPaper"
        self.sources[name] = "import H0mework.Physics.Independent\n"
        self.write_module(name, self.sources[name])
        self.write_module("H0mework", self.sources["H0mework"] + f"import {name}\n")
        self.write_config()
        after = make_plan(self.root)
        for part in before["parts"]:
            if part != "integration":
                self.assertEqual(before["parts"][part]["fingerprint"], after["parts"][part]["fingerprint"], part)
        self.assertNotEqual(before["parts"]["integration"]["fingerprint"], after["parts"]["integration"]["fingerprint"])

    def test_resource_change_invalidates_consumers_but_not_independent_physics(self):
        before = make_plan(self.root)
        (self.root / "evidence/source.json").write_text('{"result": 2}\n')
        after = make_plan(self.root)
        for part in ["base", "chemistry-1", "chemistry-2", "integration"]:
            self.assertNotEqual(before["parts"][part]["fingerprint"], after["parts"][part]["fingerprint"], part)
        self.assertEqual(before["parts"]["physics"]["fingerprint"], after["parts"]["physics"]["fingerprint"])

    def test_real_import_header_ignores_comments_and_body_strings(self):
        source = '/- import H0mework.Wrong /- nested -/ -/\nmodule\npublic import H0mework.Foundation.Shared -- note\n'
        source += 'def example := "a /- quoted delimiter"\nimport H0mework.Wrong\n'
        self.assertEqual(imports(source), ["H0mework.Foundation.Shared"])

    def test_default_cannot_import_pinned_failure(self):
        self.write_module("H0mework", "import H0mework.Versions.Y.Broken\n")
        with self.assertRaisesRegex(ValueError, "non-default"):
            make_plan(self.root)

    def test_trigger_positive_override_and_near_miss(self):
        self.assertTrue(requires_lean(["Lean/H0mework/Papers/New.lean"]))
        self.assertTrue(requires_lean(None))
        self.assertFalse(requires_lean(["README.md", "docs/assets/banner.svg"]))
        self.assertFalse(requires_lean(["docs/source/physics/criterion.md"]))
        self.assertTrue(requires_lean(["evidence/physics/receipt.json"]))

    def test_force_push_without_previous_head_keeps_full_verification(self):
        with patch("ci_plan.subprocess.check_output", side_effect=subprocess.CalledProcessError(128, ["git", "diff"])):
            paths = changed_paths(self.root, "push", {"before": "a" * 40, "after": "b" * 40})
        self.assertIsNone(paths)
        self.assertTrue(requires_lean(paths))

    @unittest.skipUnless(shutil.which("lake") and shutil.which("zstd"), "Lean and zstd are required")
    def test_checked_artifacts_work_in_a_separate_checkout_and_missing_outputs_fail(self):
        updated = subprocess.run(["lake", "update"], cwd=self.root / "Lean", capture_output=True, text=True)
        self.assertEqual(updated.returncode, 0, updated.stdout + updated.stderr)
        plan = make_plan(self.root)
        ordered = ["base", *sorted(n for n in plan["parts"] if n not in {"base", "integration"}), "integration"]
        second = self.root / "second-checkout"
        shutil.copytree(self.root / "Lean", second / "Lean", ignore=shutil.ignore_patterns(".lake"))
        shutil.copytree(self.root / "evidence", second / "evidence")
        for name in ordered:
            part = plan["parts"][name]
            self.assertEqual(build_part(self.root, part), 0, name)
            archive = self.root / (name + ".tar.zst")
            pack(self.root, part["modules"], archive)
            unpack(second, archive)
        check = subprocess.run(["lake", "--no-build", "build"], cwd=second / "Lean", capture_output=True, text=True)
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
        packet = second / "evidence/source.json"
        original = packet.read_bytes()
        packet.write_text('{"result": 2}\n')
        check = subprocess.run(["lake", "--no-build", "build"], cwd=second / "Lean", capture_output=True, text=True)
        self.assertEqual(check.returncode, 3, check.stdout + check.stderr)
        packet.write_bytes(original)
        (second / "Lean/.lake/build/lib/lean/H0mework/Physics/Independent.olean").unlink()
        check = subprocess.run(["lake", "--no-build", "build"], cwd=second / "Lean", capture_output=True, text=True)
        self.assertEqual(check.returncode, 3, check.stdout + check.stderr)


@unittest.skipUnless(shutil.which("zstd"), "zstd is needed for artifact transport")
class ArtifactTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.build = self.root / "Lean/.lake/build"

    def file(self, relative, data=b"checked module"):
        path = self.build / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return path

    def test_round_trip_keeps_owned_artifacts_and_excludes_setup_and_other_parts(self):
        self.file("lib/lean/H0mework/Example.olean")
        self.file("lib/lean/H0mework/Example.trace")
        self.file("ir/H0mework/Example.c")
        self.file("ir/H0mework/Example.setup.json", b"temporary absolute paths")
        self.file("lib/lean/H0mework/Other.olean")
        archive = self.root / "part.tar.zst"
        pack(self.root, ["H0mework.Example"], archive)
        destination = self.root / "destination"
        unpack(destination, archive)
        restored = destination / "Lean/.lake/build"
        self.assertEqual((restored / "lib/lean/H0mework/Example.olean").read_bytes(), b"checked module")
        self.assertFalse((restored / "ir/H0mework/Example.setup.json").exists())
        self.assertFalse((restored / "lib/lean/H0mework/Other.olean").exists())

    def test_archive_traversal_is_rejected(self):
        raw = io.BytesIO()
        with tarfile.open(fileobj=raw, mode="w") as tar:
            entry = tarfile.TarInfo("../../escape")
            entry.size = 3
            tar.addfile(entry, io.BytesIO(b"bad"))
        archive = self.root / "unsafe.tar.zst"
        archive.write_bytes(subprocess.check_output(["zstd", "-q", "-c"], input=raw.getvalue()))
        with self.assertRaisesRegex(ValueError, "Invalid artifact"):
            unpack(self.root, archive)
        self.assertFalse((self.root / "escape").exists())

    def test_janitor_waits_for_compilation_trace(self):
        setup = self.file("ir/H0mework/Example.setup.json")
        trace = self.file("lib/lean/H0mework/Example.trace")
        os.utime(trace, ns=(10, 10))
        os.utime(setup, ns=(20, 20))
        self.assertEqual(completed_setup_files(self.build), 0)
        self.assertTrue(setup.exists())
        os.utime(trace, ns=(30, 30))
        self.assertEqual(completed_setup_files(self.build), 1)
        self.assertFalse(setup.exists())


if __name__ == "__main__":
    unittest.main()
