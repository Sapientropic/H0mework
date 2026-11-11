import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import first_release as release


class BuildConfigurationCompatibilityTests(unittest.TestCase):
    def fixture(self, root, *, promote_dependency=False):
        for path in ("Lean/Public", "checks", "evidence", "tools"):
            (root / path).mkdir(parents=True)
        before = '''name = "Fixture"
defaultTargets = ["Existing"]
moreLeanArgs = ["--trust=0"]
weakLeanArgs = ["-DmaxHeartbeats=2000000"]
[[lean_lib]]
name = "Existing"
globs = ["Public.*"]
moreLeanArgs = ["-DwarningAsError=true"]
weakLeanArgs = ["-DmaxRecDepth=1000"]
roots = []
needs = ["Input"]
[[input_file]]
name = "Input"
path = "../evidence/input.json"
text = false
'''
        if promote_dependency:
            before = before.replace('globs = ["Public.*"]', 'globs = ["Public.Root"]')
            before += '''[[lean_lib]]
name = "Optional"
globs = ["Public.Dep", "Public.Other"]
moreLeanArgs = ["-DwarningAsError=true"]
roots = []
needs = ["Input"]
'''
        after = before.replace('defaultTargets = ["Existing"]', 'defaultTargets = ["Existing", "Added"]')
        after = after.replace('globs = ["Public.*"]', 'globs = ["Public.*", "Extension.New"]')
        after += '''[[lean_lib]]
name = "Added"
globs = ["Added.*"]
moreLeanArgs = ["-DwarningAsError=true"]
'''
        if promote_dependency:
            after = after.replace('globs = ["Public.Dep", "Public.Other"]', 'globs = ["Public.Other"]')
            after = after.replace('globs = ["Added.*"]', 'globs = ["Added.*", "Public.Dep"]')
            after += 'roots = []\nneeds = ["Input"]\n'
        (root / "Lean/lakefile.toml").write_text(after)
        (root / "evidence/lakefile-before.toml").write_text(before)
        resource = b'{"value":1.00}\n'
        (root / "evidence/input.json").write_bytes(resource)
        subprocess.run(["git", "init", "--quiet", str(root)], check=True, capture_output=True)
        (root / "Lean/lakefile.toml").write_text(before)
        subprocess.run(["git", "-C", str(root), "add", "Lean/lakefile.toml", "evidence/input.json"],
                       check=True, capture_output=True)
        subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                        "commit", "--quiet", "-m", "fixed original build inputs"], check=True, capture_output=True)
        commit = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"]).decode().strip()
        (root / "Lean/lakefile.toml").write_text(after)
        digest = release.sha(before.encode())
        compatibility = {"schema": "h0mework/build-configuration-compatibility@1", "baselines": [{
            "source_commit": commit, "source_path": "Lean/lakefile.toml", "accepted_lakefile_sha256": digest,
            "snapshot": {"path": "evidence/lakefile-before.toml", "sha256": digest},
            "resources": {"Input": {"path": "evidence/input.json", "sha256": release.sha(resource)}}}]}
        (root / release.BUILD_COMPATIBILITY).write_text(json.dumps(compatibility))
        modules = []
        for name, source in (("Public.Root", "import Public.Dep\ndef result := 1\n"),
                             ("Public.Dep", "def input := 1\n")):
            path = release.module_path(name)
            (root / path).write_text(source)
            modules.append({"target": name, "path": path, "target_sha256": release.sha(source.encode())})
        exported = {"modules": modules, "artifacts": []}
        (root / release.EXPORT_MAP).write_text(json.dumps(exported))
        package = {"id": "existing", "paper": "paper", "source_commit": "1" * 40, "lean_target": "Public.Root"}
        proof = {"source_commit": "1" * 40, "public": {"module": "Public.Root"}}
        data = {"proof_packages": [package], "claims": [{"id": "old", "paper": "paper", "producers": [proof]}]}
        scope = release.package_inputs(root, exported, package, release.package_entries(data["claims"], package))
        return digest, data, {"existing": {"source_scope_sha256": scope["digest"], "modules": scope["modules"]}}

    def verify(self, root, inputs):
        digest, data, scopes = inputs
        return release.verify_build_configuration(root, digest, data=data, scopes=scopes)

    def test_append_only_new_library_glob_and_default_target_preserve_signed_scope(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            result = self.verify(root, self.fixture(root))
            self.assertEqual(result["mode"], "append-only-equivalent")
            self.assertEqual((result["modules"], result["resources"]), (2, 1))

    def test_exact_configuration_keeps_original_path_without_compatibility_file(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            inputs = self.fixture(root)
            (root / "Lean/lakefile.toml").write_bytes((root / "evidence/lakefile-before.toml").read_bytes())
            (root / release.BUILD_COMPATIBILITY).unlink()
            self.assertEqual(self.verify(root, inputs)["mode"], "exact")

    def test_nondefault_dependency_can_enter_ci_with_the_same_options_and_resources(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            inputs = self.fixture(root, promote_dependency=True)
            result = self.verify(root, inputs)
            self.assertEqual(result["mode"], "nondefault-promotion-equivalent")
            self.assertEqual((result["modules"], result["resources"]), (2, 1))

            path = root / "Lean/lakefile.toml"
            config = path.read_text()
            before, added = config.split('name = "Added"', 1)
            for source, replacement in [
                ('needs = ["Input"]', 'needs = []'),
                ('"-DwarningAsError=true"', '"-DwarningAsError=false"'),
                ('"Public.Dep"', '"Public.+"'),
            ]:
                with self.subTest(replacement=replacement):
                    path.write_text(before + 'name = "Added"' + added.replace(source, replacement))
                    with self.assertRaises(release.ReleaseError):
                        self.verify(root, inputs)

    def test_changed_options_owners_needs_or_dependency_configuration_are_rejected(self):
        changes = {
            "old-owner": ('name = "Existing"', 'name = "Replacement"'),
            "ambiguous-owner": ('globs = ["Added.*"]', 'globs = ["Added.*", "Public.Dep"]'),
            "strong-options": ('"--trust=0"', '"--trust=1"'),
            "package-weak-options": ('"-DmaxHeartbeats=2000000"', '"-DmaxHeartbeats=3000000"'),
            "library-weak-options": ('"-DmaxRecDepth=1000"', '"-DmaxRecDepth=2000"'),
            "needs": ('needs = ["Input"]', 'needs = []'),
            "resource-definition": ('text = false', 'text = true'),
            "old-glob-removal": ('globs = ["Public.*", "Extension.New"]', 'globs = ["Public.Root"]'),
        }
        for change, (before, after) in changes.items():
            with self.subTest(change=change), tempfile.TemporaryDirectory() as name:
                root = Path(name)
                inputs = self.fixture(root)
                path = root / "Lean/lakefile.toml"
                path.write_text(path.read_text().replace(before, after))
                with self.assertRaises(release.ReleaseError):
                    self.verify(root, inputs)

    def test_changed_resource_bytes_and_unbound_snapshot_are_rejected(self):
        for change in ("resource", "snapshot", "accepted-digest", "resource-binding"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as name:
                root = Path(name)
                inputs = self.fixture(root)
                if change == "resource":
                    (root / "evidence/input.json").write_text('{"value":2.00}\n')
                elif change == "snapshot":
                    (root / "evidence/lakefile-before.toml").write_text('name = "Forged"\n')
                else:
                    path = root / release.BUILD_COMPATIBILITY
                    compatibility = json.loads(path.read_text())
                    baseline = compatibility["baselines"][0]
                    if change == "accepted-digest":
                        baseline["accepted_lakefile_sha256"] = "0" * 64
                    else:
                        baseline["resources"].clear()
                    path.write_text(json.dumps(compatibility))
                with self.assertRaises(release.ReleaseError):
                    self.verify(root, inputs)

    def test_scope_is_recomputed_instead_of_accepting_a_similar_old_package(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            inputs = self.fixture(root)
            changed = copy.deepcopy(inputs)
            changed[2]["existing"]["source_scope_sha256"] = "changed"
            with self.assertRaises(release.ReleaseError):
                self.verify(root, changed)
            changed = copy.deepcopy(inputs)
            changed[2]["existing-extra"] = changed[2].pop("existing")
            with self.assertRaises(release.ReleaseError):
                self.verify(root, changed)

    def test_resource_and_explicit_table_cannot_be_changed_together(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            inputs = self.fixture(root)
            raw = b'{"value":2.00}\n'
            (root / "evidence/input.json").write_bytes(raw)
            path = root / release.BUILD_COMPATIBILITY
            compatibility = json.loads(path.read_text())
            compatibility["baselines"][0]["resources"]["Input"]["sha256"] = release.sha(raw)
            path.write_text(json.dumps(compatibility))
            with self.assertRaisesRegex(release.ReleaseError, "fixed Git preservation baseline"):
                self.verify(root, inputs)

    def test_missing_baseline_has_an_explicit_restore_command_and_no_fallback(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            inputs = self.fixture(root)
            path = root / release.BUILD_COMPATIBILITY
            compatibility = json.loads(path.read_text())
            compatibility["baselines"][0]["source_commit"] = "0" * 40
            path.write_text(json.dumps(compatibility))
            with self.assertRaisesRegex(release.ReleaseError, "git fetch --no-tags origin " + "0" * 40):
                self.verify(root, inputs)


if __name__ == "__main__":
    unittest.main()
