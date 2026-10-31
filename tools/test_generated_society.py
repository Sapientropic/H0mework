import copy
import gzip
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import edition_release
import generated_society as society


class SocietyContractTests(unittest.TestCase):
    def document(self, claims):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            (root / "docs").mkdir()
            (root / society.MAP).write_text(json.dumps({"schema": society.SCHEMA, "claims": claims}))
            return society.document(root)

    def claims(self):
        return [{"id": name, "paper": "generated-society", "direct_consumers": [{}]}
                for name in sorted(society.CORE_CLAIMS)]

    def test_core_contract_and_explicit_interface_override(self):
        claims = self.claims()
        self.assertEqual(len(self.document(claims)["claims"]), 11)
        interface = {"id": "G10", "paper": "generated-society", "direct_consumers": [{}], "interface_only": True}
        self.assertEqual(len(self.document([*claims, interface])["claims"]), 12)
        for change in (claims[:-1], [*claims, {**interface, "interface_only": False}],
                       [{**claims[0], "id": "G00"}, *claims[1:]],
                       [{**claims[0], "selected": False}, *claims[1:]],
                       [{**claims[0], "direct_consumers": []}, *claims[1:]]):
            with self.assertRaises(society.release.ReleaseError):
                self.document(change)

    def test_edition_registration_does_not_change_old_defaults(self):
        self.assertEqual(edition_release.EDITIONS["generated-society"], (society.MAP, society.SCHEMA))
        self.assertEqual(edition_release.EDITIONS["whole-ledger"][0], "docs/whole-ledger-map.json")
        self.assertEqual(society.release.MAP, "docs/first-release-map.json")

    def test_receipt_checks_compressed_and_payload_bytes(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            raw = b'{"status":"failed","value":1.00}\n'
            stored = gzip.compress(raw, mtime=0)
            (root / "receipt.json.gz").write_bytes(stored)
            reference = {"path": "receipt.json.gz", "sha256": society.release.sha(stored),
                         "compression": "gzip", "payload_sha256": society.release.sha(raw)}
            self.assertEqual(society.artifact(root, reference)["status"], "failed")
            for field in ("sha256", "payload_sha256"):
                with self.assertRaises(society.release.ReleaseError):
                    society.artifact(root, {**reference, field: "0" * 64})


class SocietyRecoveryTests(unittest.TestCase):
    EPOCH = "1" * 40

    def fixture(self, root):
        (root / "checks").mkdir()
        (root / "tools").mkdir()
        (root / "Lean/Public").mkdir(parents=True)
        modules = []
        for name, source, public in (
            ("Root", b"import Original.Dep\ndef result := 1\n", b"import Public.Dep\ndef result := 1\n"),
            ("Dep", b"def value := 1\n", b"def value := 1\n"),
        ):
            path = f"Lean/Public/{name}.lean"
            (root / path).write_bytes(public)
            modules.append({"path": path, "source": "Original." + name,
                            "source_path": f"Lean/Original/{name}.lean", "source_revision": self.EPOCH,
                            "source_revisions": [self.EPOCH], "source_sha256": society.release.sha(source),
                            "target": "Public." + name, "target_sha256": society.release.sha(public),
                            "variant": "fixture", "import_map": {"Public.Dep": "Original.Dep"} if name == "Root" else {}})
        raw = b'{"status":"failed","value":1.00}\n'
        (root / "receipt.json").write_bytes(raw)
        resource = {"source": "Verification/receipt.json", "path": "receipt.json",
                    "source_revision": self.EPOCH, "source_revisions": [self.EPOCH],
                    "source_sha256": society.release.sha(raw), "target_sha256": society.release.sha(raw)}
        exported = {"schema": 2, "lean_directory": "Lean", "modules": modules, "artifacts": [resource]}
        (root / society.release.EXPORT_MAP).write_text(json.dumps(exported))
        selection = {"schema": society.whole_ledger_export.SELECTION_SCHEMA,
                     "selections": [{"source_commit": self.EPOCH, "roots": ["Lean/Original/Root.lean"],
                                     "artifacts": ["Verification/receipt.json"]}]}
        (root / society.SELECTION).write_text(json.dumps(selection))
        return exported

    def test_recovery_follows_real_imports_and_preserves_original_failure(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            self.fixture(root)
            _, _, public = society.selected_views(root)
            _, _, exact = society.selected_views(root, exact=True)
            expected = {"Lean/Original/Root.lean", "Lean/Original/Dep.lean", "Verification/receipt.json"}
            self.assertEqual(set(public[self.EPOCH]["outputs"]), expected)
            self.assertEqual(exact[self.EPOCH]["outputs"]["Lean/Original/Root.lean"],
                             b"import Original.Dep\ndef result := 1\n")
            self.assertIn(b'"status":"failed"', public[self.EPOCH]["outputs"]["Verification/receipt.json"])
            self.assertEqual(society.source_view.ROOT, society.release.ROOT)

    def test_missing_dependency_or_wrong_epoch_cannot_be_recovered(self):
        for change in ("dependency", "epoch"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as name:
                root = Path(name)
                exported = self.fixture(root)
                if change == "dependency":
                    exported["modules"].pop()
                else:
                    exported["modules"][1]["source_revision"] = "2" * 40
                    exported["modules"][1]["source_revisions"] = ["2" * 40]
                (root / society.release.EXPORT_MAP).write_text(json.dumps(exported))
                with self.assertRaises(society.release.ReleaseError):
                    society.selected_views(root)

    def test_changed_public_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            self.fixture(root)
            (root / "Lean/Public/Dep.lean").write_text("axiom value : Nat\n")
            with self.assertRaises(society.source_view.ViewError):
                society.selected_views(root)


class SocietyCoverageTests(unittest.TestCase):
    def fixture(self):
        entry = {"source_commit": "1" * 40, "public": {}, "verification": {"proof_package": "p"}}
        data = {"claims": [{"id": "G1", "paper": "generated-society", "producers": [entry],
                            "direct_consumers": [copy.deepcopy(entry)]}],
                "proof_packages": [{"id": "p", "paper": "generated-society", "source_commit": "1" * 40,
                                    "lean_target": "Public.Root"}]}
        return data

    def test_package_coverage_includes_direct_consumers_and_exact_package(self):
        data = self.fixture()
        expected_scope = {"files": {}, "digest": "scope", "modules": 2}
        with patch.object(society.release, "package_inputs", return_value=expected_scope):
            scopes, _ = society.package_scopes(data, {}, Path("."))
            self.assertEqual(scopes["p"], expected_scope)
            data["claims"][0]["direct_consumers"][0]["source_commit"] = "2" * 40
            with self.assertRaises(society.release.ReleaseError):
                society.package_scopes(data, {}, Path("."))
            data = self.fixture()
            data["claims"][0]["direct_consumers"][0]["verification"]["proof_package"] = "other"
            with self.assertRaises(society.release.ReleaseError):
                society.package_scopes(data, {}, Path("."))

    def test_types_uses_society_map_and_restores_existing_runner(self):
        previous = society.whole_ledger.MAP, society.whole_ledger.SCHEMA
        def inspect(output, ids):
            self.assertEqual((society.whole_ledger.MAP, society.whole_ledger.SCHEMA), (society.MAP, society.SCHEMA))
            return {"status": "passed"}
        with patch.object(society.whole_ledger, "types", side_effect=inspect):
            self.assertEqual(society.types(".local/test", ["p"])["status"], "passed")
        self.assertEqual((society.whole_ledger.MAP, society.whole_ledger.SCHEMA), previous)


class SocietyReadinessTests(unittest.TestCase):
    def fixture(self, root):
        (root / "Lean").mkdir()
        for path in ("Lean/lakefile.toml", "Lean/lean-toolchain", "Lean/lake-manifest.json"):
            (root / path).write_text(path + "\n")
        entry = {"public": {"module": "Public.Root"}, "declarations": [{"qualified_name": "Root.result"}]}
        package = {"id": "p", "source_commit": "1" * 40, "lean_target": "Public.Root"}
        entries = {"p": [({"id": "G1"}, "producers", 0, entry)]}
        _, expected = society.release.audit_source(package, entries["p"])
        configured = {"package_moreLeanArgs": ["--trust=0"], "package_weakLeanArgs": []}
        identity = {"package_inputs": {"p": "current"}, "sha256": {
            key: society.release.sha((root / path).read_bytes())
            for key, path in (("lakefile", "Lean/lakefile.toml"), ("toolchain", "Lean/lean-toolchain"),
                              ("manifest", "Lean/lake-manifest.json"))}}
        receipts = {kind: {"ok": True, "inputs_unchanged": True, "input_identity": identity,
                           "input_identity_after": identity, "settings": configured}
                    for kind in ("build", "trust")}
        receipts["build"]["results"] = [{"exit_code": 0}]
        receipts["trust"].update(preflight={"exit_code": 0}, results=[{
            "package": "p", "exit_code": 0, "status": "passed", "audit_scope": expected,
            "audit": {"token": expected["token"], "roots": 1, "constants": 3,
                      "full_metadata": True, "unsafe": 0, "partial": 0,
                      "axioms": ["propext", "Classical.choice", "Quot.sound"]}}])
        receipts["types"] = {"declarations": [{"unsafe": False, "partial": False, "axioms": ["propext"]}]}
        package["accepted_source_scope_sha256"] = "current"
        data = {"proof_packages": [package], "acceptance": {"status": "passed",
                **{key: {"path": key} for key in ("build", "trust")},
                "declaration_types": {"path": "types"}}}
        return data, {"p": {"digest": "current", "modules": 2}}, entries, configured, receipts

    def run_ready(self, root, fixture):
        data, scopes, entries, configured, receipts = fixture
        with patch.object(society, "artifact", side_effect=lambda _, ref: receipts[ref["path"]]), \
                patch.object(society.release, "settings", return_value=configured), \
                patch.object(society.whole_ledger, "verify_recorded_types", return_value=1):
            return society.recorded_acceptance(data, scopes, entries, root)

    def test_exact_current_receipts_pass_and_nonstandard_audit_fails(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            fixture = self.fixture(root)
            self.assertEqual(self.run_ready(root, fixture), 1)
            audit = fixture[-1]["trust"]["results"][0]["audit"]
            for change in ({"full_metadata": False}, {"unsafe": 1}, {"partial": 1}, {"axioms": ["sorryAx"]}):
                changed = copy.deepcopy(fixture)
                changed[-1]["trust"]["results"][0]["audit"] = {**audit, **change}
                with self.assertRaises(society.release.ReleaseError):
                    self.run_ready(root, changed)

    def test_missing_package_or_stale_scope_cannot_reuse_historical_green(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            fixture = self.fixture(root)
            for kind in ("missing", "stale", "types"):
                changed = copy.deepcopy(fixture)
                if kind == "missing":
                    changed[-1]["trust"]["results"] = []
                elif kind == "stale":
                    changed[-1]["build"]["input_identity"]["package_inputs"]["p"] = "historical"
                else:
                    changed[-1]["types"]["declarations"][0]["unsafe"] = True
                with self.assertRaises(society.release.ReleaseError):
                    self.run_ready(root, changed)


if __name__ == "__main__":
    unittest.main()
