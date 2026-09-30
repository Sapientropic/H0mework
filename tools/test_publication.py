"""Checks for receipt publication and public/exact source-view identity."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import publication as p
import source_view as s

FIXTURE_ROOT = "/".join(["", "Users", "sample", "Documents", "Homework"])


def fixture(raw: bytes) -> bytes:
    return raw.replace(b"@ROOT@", FIXTURE_ROOT.encode())


class PublicationTests(unittest.TestCase):
    def test_only_runtime_addresses_change(self):
        raw = fixture(b'{"root":"@ROOT@","command":["lean","@ROOT@/Lean/A.lean"],"source_inputs":{"@ROOT@/data/a.json":"abcd"},"value":1.2300000000000000001,"failed":true}')
        public, count = p.normalize_paths(raw)
        self.assertEqual(count, 3)
        self.assertIn(b'"value":1.2300000000000000001,"failed":true', public)
        self.assertEqual(json.loads(public)["source_inputs"], {"data/a.json": "abcd"})
        self.assertEqual(p.normalize_paths(public), (public, 0))

    def test_similar_non_machine_paths_are_preserved(self):
        raw = b'{"command":["/UsersManual/Homework/Lean/A.lean"],"root":"data/Homework"}'
        self.assertEqual(p.normalize_paths(raw), (raw, 0))

    def test_path_collision_and_non_metadata_path_fail(self):
        with self.assertRaises(p.PublicationError):
            p.normalize_paths(fixture(b'{"source_inputs":{"@ROOT@/a":"x","a":"y"}}'))
        with self.assertRaises(p.PublicationError):
            p.normalize_paths(fixture(b'{"measurement":"@ROOT@/a"}'))

    def test_payload_rejects_changed_result_even_with_new_target_digest(self):
        original = fixture(b'{"root":"@ROOT@","result":17}')
        public = p.normalize_paths(original)[0]
        row = {"source_sha256": p.sha(original), "target_sha256": p.sha(public),
               "publication": {"kind": p.KIND, "payload_sha256": p.sha(public)}}
        p.verify_artifact(public, row, original)
        tampered = public.replace(b'17', b'18')
        row["target_sha256"] = p.sha(tampered)
        with self.assertRaises(p.PublicationError):
            p.verify_artifact(tampered, row, original)

    def test_binding_updates_and_resource_digest_remain_byte_checked(self):
        receipt = fixture(b'{"root":"@ROOT@","result":17}')
        source = b'def packetSha256 := "' + p.sha(receipt).encode() + b'"\n'
        verifier = json.dumps({"root": FIXTURE_ROOT,
                               "bindings": {"replay.json": p.sha(receipt)}}).encode()
        artifacts = [
            {"source": "pkg/replay.json", "target": "evidence/replay.json",
             "source_sha256": p.sha(receipt), "target_sha256": p.sha(receipt)},
            {"source": "pkg/independent.json", "target": "evidence/independent.json",
             "source_sha256": p.sha(verifier), "target_sha256": p.sha(verifier)},
        ]
        modules = [{"path": "Lean/A.lean", "source_sha256": p.sha(source),
                    "target_sha256": p.sha(source), "resource_rewrites": [
                        {"data_sha256": p.sha(receipt), "target_artifact": "evidence/replay.json"}]}]
        outputs = {"evidence/replay.json": receipt, "evidence/independent.json": verifier,
                   "Lean/A.lean": source}
        result = p.publish_outputs(outputs, modules, artifacts, lambda row: source)
        self.assertEqual(result, {"artifacts": 2, "machine_paths": 2, "resource_modules": 1})
        self.assertEqual(json.loads(outputs["evidence/independent.json"])["bindings"]["replay.json"],
                         p.sha(outputs["evidence/replay.json"]))
        p.verify_artifact(outputs["evidence/independent.json"], artifacts[1], verifier)
        self.assertEqual(s.invert_resource_digests(outputs["Lean/A.lean"], modules[0]), source)


class SourceViewTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.original = fixture(b'{"root":"@ROOT@","result":17}')
        self.public = p.normalize_paths(self.original)[0]
        row = {"source": "source/receipt.json", "source_revision": "a" * 40,
               "source_revisions": ["a" * 40], "path": "receipt.json", "target": "receipt.json",
               "source_sha256": p.sha(self.original), "target_sha256": p.sha(self.public),
               "publication": {"kind": p.KIND, "payload_sha256": p.sha(self.public)}}
        (self.root / "receipt.json").write_bytes(self.public)
        data = {"schema": 2, "lean_directory": "Lean", "modules": [], "artifacts": [row],
                "revisions": {"T": "a" * 40}}
        self.map = self.root / "map.json"
        self.map.write_text(json.dumps(data))
        self.patches = [patch.object(s, "ROOT", self.root), patch.object(s, "EXPORT_MAP", self.map)]
        for item in self.patches:
            item.start()

    def tearDown(self):
        for item in self.patches:
            item.stop()
        self.temp.cleanup()

    def test_default_view_is_public(self):
        outputs, skipped = s.reconstruct(paths=["source/receipt.json"])
        self.assertEqual(outputs, {"source/receipt.json": self.public})
        self.assertEqual(skipped, [])
        self.assertEqual(s.verify_all()["private_originals_verified"], 0)

    def test_exact_override_needs_and_checks_original(self):
        with self.assertRaises(s.ViewError):
            s.reconstruct(paths=["source/receipt.json"], exact=True)
        archive = self.root / "originals"
        archive.mkdir()
        path = archive / p.sha(self.original)
        path.write_bytes(self.original)
        outputs, _ = s.reconstruct(paths=["source/receipt.json"], exact=True, private_originals=archive)
        self.assertEqual(outputs["source/receipt.json"], self.original)
        self.assertEqual(s.verify_all(archive)["private_originals_verified"], 1)
        path.write_bytes(b'{}')
        with self.assertRaises(s.ViewError):
            s.reconstruct(paths=["source/receipt.json"], exact=True, private_originals=archive)

    def test_receipt_prefix_does_not_hide_missing_original_or_bad_payload(self):
        clean = b'{}'
        (self.root / "clean.json").write_bytes(clean)
        data = json.loads(self.map.read_text())
        data["artifacts"].append({"source": "source/clean.json", "path": "clean.json",
            "source_revision": "a" * 40, "source_sha256": p.sha(clean),
            "target_sha256": p.sha(clean)})
        self.map.write_text(json.dumps(data))
        self.assertEqual(s.reconstruct(paths=["source/clean.json"], exact=True)[0],
                         {"source/clean.json": clean})
        with self.assertRaises(s.ViewError):
            s.reconstruct(paths=["source/clean.json"], receipt_prefixes=["receipt"], exact=True)
        (self.root / "receipt.json").write_bytes(self.public.replace(b'17', b'18'))
        with self.assertRaises(s.ViewError):
            s.reconstruct(paths=["source/clean.json"], receipt_prefixes=["receipt"])

    def test_public_module_hash_matches_public_receipt_and_exact_restores_both(self):
        original_module = (b'import Mathlib\ndef packetText := include_str "source/receipt.json"\n'
                           b'def packetSha256 := "' + p.sha(self.original).encode() + b'"\n')
        view = original_module.replace(p.sha(self.original).encode(), p.sha(self.public).encode())
        exported = view.replace(b'"source/receipt.json"', b'"receipt.json"')
        (self.root / "Consumer.lean").write_bytes(exported)
        row = {"source": "Original.Consumer", "source_path": "Lean/Original/Consumer.lean",
               "source_revision": "a" * 40, "target": "H0mework.Consumer", "path": "Consumer.lean",
               "source_sha256": p.sha(original_module), "target_sha256": p.sha(exported),
               "view_sha256": p.sha(view), "resource_rewrites": [{"source_address": "source/receipt.json",
                    "target_address": "receipt.json", "data_sha256": p.sha(self.original),
                    "target_artifact": "receipt.json"}],
               "resource_sha256_rewrites": [{"source": p.sha(self.original), "target": p.sha(self.public)}]}
        data = json.loads(self.map.read_text())
        data["modules"] = [row]
        self.map.write_text(json.dumps(data))
        paths = ["Lean/Original/Consumer.lean", "source/receipt.json"]
        public, _ = s.reconstruct(paths=paths)
        self.assertEqual(public[paths[0]], view)
        self.assertEqual(public[paths[1]], self.public)
        archive = self.root / "originals"
        archive.mkdir()
        (archive / p.sha(self.original)).write_bytes(self.original)
        exact, _ = s.reconstruct(paths=paths, exact=True, private_originals=archive)
        self.assertEqual(exact[paths[0]], original_module)
        self.assertEqual(exact[paths[1]], self.original)


if __name__ == "__main__":
    unittest.main()
