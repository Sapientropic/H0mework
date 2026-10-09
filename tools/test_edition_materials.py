import gzip
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import edition_materials as materials
import first_release as release
import source_view


class EditionMaterialsTests(unittest.TestCase):
    def bundle(self, root, raw, codec="gzip"):
        packed = gzip.compress(raw, mtime=0) if codec == "gzip" else raw
        path = "evidence/frozen.gz" if codec == "gzip" else "evidence/frozen.json"
        file = root / path
        file.parent.mkdir(parents=True)
        file.write_bytes(packed)
        digest = hashlib.sha256(packed).hexdigest()
        artifacts = {path: {"path": path, "source_sha256": digest, "target_sha256": digest}}
        return {"artifact": path, "destination": "ComputeNode/state/original.json", "codec": codec,
                "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}, artifacts

    def test_gzip_restores_exact_scientific_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "view"
            output.mkdir()
            raw = b'{"value":1.0000000000000001,"counterexample":false}\n'
            bundle, artifacts = self.bundle(root, raw)
            with patch.object(source_view, "ROOT", root):
                receipt = materials.restore_bundle(root, output, bundle, artifacts)
            self.assertEqual((output / bundle["destination"]).read_bytes(), raw)
            self.assertEqual(receipt["sha256"], hashlib.sha256(raw).hexdigest())

    def test_explicit_copy_preserves_an_original_gzip_stream(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "view"
            output.mkdir()
            raw = gzip.compress(b"original stream\n", mtime=13)
            bundle, artifacts = self.bundle(root, raw, "copy")
            with patch.object(source_view, "ROOT", root):
                materials.restore_bundle(root, output, bundle, artifacts)
            self.assertEqual((output / bundle["destination"]).read_bytes(), raw)

    def test_a_rehashed_archive_with_the_wrong_raw_identity_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "view"
            output.mkdir()
            bundle, artifacts = self.bundle(root, b"wrong scientific payload")
            bundle["sha256"] = hashlib.sha256(b"original scientific payload").hexdigest()
            with patch.object(source_view, "ROOT", root), self.assertRaises(release.ReleaseError):
                materials.restore_bundle(root, output, bundle, artifacts)
            self.assertFalse((output / bundle["destination"]).exists())
            self.assertFalse(list(output.rglob("*.partial")))

    def test_size_limit_and_path_escape_are_rejected(self):
        for change in ({"bytes": 1}, {"destination": "../outside.json"}):
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                output = root / "view"
                output.mkdir()
                bundle, artifacts = self.bundle(root, b"longer than one byte")
                bundle.update(change)
                with patch.object(source_view, "ROOT", root), self.assertRaises(release.ReleaseError):
                    materials.restore_bundle(root, output, bundle, artifacts)
                self.assertFalse((root / "outside.json").exists())

    def test_an_existing_view_input_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "view"
            output.mkdir()
            bundle, artifacts = self.bundle(root, b"replacement")
            target = output / bundle["destination"]
            target.parent.mkdir(parents=True)
            target.write_bytes(b"existing input")
            with patch.object(source_view, "ROOT", root), self.assertRaises(release.ReleaseError):
                materials.restore_bundle(root, output, bundle, artifacts)
            self.assertEqual(target.read_bytes(), b"existing input")


if __name__ == "__main__":
    unittest.main()
