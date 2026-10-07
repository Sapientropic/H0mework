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
                "map_sha256": cache.sha(cache.ROOT / "tools/export-map.json"),
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


if __name__ == "__main__":
    unittest.main()
