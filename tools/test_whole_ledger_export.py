"""Focused checks for fixed-epoch intake, immutable reuse and exact resource views."""
from __future__ import annotations

import json
import gzip
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import source_view as sv
import whole_ledger_export as w


class ExportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.directory = Path(self.temp.name)
        self.source = self.directory / "source"
        self.public = self.directory / "public"
        self.source.mkdir()
        self.public.mkdir()
        self.init_git(self.source)
        self.init_git(self.public)
        self.export = {"schema": 2, "source_repository": "https://example.org/Homework.git",
                       "lean_directory": "Lean", "modules": [], "artifacts": []}
        self.write_map()

    def tearDown(self):
        self.temp.cleanup()

    def init_git(self, root):
        self.git(root, "init", "-q")
        self.git(root, "config", "user.email", "fixture@example.org")
        self.git(root, "config", "user.name", "Fixture")

    def git(self, root, *args):
        return subprocess.check_output(["git", "-C", str(root), *args], stderr=subprocess.DEVNULL).decode().strip()

    def write(self, root, path, raw):
        destination = root / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(raw)

    def commit(self, root):
        self.git(root, "add", ".")
        self.git(root, "commit", "-qm", "Fixture")
        return self.git(root, "rev-parse", "HEAD")

    def write_map(self):
        self.write(self.public, "tools/export-map.json", json.dumps(self.export).encode())

    def selection(self, selections):
        path = self.directory / "selection.json"
        path.write_text(json.dumps({"schema": w.SELECTION_SCHEMA, "selections": selections}))
        return path

    def run_stage(self, selections, providers=(), name="stage"):
        return w.stage(self.public, self.source, self.selection(selections), self.directory / name, providers)

    def existing(self, path, raw, revision, target="H0mework.A", imports=None, origin=None):
        encoded = sv.transform(raw.decode(), sv.import_tokens(raw.decode()), imports or {})
        public_path = "Lean/" + target.replace(".", "/") + ".lean"
        row = {"source": w.original_module(path), "source_path": path, "source_revision": revision,
               "source_revisions": [revision], "source_sha256": w.sha(raw), "path": public_path,
               "target": target, "target_sha256": w.sha(encoded), "variant": "base",
               "import_map": {owner: name for name, owner in (imports or {}).items()}}
        if origin:
            row["source_origin"] = origin
        self.write(self.public, public_path, encoded)
        self.export["modules"].append(row)
        self.write_map()
        return row

    def test_complete_import_resource_closure_and_exact_inverse(self):
        receipt = json.dumps({"root": "/Users/fixture/Homework", "result": 17, "status": "certified"}).encode()
        source = (b'import A\nimport Mathlib\ndef packet := include_str "../Verification/receipt.json"\n'
                  b'def digest := "' + w.sha(receipt).encode() + b'"\n'
                  b'def owner := Name.num `_private.A 0\n')
        self.write(self.source, "Lean/A.lean", b'import Mathlib\ndef sourceValue := 7\n')
        self.write(self.source, "Lean/Root.lean", source)
        self.write(self.source, "Verification/receipt.json", receipt)
        revision = self.commit(self.source)
        plan = self.run_stage([{"source_commit": revision, "roots": ["Lean/Root.lean"]}])
        self.assertEqual(plan["summary"]["source_closure"], 2)
        self.assertEqual(plan["summary"]["exact_inverse_passed"], 2)
        artifact = plan["artifacts"][0]
        original_artifact = (self.directory / "stage/raw" / artifact["source_sha256"]).read_bytes()
        self.assertEqual(original_artifact, receipt)
        public_receipt = (self.directory / "stage/stage" / artifact["path"]).read_bytes()
        self.assertEqual(json.loads(public_receipt), {"root": ".", "result": 17, "status": "certified"})
        row = next(row for row in plan["additions"] if row["source_path"] == "Lean/Root.lean")
        with patch.object(sv, "ROOT", self.directory / "stage/stage"):
            view, exact = sv.module_views(row, {})
        self.assertEqual(exact, source)
        self.assertIn(artifact["target_sha256"].encode(), view)
        self.assertEqual(row["private_name_rewrites"][0]["source_name"], "_private.A")
        self.assertEqual(self.export["modules"], [])

    def test_unchanged_body_with_changed_dependency_gets_distinct_owner(self):
        self.write(self.source, "Lean/A.lean", b'import Mathlib\ndef a := 1\n')
        self.write(self.source, "Lean/Root.lean", b'import A\ndef root := a\n')
        first = self.commit(self.source)
        self.write(self.source, "Lean/A.lean", b'import Mathlib\ndef a := 2\n')
        second = self.commit(self.source)
        plan = self.run_stage([{"source_commit": ref, "roots": ["Lean/Root.lean"]} for ref in (first, second)])
        first_root = plan["sources"][w.source_key(first, "Lean/Root.lean")]
        second_root = plan["sources"][w.source_key(second, "Lean/Root.lean")]
        self.assertEqual(first_root["source_sha256"], second_root["source_sha256"])
        self.assertNotEqual(first_root["target"], second_root["target"])
        self.assertEqual(len(plan["additions"]), 4)

    def test_suggestion_index_postlude_survives_a_new_dependency_owner(self):
        first_dependency = b'import Mathlib\ndef a := 1\n'
        root = b'import A\nnamespace Demo\ntheorem root : True := True.intro\nend Demo\n'
        self.write(self.source, 'Lean/A.lean', first_dependency)
        self.write(self.source, 'Lean/Root.lean', root)
        first = self.commit(self.source)
        self.existing('Lean/A.lean', first_dependency, first)
        row = self.existing('Lean/Root.lean', root, first, target='H0mework.Root', imports={'A': 'H0mework.A'})
        public = sv.suggestion_index_postlude((self.public / row['path']).read_text(), ['Demo']).encode()
        row.update(suggestion_name_exclusions=['Demo'], target_sha256=w.sha(public),
                   view_sha256=w.sha(sv.suggestion_index_postlude(root.decode(), ['Demo']).encode()))
        self.write(self.public, row['path'], public)
        self.write_map()
        self.write(self.source, 'Lean/A.lean', b'import Mathlib\ndef a := 2\n')
        second = self.commit(self.source)
        plan = self.run_stage([{'source_commit': second, 'roots': ['Lean/Root.lean']}])
        new = next(item for item in plan['additions'] if item['source_path'] == 'Lean/Root.lean')
        self.assertEqual(new['suggestion_name_exclusions'], ['Demo'])
        with patch.object(sv, 'ROOT', self.directory / 'stage/stage'):
            view, exact = sv.module_views(new, {})
        self.assertEqual(exact, root)
        self.assertIn(b'nameDenyListExt.addEntry env "Demo"', view)

    def test_existing_full_public_owner_is_reused_and_epoch_registered(self):
        raw = b'import Mathlib\ntheorem intact : True := True.intro\n'
        self.write(self.source, "Lean/A.lean", raw)
        first = self.commit(self.source)
        owner = self.existing("Lean/A.lean", raw, first)
        self.write(self.source, "unrelated.txt", b'Later fixed epoch\n')
        second = self.commit(self.source)
        before = (self.public / owner["path"]).read_bytes()
        plan = self.run_stage([{"source_commit": second, "roots": ["Lean/A.lean"]}])
        self.assertEqual(plan["additions"], [])
        self.assertEqual(plan["assignments"][w.source_key(second, "Lean/A.lean")], owner["target"])
        self.assertEqual(plan["source_revision_updates"], [{"target": owner["target"], "source_revisions": sorted([first, second])}])
        self.assertEqual((self.public / owner["path"]).read_bytes(), before)

    def test_same_recursive_layout_across_epochs_compiles_once(self):
        self.write(self.source, "Lean/A.lean", b'import Mathlib\ndef a := 1\n')
        first = self.commit(self.source)
        self.write(self.source, "unrelated.txt", b'Later fixed epoch\n')
        second = self.commit(self.source)
        plan = self.run_stage([{"source_commit": ref, "roots": ["Lean/A.lean"]} for ref in (first, second)])
        self.assertEqual(len(plan["additions"]), 1)
        self.assertEqual(plan["additions"][0]["source_revisions"], sorted([first, second]))

    def test_tampered_public_bytes_cannot_be_reused(self):
        raw = b'import Mathlib\ndef a := 1\n'
        self.write(self.source, "Lean/A.lean", raw)
        revision = self.commit(self.source)
        owner = self.existing("Lean/A.lean", raw, revision)
        self.write(self.public, owner["path"], raw.replace(b'1', b'2'))
        with self.assertRaisesRegex(sv.ViewError, "recorded digest"):
            self.run_stage([{"source_commit": revision, "roots": ["Lean/A.lean"]}])

    def test_working_tree_never_fills_a_missing_fixed_source(self):
        self.write(self.source, "Lean/A.lean", b'import Mathlib\ndef a := 1\n')
        revision = self.commit(self.source)
        self.write(self.source, "Lean/Missing.lean", b'import Mathlib\ndef a := 2\n')
        with self.assertRaisesRegex(w.ExportError, "Missing fixed Git source.*Lean/Missing.lean"):
            self.run_stage([{"source_commit": revision, "roots": ["Lean/Missing.lean"]}])

    def test_comment_and_string_lookalikes_are_not_dependencies(self):
        raw = (b'import Mathlib\n/- import Fake\ndef text := include_str "missing.json" -/\n'
               b'-- code.startsWith "_private.Fake."\n'
               b'def quoted := "import Fake; include_str \\\"missing.json\\\""\n')
        self.write(self.source, "Lean/A.lean", raw)
        revision = self.commit(self.source)
        plan = self.run_stage([{"source_commit": revision, "roots": ["Lean/A.lean"]}])
        self.assertEqual(plan["summary"]["source_closure"], 1)
        self.assertEqual(plan["summary"]["resource_identities"], 0)

    def test_resource_path_escapes_and_compound_literals_are_rejected(self):
        with self.assertRaisesRegex(w.ExportError, "escapes source"):
            w.resolve_resource("Lean/A.lean", "../../secret.txt")
        with self.assertRaisesRegex(w.ExportError, "compound"):
            w.include_tokens('def x := include_str "piece" ++ "other"\n')
        with self.assertRaisesRegex(w.ExportError, "include_bin"):
            w.include_tokens('def x := include_bin "file.bin"\n')

    def test_explicit_retained_original_requires_fixed_ledger_binding(self):
        raw = b'import Mathlib\ntheorem generated : True := True.intro\n'
        ledger = b'Original Generated.lean SHA256 ' + w.sha(raw).encode() + b'\n'
        self.write(self.source, "Verification/ledger.md", ledger)
        revision = self.commit(self.source)
        provider = self.directory / "provider.lean"
        provider.write_bytes(raw)
        rows = [{"source_commit": revision, "source_path": "Lean/Generated.lean", "source_sha256": w.sha(raw),
                 "provider": provider.name, "source_origin": {"kind": "retained-original-source",
                    "ledger_commit": revision, "ledger_path": "Verification/ledger.md", "ledger_sha256": w.sha(ledger),
                    "original_source_sha256": w.sha(raw)}}]
        document = self.directory / "providers.json"
        document.write_text(json.dumps(rows))
        plan = self.run_stage([{"source_commit": revision, "roots": ["Lean/Generated.lean"]}], [document])
        self.assertEqual(plan["additions"][0]["source_origin"]["kind"], "retained-original-source")
        rows[0]["source_origin"]["ledger_sha256"] = "f" * 64
        document.write_text(json.dumps(rows))
        with self.assertRaisesRegex(w.ExportError, "ledger SHA differs"):
            self.run_stage([{"source_commit": revision, "roots": ["Lean/Generated.lean"]}], [document], name="bad-stage")

    def test_paid_h0_definition_repair_keeps_effective_and_original_identities(self):
        original = b'import Mathlib\ndef receiverFee := 0\n'
        effective = b'import Mathlib\ndef receiverFee := 1\n'
        self.write(self.source, "Lean/A.lean", original)
        first = self.commit(self.source)
        self.write(self.public, "docs/source/repair.lean", effective)
        supplement_commit = self.commit(self.public)
        origin = {"kind": "H0-source-action-environment-contract-repair",
                  "source_repository": "https://example.org/H0mework.git", "source_commit": supplement_commit,
                  "source_path": "docs/source/repair.lean", "dependency_epoch": first,
                  "original_source_sha256": w.sha(original), "edit_scope": "Actual receiver fee production"}
        owner = self.existing("Lean/A.lean", effective, first, origin=origin)
        self.write(self.source, "unrelated.txt", b'Later fixed epoch\n')
        second = self.commit(self.source)
        plan = self.run_stage([{"source_commit": second, "roots": ["Lean/A.lean"]}])
        selected = plan["sources"][w.source_key(second, "Lean/A.lean")]
        self.assertEqual(selected["source_sha256"], w.sha(effective))
        self.assertEqual(selected["original_git_sha256"], w.sha(original))
        self.assertEqual(selected["source_origin"]["edit_scope"], origin["edit_scope"])
        self.assertEqual(plan["assignments"][w.source_key(second, "Lean/A.lean")], owner["target"])
        alias = plan["source_alias_updates"][0]["source_aliases"][0]
        self.assertEqual(alias["source_origin"]["dependency_epoch"], second)
        self.assertEqual(alias["source_origin"]["inherited_supplement_dependency_epoch"], first)
        self.assertEqual(plan["source_revision_updates"], [])

    def test_unregistered_runtime_pointer_is_reported_without_changing_result(self):
        raw = b'{"command":"/tmp/fixed-audit/run.lean", "result":17, "status":"certified"}'
        self.write(self.source, "Verification/receipt.json", raw)
        revision = self.commit(self.source)
        with self.assertRaisesRegex(w.ExportError, r"runtime_paths.*\/command"):
            self.run_stage([{"source_commit": revision, "artifacts": ["Verification/receipt.json"]}])

    def test_recursive_semantic_reuse_does_not_copy_a_legacy_import_owner(self):
        a = b'import Mathlib\ndef a := 1\n'
        root = b'import A\ndef root := a\n'
        self.write(self.source, "Lean/A.lean", a)
        self.write(self.source, "Lean/Root.lean", root)
        revision = self.commit(self.source)
        self.existing("Lean/A.lean", a, revision, target="H0mework.A1")
        self.existing("Lean/A.lean", a, revision, target="H0mework.A2")
        existing_root = self.existing("Lean/Root.lean", root, revision, target="H0mework.Root", imports={"A": "H0mework.A2"})
        plan = self.run_stage([{"source_commit": revision, "roots": ["Lean/Root.lean"]}])
        self.assertEqual(plan["additions"], [])
        selected = plan["sources"][w.source_key(revision, "Lean/Root.lean")]
        self.assertEqual(selected["target"], existing_root["target"])
        self.assertEqual(selected["canonical_import_owner_equivalence"]["actual_owner_import_targets"], ["H0mework.A2"])

    def test_explicit_runtime_override_and_gzip_keep_all_result_bytes(self):
        raw = b'{"command":"/tmp/fixed-audit/run.lean","status":"certified","result":17,"type":"' + b'P ' * 600000 + b'"}'
        self.write(self.source, "Verification/receipt.json", raw)
        revision = self.commit(self.source)
        provider = self.directory / "receipt.json"
        provider.write_bytes(raw)
        origin = {"kind": "fixed-original-certification", "source_commit": revision,
                  "source_path": "Verification/receipt.json"}
        document = self.directory / "providers.json"
        document.write_text(json.dumps([{"source_commit": revision, "source_path": "Verification/receipt.json",
            "source_sha256": w.sha(raw), "provider": provider.name, "source_origin": origin,
            "runtime_paths": [{"pointer": "/command", "relative": "runtime/fixed-audit/run.lean"}]}]))
        plan = self.run_stage([{"source_commit": revision, "artifacts": ["Verification/receipt.json"]}], [document])
        row = plan["artifacts"][0]
        encoded = (self.directory / "stage/stage" / row["path"]).read_bytes()
        self.assertTrue(row["path"].endswith(".json.gz"))
        restored = gzip.decompress(encoded)
        self.assertEqual(restored, raw.replace(b'/tmp/fixed-audit/run.lean', b'runtime/fixed-audit/run.lean'))
        self.assertEqual(row["source_sha256"], w.sha(raw))
        self.assertEqual(row["compression"]["uncompressed_sha256"], w.sha(restored))

    def test_linked_original_certification_requires_the_actual_verdict_digest(self):
        linked = b'{"exactType":"Nat", "status":"certified"}'
        verdict = json.dumps({"manifest": {"sha256": w.sha(linked)}, "status": "certified"}).encode()
        ledger = b'Original verdict SHA256 ' + w.sha(verdict).encode() + b'\n'
        self.write(self.source, "Verification/ledger.md", ledger)
        revision = self.commit(self.source)
        rows = []
        for name, raw in (("verdict.json", verdict), ("manifest.json", linked)):
            self.write(self.directory, name, raw)
            rows.append({"source_commit": revision, "source_path": "Verification/original/" + name,
                         "source_sha256": w.sha(raw), "provider": name, "source_origin": {
                "kind": "retained-original-certification", "original_artifact_name": name,
                "original_source_sha256": w.sha(raw), "original_verdict_sha256": w.sha(verdict),
                "original_verdict_sha_bindings": [] if name == "verdict.json" else ["manifest.sha256"],
                "ledger_commit": revision, "ledger_path": "Verification/ledger.md", "ledger_sha256": w.sha(ledger)}})
        document = self.directory / "providers.json"
        document.write_text(json.dumps({"schema": "whole-ledger-original-certification-providers/v1", "providers": rows}))
        selection = [{"source_commit": revision, "artifacts": [row["source_path"] for row in rows]}]
        plan = self.run_stage(selection, [document])
        self.assertEqual(len(plan["artifacts"]), 2)
        rows[1]["source_origin"]["original_verdict_sha_bindings"] = ["absent.sha256"]
        document.write_text(json.dumps(rows))
        with self.assertRaisesRegex(w.ExportError, "verdict does not bind"):
            self.run_stage(selection, [document], name="bad-stage")

    def test_top_level_certification_list_keeps_its_original_shape(self):
        raw = b'[{"root":"/Users/fixture/Homework","result":17,"status":"certified"}]'
        self.write(self.source, "Verification/list.json", raw)
        revision = self.commit(self.source)
        plan = self.run_stage([{"source_commit": revision, "artifacts": ["Verification/list.json"]}])
        row = plan["artifacts"][0]
        self.assertEqual((self.directory / "stage/stage" / row["path"]).read_bytes(), raw.replace(b'/Users/fixture/Homework', b'.'))

    def test_explicit_text_runtime_spans_use_the_registered_v2_contract(self):
        raw = b'Original certified runtime: /Volumes/Fixture/audit/run.lean\nMachine fact: True\n'
        self.write(self.source, "Verification/ledger.md", raw)
        revision = self.commit(self.source)
        self.write(self.directory, "ledger.md", raw)
        begin = raw.index(b'/Volumes/')
        end = raw.index(b'\n', begin)
        rows = [{"source_commit": revision, "source_path": "Verification/ledger.md", "source_sha256": w.sha(raw),
                 "provider": "ledger.md",
                 "runtime_paths": [{"begin": begin, "end": end, "relative": "runtime/audit/run.lean"}]}]
        document = self.directory / "providers.json"
        document.write_text(json.dumps(rows))
        plan = w.stage(
            self.public, self.source, self.selection([{"source_commit": revision, "roots": ["Lean/UnusedMissing.lean"],
                "artifacts": ["Verification/ledger.md"]}]), self.directory / "text-stage", [document], artifacts_only=True)
        row = plan["artifacts"][0]
        self.assertEqual(row["publication"]["kind"], w.pub.TEXT_RUNTIME_KIND)
        self.assertEqual((self.directory / "text-stage/stage" / row["path"]).read_bytes(),
                         raw.replace(b'/Volumes/Fixture/audit/run.lean', b'runtime/audit/run.lean'))
        self.assertEqual(plan["sources"], {})

    def test_large_include_str_input_remains_raw(self):
        raw = b'{"type":"' + b'P ' * 600000 + b'","result":17}'
        self.write(self.source, "Verification/receipt.json", raw)
        self.write(self.source, "Lean/A.lean", b'import Mathlib\ndef text := include_str "../Verification/receipt.json"\n')
        revision = self.commit(self.source)
        plan = self.run_stage([{"source_commit": revision, "roots": ["Lean/A.lean"]}])
        row = plan["artifacts"][0]
        self.assertNotIn("compression", row)
        self.assertTrue(row["path"].endswith(".json"))
        self.assertEqual((self.directory / "stage/stage" / row["path"]).read_bytes(), raw)

    def test_quoted_private_name_constructor_follows_the_actual_import_owner(self):
        raw = (b'import A\nimport Lean\n'
               b'def owner := Lean.mkPrivateNameCore `A `Domain.value\n'
               b'-- Lean.mkPrivateNameCore `Fake `NotARealDeclaration\n')
        self.write(self.source, "Lean/A.lean", b'import Mathlib\ndef a := 1\n')
        self.write(self.source, "Lean/Bindings.lean", raw)
        revision = self.commit(self.source)
        plan = self.run_stage([{"source_commit": revision, "roots": ["Lean/Bindings.lean"]}])
        row = next(row for row in plan["additions"] if row["source_path"] == "Lean/Bindings.lean")
        rule = row["private_owner_expression_rewrites"][0]
        owner = plan["assignments"][w.source_key(revision, "Lean/A.lean")]
        self.assertEqual(rule["source_expression"], "Lean.mkPrivateNameCore `A `Domain.value")
        self.assertEqual(rule["target_expression"], "Lean.mkPrivateNameCore `" + owner + " `Domain.value")
        with patch.object(sv, "ROOT", self.directory / "stage/stage"):
            self.assertEqual(sv.module_views(row, {})[1], raw)

    def test_split_private_owner_follows_the_actual_import_and_ignores_lookalikes(self):
        expression = '("_private.A".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous'
        fake = expression.replace('_private.A', '_private.Missing')
        raw = ('import A\nimport Lean\nlet head := ' + expression + '\n'
               'let again := ' + expression + '\nlet full := Lean.Name.num head 0\n-- ' + fake + '\n'
               'def message := r##"' + fake + '"##\n').encode()
        self.write(self.source, 'Lean/A.lean', b'import Mathlib\ndef a := 1\n')
        self.write(self.source, 'Lean/Bindings.lean', raw)
        revision = self.commit(self.source)
        plan = self.run_stage([{'source_commit': revision, 'roots': ['Lean/Bindings.lean']}])
        row = next(row for row in plan['additions'] if row['source_path'] == 'Lean/Bindings.lean')
        owner = plan['assignments'][w.source_key(revision, 'Lean/A.lean')]
        rules = row['private_owner_expression_rewrites']
        self.assertEqual(rules, [{'source_expression': expression,
                                'target_expression': expression.replace('_private.A', '_private.' + owner),
                                'count': 2}])
        with patch.object(sv, 'ROOT', self.directory / 'stage/stage'):
            self.assertEqual(sv.module_views(row, {})[1], raw)

    def test_nested_private_owner_uses_the_actual_import_without_changing_the_index(self):
        expression = sv.private_str_owner_expression('A')
        fake = sv.private_str_owner_expression('Missing')
        raw = ('import A\nimport Lean\nlet first := (Lean.Name.num ' + expression + ' 3)\n'
               'let second := (Lean.Name.num ' + expression + ' 7)\n'
               '-- (Lean.Name.num ' + fake + ' 0)\n').encode()
        self.write(self.source, 'Lean/A.lean', b'import Mathlib\ndef a := 1\n')
        self.write(self.source, 'Lean/Bindings.lean', raw)
        revision = self.commit(self.source)
        plan = self.run_stage([{'source_commit': revision, 'roots': ['Lean/Bindings.lean']}])
        row = next(row for row in plan['additions'] if row['source_path'] == 'Lean/Bindings.lean')
        owner = plan['assignments'][w.source_key(revision, 'Lean/A.lean')]
        self.assertEqual(row['private_owner_expression_rewrites'], [{'source_expression': expression,
                         'target_expression': sv.private_str_owner_expression(owner), 'count': 2}])
        with patch.object(sv, 'ROOT', self.directory / 'stage/stage'):
            self.assertEqual(sv.module_views(row, {})[1], raw)

    def test_artifact_only_reconciles_an_unrelated_source_map_change(self):
        raw = b'{"result":17}'
        self.write(self.source, "Verification/receipt.json", raw)
        revision = self.commit(self.source)
        build = w.Planner.build
        def changed(instance, *args, **kwargs):
            result = build(instance, *args, **kwargs)
            value = json.loads((instance.root / "tools/export-map.json").read_bytes())
            value["scope"] = "A separately admitted source owner"
            w.write_json(instance.root / "tools/export-map.json", value)
            return result
        with patch.object(w.Planner, "build", changed):
            plan = w.stage(self.public, self.source,
                self.selection([{"source_commit": revision, "artifacts": ["Verification/receipt.json"]}]),
                self.directory / "artifact-stage", artifacts_only=True)
        self.assertEqual(plan["export_map_sha256"], w.sha((self.public / "tools/export-map.json").read_bytes()))
        self.assertEqual(plan["baseline_reconciliation"]["new_artifact_paths_rechecked"], 1)
        self.assertFalse(plan["baseline_reconciliation"]["source_scope_consumed"])

    def test_artifact_reconciliation_rejects_a_changed_selected_public_receipt(self):
        path = "evidence/receipt.json"
        raw = b'{"result":17}'
        self.write(self.public, path, raw)
        row = {"path": path, "source": "Verification/receipt.json", "source_revision": "a" * 40,
               "source_sha256": w.sha(raw), "target_sha256": w.sha(raw)}
        self.export["artifacts"] = [row]
        self.write_map()
        planner = w.Planner(self.public, self.source, {"selections": []})
        try:
            latest = json.loads(planner.export_bytes)
            latest["artifacts"][0]["target_sha256"] = "f" * 64
            plan = {"reuse_artifacts": [{"public_path": path}], "artifacts": [], "artifact_revision_updates": [],
                    "export_map_sha256": w.sha(planner.export_bytes)}
            with self.assertRaisesRegex(w.ExportError, "Selected artifact changed"):
                w.reconcile_artifact_baseline(planner, plan, json.dumps(latest).encode())
        finally:
            planner.close()

    def git_supplement_fixture(self):
        original = b'import Mathlib\ntheorem same : True := by rfl\n'
        effective = b'import Mathlib\ntheorem same : True := True.intro\n'
        self.write(self.source, "Lean/A.lean", original)
        epoch = self.commit(self.source)
        self.write(self.source, "Lean/A.lean", effective)
        repair = self.commit(self.source)
        origin = {"kind": "git-source-supplement", "original_path": "Lean/A.lean", "source_commit": repair,
                  "source_sha256": w.sha(effective)}
        owner = self.existing("Lean/A.lean", effective, epoch, origin=origin)
        return original, effective, epoch, repair, owner

    def test_same_epoch_signed_git_supplement_without_original_digest_is_reused(self):
        original, effective, epoch, repair, owner = self.git_supplement_fixture()
        plan = self.run_stage([{"source_commit": epoch, "roots": ["Lean/A.lean"]}])
        selected = plan["sources"][w.source_key(epoch, "Lean/A.lean")]
        self.assertEqual(selected["target"], owner["target"])
        self.assertEqual(selected["source_sha256"], w.sha(effective))
        self.assertEqual(selected["original_git_sha256"], w.sha(original))
        self.assertEqual(selected["source_origin"]["original_source_commit"], epoch)
        self.assertEqual(plan["additions"], [])

    def test_explicit_provider_overrides_the_same_epoch_git_supplement(self):
        original, effective, epoch, repair, owner = self.git_supplement_fixture()
        override = b'import Mathlib\ntheorem same : True := by exact True.intro\n'
        self.write(self.source, "Lean/A.lean", override)
        override_commit = self.commit(self.source)
        self.write(self.directory, "override.lean", override)
        provider = self.directory / "override.json"
        provider.write_text(json.dumps([{"source_commit": epoch, "source_path": "Lean/A.lean", "source_sha256": w.sha(override),
            "provider": "override.lean", "source_origin": {"kind": "git-source-supplement", "source_commit": override_commit,
                "source_path": "Lean/A.lean", "original_source_sha256": w.sha(original)}}]))
        plan = self.run_stage([{"source_commit": epoch, "roots": ["Lean/A.lean"]}], [provider])
        self.assertEqual(plan["sources"][w.source_key(epoch, "Lean/A.lean")]["source_sha256"], w.sha(override))
        self.assertNotEqual(plan["assignments"][w.source_key(epoch, "Lean/A.lean")], owner["target"])

    def test_git_supplement_cannot_migrate_to_an_unregistered_epoch(self):
        original, effective, epoch, repair, owner = self.git_supplement_fixture()
        self.write(self.source, "Lean/A.lean", original)
        other_epoch = self.commit(self.source)
        plan = self.run_stage([{"source_commit": other_epoch, "roots": ["Lean/A.lean"]}])
        selected = plan["sources"][w.source_key(other_epoch, "Lean/A.lean")]
        self.assertEqual(selected["source_sha256"], w.sha(original))
        self.assertNotIn("source_origin", selected)
        self.assertNotEqual(selected["target"], owner["target"])


if __name__ == "__main__":
    unittest.main()
