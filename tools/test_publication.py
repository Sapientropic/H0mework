"""Checks for receipt publication and public/exact source-view identity."""
import json
import gzip
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import publication as p
import source_view as s

FIXTURE_ROOT = "/".join(["", "Users", "sample", "Documents", "Homework"])


class ModuleImportTests(unittest.TestCase):
    def test_module_visibility_and_exact_relocation(self):
        raw = 'module\npublic import Source.A\npublic meta import Source.B\nimport all Source.C\ndef value := 1\n'
        tokens = s.import_tokens(raw)
        self.assertEqual([name for _, _, name in tokens], ['Source.A', 'Source.B', 'Source.C'])
        mapping = {name: 'H0mework.' + name for _, _, name in tokens}
        public = s.transform(raw, tokens, mapping).decode()
        self.assertIn('public meta import H0mework.Source.B', public)
        self.assertEqual(s.transform(public, s.import_tokens(public),
                                     {target: source for source, target in mapping.items()}), raw.encode())

    def test_plain_import_still_accepts_continuations(self):
        self.assertEqual([token[2] for token in s.import_tokens('import Source.A\n  Source.B\n')],
                         ['Source.A', 'Source.B'])

    def test_pinned_external_import_is_preserved(self):
        raw = 'module\npublic import Aesop\npublic import QuantumInfo.Entropy.DPI\n'
        public = s.transform(raw, s.import_tokens(raw),
                             {'QuantumInfo.Entropy.DPI': 'H0mework.ThirdParty.QuantumInfo.Entropy.DPI'})
        self.assertIn(b'public import Aesop\n', public)
        self.assertIn(b'public import H0mework.ThirdParty.QuantumInfo.Entropy.DPI\n', public)

    def test_invalid_visibility_is_rejected(self):
        for raw in ('public import Source.A\n', 'module\npublic import all Source.A\n',
                    'module\nprivate import Source.A\n', 'module\npublic import\n',
                    'module\ndef x := 1\npublic import Source.A\n'):
            with self.subTest(raw=raw), self.assertRaises(s.ViewError):
                s.import_tokens(raw)


class DynamicPrivateOwnerTests(unittest.TestCase):
    def test_indexed_schema_keeps_its_original_file_and_certificate(self):
        raw = ('let file := if i=0 then "SourcePilot" else "SourceRows" ++ toString(i/16)\n'
               'let schema := Name.str (Name.num (Name.str `_private file) 0) "schema"\n')
        rule = {'source_expression': '(Name.str `_private file)',
                'target_expression': '(Name.append `_private ("H0mework.P." ++ file).toName)', 'count': 1}
        public = s.rewrite_private_owner_expressions(raw, [rule])
        self.assertTrue(public.startswith(raw.splitlines(keepends=True)[0]))
        self.assertIn(' 0) "schema"', public)
        self.assertEqual(s.rewrite_private_owner_expressions(public, [rule], reverse=True), raw)

    def test_string_module_name_preserves_the_row_selection(self):
        raw = ('let moduleName := if row=0 then "SourcePilot" else "SourceRows" ++ toString(row/16)\n'
               'let current := Name.num (Name.str `_private moduleName) 0\n')
        rule = {'source_expression': '(Name.str `_private moduleName)',
                'target_expression': '(Name.append `_private ("H0mework.P." ++ moduleName).toName)', 'count': 1}
        public = s.rewrite_private_owner_expressions(raw, [rule])
        self.assertTrue(public.startswith(raw.splitlines(keepends=True)[0]))
        self.assertEqual(s.rewrite_private_owner_expressions(public, [rule], reverse=True), raw)

    def test_family_and_private_index_are_preserved(self):
        raw = ('  let moduleName := Name.mkSimple ("SourceValues"++family)\n'
               '  let paid := Name.str (Name.num (Name.str `_private moduleName.toString) 0) "value"\n')
        rules = [{'source_expression': '  let moduleName := Name.mkSimple ("SourceValues"++family)',
                  'target_expression': '  let moduleName := ("H0mework.P.SourceValues"++family).toName', 'count': 1},
                 {'source_expression': '(Name.str `_private moduleName.toString)',
                  'target_expression': '(Name.append `_private moduleName)', 'count': 1}]
        public = s.rewrite_private_owner_expressions(raw, rules)
        self.assertIn('Name.num (Name.append `_private moduleName) 0', public)
        self.assertEqual(s.rewrite_private_owner_expressions(public, rules, reverse=True), raw)

    def test_single_owner_and_lookalike_comment(self):
        expression = '(Name.str `_private "SourceTail")'
        raw = '-- ' + expression + '\nlet name := ' + expression + '\n'
        rules = [{'source_expression': expression,
                  'target_expression': '(`_private.H0mework.P.SourceTail)', 'count': 1}]
        public = s.rewrite_private_owner_expressions(raw, rules)
        self.assertTrue(public.startswith('-- ' + expression))
        self.assertEqual(s.rewrite_private_owner_expressions(public, rules, reverse=True), raw)
        with self.assertRaises(s.ViewError):
            s.rewrite_private_owner_expressions(raw, [{**rules[0], 'target_expression': '(True.intro)'}])
        with self.assertRaises(s.ViewError):
            s.rewrite_private_owner_expressions(raw + 'let another := ' + expression, rules)


def fixture(raw: bytes) -> bytes:
    return raw.replace(b"@ROOT@", FIXTURE_ROOT.encode())


class PublicationTests(unittest.TestCase):
    def test_source_text_runtime_spans_preserve_the_program(self):
        raw = fixture(b'ROOT = Path("@ROOT@")\nvalue = 1.2300000000000000001\n')
        text = raw.decode()
        begin = text.index(FIXTURE_ROOT)
        rules = [{'begin': begin, 'end': begin + len(FIXTURE_ROOT), 'relative': '.'}]
        public = p.text_runtime_paths(raw, rules)
        self.assertEqual(public, b'ROOT = Path(".")\nvalue = 1.2300000000000000001\n')
        row = {'source_sha256': p.sha(raw), 'target_sha256': p.sha(public),
               'publication': {'kind': p.TEXT_KIND, 'runtime_paths': rules,
                               'payload_sha256': p.sha(public)}}
        self.assertEqual(p.verify_artifact(public, row, raw), public)
        changed = public.replace(b'1.230', b'2.230')
        row['target_sha256'] = p.sha(changed)
        with self.assertRaises(p.PublicationError):
            p.verify_artifact(changed, row, raw)
        with self.assertRaises(p.PublicationError):
            p.text_runtime_paths(raw, [{**rules[0], 'begin': 0}])

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


class PublicationSizeTests(unittest.TestCase):
    def test_limit_boundary_and_explicit_override(self):
        p.verify_file_size(p.MAX_PUBLIC_FILE_BYTES, "build.log.zst")
        with self.assertRaisesRegex(p.PublicationError, "build.log"):
            p.verify_file_size(p.MAX_PUBLIC_FILE_BYTES + 1, "build.log")
        p.verify_file_size(12, "small.log", limit=12)
        with self.assertRaises(p.PublicationError):
            p.verify_file_size(13, "small.log", limit=12)

    def test_compressed_extension_does_not_exempt_an_oversized_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with (root / "oversized.log.zst").open("wb") as handle:
                handle.truncate(p.MAX_PUBLIC_FILE_BYTES + 1)
            with self.assertRaisesRegex(p.PublicationError, "oversized.log.zst"):
                p.verify_file_sizes(root, ["oversized.log.zst"])
            (root / "oversized.log.zst").unlink()
            with (root / "fresh-retarded-inlet.json.gz").open("wb") as handle:
                handle.truncate(55 * 1024 * 1024)
            self.assertEqual(p.verify_file_sizes(root, ["fresh-retarded-inlet.json.gz"]), 1)

    def test_lossless_artifact_restores_source_identity(self):
        original = b'[{"name":"producer","unsafe":false,"partial":false}]\n'
        compressed = gzip.compress(original, mtime=0)
        row = {'source_sha256': p.sha(original), 'target_sha256': p.sha(compressed),
               'compression': {'kind': 'gzip', 'uncompressed_bytes': len(original),
                               'uncompressed_sha256': p.sha(original)}}
        self.assertEqual(p.verify_artifact(compressed, row), original)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'declarations.json.gz').write_bytes(compressed)
            with patch.object(s, 'ROOT', root):
                self.assertEqual(s.artifact_views({**row, 'path': 'declarations.json.gz'}),
                                 (original, original))
        row['compression']['uncompressed_bytes'] += 1
        with self.assertRaisesRegex(p.PublicationError, 'Uncompressed artifact'):
            p.verify_artifact(compressed, row)

    def test_compressed_receipt_retains_declared_payload(self):
        original = fixture(b'{"root":"@ROOT@","value":17}\n')
        public, _ = p.normalize_paths(original)
        compressed = gzip.compress(public, mtime=0)
        row = {'source_sha256': p.sha(original), 'target_sha256': p.sha(compressed),
               'compression': {'kind': 'gzip', 'uncompressed_bytes': len(public),
                               'uncompressed_sha256': p.sha(public)},
               'publication': {'kind': p.KIND, 'payload_sha256': p.sha(public)}}
        self.assertEqual(p.verify_artifact(compressed, row, original), public)
        bad = {**row, 'compression': {**row['compression'], 'kind': 'zstd'}}
        with self.assertRaisesRegex(p.PublicationError, 'Unsupported'):
            p.verify_artifact(compressed, bad)

    def test_export_rejects_size_before_mutating_metadata(self):
        class Oversized:
            def __len__(self):
                return p.MAX_PUBLIC_FILE_BYTES + 1
        row = {"target_sha256": "unchanged"}
        with self.assertRaises(p.PublicationError):
            p.publish_outputs({"evidence/build.log": Oversized()}, [], [row], None)
        self.assertEqual(row, {"target_sha256": "unchanged"})

    def test_source_bundle_checks_public_target_instead_of_source_address(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with (root / "published.lean").open("wb") as handle:
                handle.truncate(p.MAX_PUBLIC_FILE_BYTES + 1)
            modules = {"source/Original.lean": [{"path": "published.lean"}]}
            with patch.object(s, "ROOT", root), patch.object(s, "load_map", return_value=({}, modules, {}, {})):
                with self.assertRaisesRegex(p.PublicationError, "published.lean"):
                    s.verify_all()


class ProofBodyRewriteTests(unittest.TestCase):
    source = "theorem total (n : Nat) : n = n := by\n  rfl\n"
    public = "theorem total (n : Nat) : n = n := by\n  exact Eq.refl n\n"

    def rules(self):
        return [{"declaration": "total", "source": self.source, "public": self.public}]

    def test_round_trip_and_no_implicit_adapter(self):
        text = "import Mathlib\n" + self.source + "def unchanged := 7\n"
        adapted = s.rewrite_proof_bodies(text, self.rules())
        self.assertEqual(adapted, text.replace(self.source, self.public))
        self.assertEqual(s.rewrite_proof_bodies(adapted, self.rules(), reverse=True), text)
        self.assertEqual(s.rewrite_proof_bodies(text, None), text)

    def test_default_view_is_adapted_and_exact_override_restores_source(self):
        original = ("import Mathlib\n" + self.source).encode()
        adapted = ("import Mathlib\n" + self.public).encode()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Proof.lean").write_bytes(adapted)
            row = {"source": "Original.Proof", "source_path": "Lean/Original/Proof.lean",
                   "source_revision": "a" * 40, "target": "H0mework.Proof", "path": "Proof.lean",
                   "source_sha256": p.sha(original), "target_sha256": p.sha(adapted),
                   "view_sha256": p.sha(adapted), "proof_body_rewrites": self.rules()}
            mapping = root / "export-map.json"
            mapping.write_text(json.dumps({"schema": 2, "lean_directory": "Lean", "modules": [row], "artifacts": []}))
            with patch.object(s, "ROOT", root), patch.object(s, "EXPORT_MAP", mapping):
                self.assertEqual(s.module_views(row, {}), (adapted, original))
                path = "Lean/Original/Proof.lean"
                self.assertEqual(s.reconstruct(paths=[path])[0][path], adapted)
                self.assertEqual(s.reconstruct(paths=[path], exact=True)[0][path], original)

    def test_statement_change_and_new_top_level_declaration_are_rejected(self):
        for public in [self.public.replace("n = n", "n = 0"), self.public + "def smuggled := 0\n"]:
            with self.subTest(public=public), self.assertRaises(s.ViewError):
                s.rewrite_proof_bodies(self.source, [{**self.rules()[0], "public": public}])

    def test_missing_or_duplicate_anchor_is_rejected(self):
        for text in ["-- another theorem\n", self.source + self.source]:
            with self.subTest(text=text), self.assertRaises(s.ViewError):
                s.rewrite_proof_bodies(text, self.rules())

    def test_resigned_nonproof_tampering_still_fails_original_identity(self):
        original = ("import Mathlib\n" + self.source + "def value := 7\n").encode()
        adapted = ("import Mathlib\n" + self.public + "def value := 8\n").encode()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Proof.lean").write_bytes(adapted)
            row = {"path": "Proof.lean", "source_path": "Proof.lean", "source_sha256": p.sha(original),
                   "target_sha256": p.sha(adapted), "view_sha256": p.sha(adapted), "proof_body_rewrites": self.rules()}
            with patch.object(s, "ROOT", root), self.assertRaisesRegex(s.ViewError, "Reconstructed source digest differs"):
                s.module_views(row, {})


class DeclaredRuntimePathTests(unittest.TestCase):
    def test_only_selected_pointer_changes_and_number_bytes_survive(self):
        raw = fixture(b'{"log":"@ROOT@/audit.log","same":"@ROOT@/audit.log","value":1.2300000000000000001,"failed":true}')
        rules = [{"pointer": "/log", "relative": "audit.log"}]
        result, count = p.declared_runtime_paths(raw, rules)
        self.assertEqual(count, 1)
        self.assertEqual(json.loads(result)["same"], FIXTURE_ROOT + "/audit.log")
        self.assertIn(b'"value":1.2300000000000000001,"failed":true', result)
        self.assertEqual(p.declared_runtime_paths(result, rules), (result, 0))

    def test_declared_key_slot_and_collision_never_change_payload_values(self):
        raw = fixture(b'{"inputs":{"@ROOT@/a.json":"original-digest"},"result":17}')
        result, count = p.declared_runtime_paths(raw, [{"pointer": "/inputs", "key_index": 0, "relative": "a.json"}])
        self.assertEqual(count, 1)
        self.assertEqual(json.loads(result), {"inputs": {"a.json": "original-digest"}, "result": 17})
        with self.assertRaises(p.PublicationError):
            p.declared_runtime_paths(raw, [{"pointer": "/absent", "relative": "a.json"}])
        collision = fixture(b'{"inputs":{"@ROOT@/a.json":"x","a.json":"y"}}')
        with self.assertRaises(p.PublicationError):
            p.declared_runtime_paths(collision, [{"pointer": "/inputs", "key_index": 0, "relative": "a.json"}])

    def test_declared_publication_rejects_tampered_result_with_updated_target_hash(self):
        raw = fixture(b'{"log":"@ROOT@/audit.log","result":17}')
        rules = [{"pointer": "/log", "relative": "audit.log"}]
        public = p.declared_runtime_paths(raw, rules)[0]
        row = {"source_sha256": p.sha(raw), "target_sha256": p.sha(public), "publication": {
            "kind": p.DECLARED_KIND, "runtime_paths": rules, "payload_sha256": p.sha(public)}}
        p.verify_artifact(public, row, raw)
        tampered = public.replace(b'17', b'18')
        row["target_sha256"] = p.sha(tampered)
        with self.assertRaises(p.PublicationError):
            p.verify_artifact(tampered, row, raw)


class PrivateNameRewriteTests(unittest.TestCase):
    source = "_private.CanonicalPreparationEngineProgram"
    target = "_private.H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram"

    def rules(self, target=None):
        return [{"source_name": self.source, "target_name": target or self.target}]

    def test_name_quotation_and_numeric_private_reference_round_trip(self):
        original = (f"let owner := Name.num `{self.source} 0\n"
                    f"#check {self.source}.0.LowEnergy.engine\n"
                    f"def quoted := `{self.source}.12.LowEnergy.engine\n")
        exported = s.rewrite_private_names(original, self.rules())
        self.assertEqual(exported, original.replace(self.source, self.target))
        self.assertEqual(s.rewrite_private_names(exported, self.rules(), reverse=True), original)

    def test_explicit_version_and_no_declared_rewrites(self):
        original = f"let owner := Name.num `{self.source} 0\n"
        other = self.target.replace(".AB.", ".AC.")
        self.assertEqual(s.rewrite_private_names(original, self.rules(other)),
                         original.replace(self.source, other))
        self.assertEqual(s.rewrite_private_names(original, None), original)
        self.assertEqual(s.rewrite_private_names(original, []), original)
        self.assertEqual(s.rewrite_private_names(original, self.rules(), reverse=True), original)

    def test_longer_names_comments_and_strings_are_unchanged(self):
        names = [self.source + tail for tail in (
            "Longer", "'", "?", "!", "α", "℀", ".Extra.0.engine", ".0extra", ".engine")]
        names += ["Longer" + self.source, "Namespace." + self.source]
        untouched = ("\n".join(f"#check {name}" for name in names) + "\n"
                     f"-- `{self.source}\n"
                     f"/- nested /- `{self.source} -/ still `{self.source} -/\n"
                     f'def string := "{self.source}"\n'
                     f'def escaped := "\\\"{self.source}\\\""\n'
                     f'def raw := r##"{self.source}"##\n'
                     f"#check «{self.source}»\n")
        original = untouched + f"let owner := Name.num `{self.source} 0\n"
        self.assertEqual(s.rewrite_private_names(original, self.rules()),
                         untouched + f"let owner := Name.num `{self.target} 0\n")

    def test_rules_apply_simultaneously_and_preserve_longer_declared_owner(self):
        rules = [{"source_name": "_private.A", "target_name": "_private.B"},
                 {"source_name": "_private.B", "target_name": "_private.C"},
                 {"source_name": "_private.A.Child", "target_name": "_private.B.Child"}]
        original = "#check `_private.A\n#check _private.B.0.f\n#check `_private.A.Child\n"
        exported = "#check `_private.B\n#check _private.C.0.f\n#check `_private.B.Child\n"
        self.assertEqual(s.rewrite_private_names(original, rules), exported)
        self.assertEqual(s.rewrite_private_names(exported, rules, reverse=True), original)

    def test_malformed_or_conflicting_metadata_is_rejected(self):
        malformed = [{}, "rules", [None], [{"source_name": self.source}],
                     [{"source_name": self.source, "target_name": self.target, "extra": True}]]
        for name in (None, 1, "CanonicalPreparationEngineProgram", "_private.",
                     "_private.A.0", "_private.A B", "`_private.A"):
            malformed.append([{"source_name": name, "target_name": self.target}])
            malformed.append([{"source_name": self.source, "target_name": name}])
        malformed += [self.rules() * 2,
                      self.rules() + [{"source_name": self.source, "target_name": "_private.Other"}],
                      self.rules() + [{"source_name": "_private.Other", "target_name": self.target}]]
        for rules in malformed:
            with self.subTest(rules=rules), self.assertRaises(s.ViewError):
                s.rewrite_private_names("", rules)


class PrivateOwnerStringRewriteTests(unittest.TestCase):
    source = "_private.SourceChannelFundamentalPotential"
    target = "_private.H0mework.Versions.LE1.Physics.AlphaSource.SourceChannelFundamentalPotential"

    def rules(self):
        return [{"source_owner": self.source, "target_owner": self.target}]

    def lookup(self, owner=None):
        return '  name.toString.startsWith "' + (owner or self.source) + '." && privateToUserName name == wanted\n'

    def test_registered_executable_prefix_round_trips_without_touching_other_strings(self):
        untouched = (f'-- name.toString.startsWith "{self.source}."\n'
                     f'/- nested /- name.toString.startsWith "{self.source}." -/ comment -/\n'
                     f'def ordinary := "{self.source}."\n'
                     f'def message := "owner {self.source}."\n'
                     f'def escaped := "\\\"{self.source}.\\\""\n'
                     f'def raw := r##"{self.source}."##\n'
                     f'#check «name.startsWith "{self.source}."»\n'
                     f'name.startsWith "{self.source}Longer."\n'
                     f'name.startsWith "{self.source}.Child."\n'
                     f'name.startsWith "{self.source}.0.function"\n')
        original = untouched + self.lookup()
        exported = s.rewrite_private_owner_strings(original, self.rules())
        self.assertEqual(exported, untouched + self.lookup(self.target))
        self.assertEqual(s.rewrite_private_owner_strings(exported, self.rules(), reverse=True), original)
        self.assertEqual(s.rewrite_private_owner_strings(original, None), original)
        self.assertEqual(s.rewrite_private_owner_strings(original, []), original)

    def test_missing_raw_or_duplicate_prefix_is_rejected(self):
        for text in (f'def ordinary := "{self.source}."\n',
                     '-- ' + self.lookup(),
                     f'name.startsWith r##"{self.source}."##\n',
                     f'name.startsWith "{self.source}.Child."\n',
                     self.lookup() * 2):
            with self.subTest(text=text), self.assertRaises(s.ViewError):
                s.rewrite_private_owner_strings(text, self.rules())

    def test_rules_are_bijective_and_applied_simultaneously(self):
        rules = [{"source_owner": "_private.A", "target_owner": "_private.B"},
                 {"source_owner": "_private.B", "target_owner": "_private.C"}]
        original = 'name.startsWith "_private.A."\nname.startsWith "_private.B."\n'
        exported = 'name.startsWith "_private.B."\nname.startsWith "_private.C."\n'
        self.assertEqual(s.rewrite_private_owner_strings(original, rules), exported)
        self.assertEqual(s.rewrite_private_owner_strings(exported, rules, reverse=True), original)
        invalid = [{}, [None], self.rules() * 2,
                   self.rules() + [{"source_owner": "_private.Other", "target_owner": self.target}],
                   [{"source_owner": self.source, "target_owner": self.target, "extra": True}]]
        for name in (None, 1, "Source", "_private.", "_private.A.0", "_private.A B", self.source + "."):
            invalid.append([{"source_owner": name, "target_owner": self.target}])
            invalid.append([{"source_owner": self.source, "target_owner": name}])
        for rules in invalid:
            with self.subTest(rules=rules), self.assertRaises(s.ViewError):
                s.rewrite_private_owner_strings(original, rules)

    def test_source_view_restores_owner_literal_and_rejects_resigned_proof_tampering(self):
        original = ('import SourceChannelRadialLayer\n'
                    'elab "paidRadialGreen% " id:ident : term => do\n' + self.lookup()
                    + 'theorem paid : True := by trivial\n')
        exported = s.rewrite_private_owner_strings(original, self.rules())
        exported = s.transform(exported, s.import_tokens(exported),
                               {"SourceChannelRadialLayer": "H0mework.LE1.SourceChannelRadialLayer"})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Slope.lean").write_bytes(exported)
            row = {"path": "Slope.lean", "source_path": "Original.lean", "target_sha256": p.sha(exported),
                   "source_sha256": p.sha(original.encode()),
                   "import_map": {"H0mework.LE1.SourceChannelRadialLayer": "SourceChannelRadialLayer"},
                   "private_owner_string_rewrites": self.rules()}
            with patch.object(s, "ROOT", root):
                self.assertEqual(s.module_views(row, {}), (original.encode(), original.encode()))
                with self.assertRaisesRegex(s.ViewError, "Reconstructed source digest differs"):
                    s.module_views({**row, "private_owner_string_rewrites": []}, {})
                changed = exported.replace(b": True :=", b": False :=")
                (root / "Slope.lean").write_bytes(changed)
                with self.assertRaisesRegex(s.ViewError, "Reconstructed source digest differs"):
                    s.module_views({**row, "target_sha256": p.sha(changed)}, {})


class AuditRewriteTests(unittest.TestCase):
    source = "SaturationMonoid.PhysicsCore.Bell.Source"
    target = "H0mework.Versions.AE.Physics.Bell.Source"
    variable = "BELL_DETECTOR_PAID_NAMES"

    def rules(self):
        return [{"source_module": self.source, "target_module": self.target}]

    def boundary(self):
        return (f'  let some paidPath ← IO.getEnv "{self.variable}" |\n'
                '    throwError "missing paid source-dependency boundary"\n'
                '  let paidText ← IO.FS.readFile paidPath\n')

    def test_module_quotation_relocation_stays_in_observer(self):
        prefix = f'def sameSpelling := `{self.source}\n'
        tail = (f'  let candidate := `{self.source}\n'
                f'  let declaration := `{self.source}.theorem\n'
                f'  let text := "`{self.source}"\n'
                f'  -- `{self.source}\n')
        original = prefix + 'open Lean Elab Command in\nrun_cmd do\n' + tail
        public = s.rewrite_audit_module_names(original, self.rules())
        self.assertTrue(public.startswith(prefix))
        self.assertEqual(public.count('`' + self.target), 1)
        self.assertIn('`' + self.source + '.theorem', public)
        self.assertEqual(s.rewrite_audit_module_names(public, self.rules(), reverse=True), original)

    def test_unregistered_or_noninvertible_module_rules_reject(self):
        for rules in ({}, [self.rules()[0], self.rules()[0]],
                      [{"source_module": "../Source", "target_module": self.target}],
                      [{"source_module": self.source, "target_module": self.target, "extra": True}]):
            with self.subTest(rules=rules), self.assertRaises(s.ViewError):
                s.rewrite_audit_module_names('\nrun_cmd do\n', rules)
        with self.assertRaises(s.ViewError):
            s.rewrite_audit_module_names('def outside := `' + self.source + '\n', self.rules())

    def test_elaborated_observer_relocates_only_module_quotations(self):
        prefix = (f'def outside := `{self.source}\n'
                  '-- run_cmd do\n'
                  '/-\nelab "#fake" : command => do\n-/\n')
        tail = (f'  let candidate := `{self.source}\n'
                f'  let declaration := `{self.source}.theorem\n'
                f'  let resolved := ``{self.source}\n'
                f'  let literal := "`{self.source}"\n'
                f'  -- `{self.source}\n')
        original = prefix + 'elab "#audit" : command => do\n' + tail + '\n#audit\n'
        public = s.rewrite_audit_module_names(original, self.rules())
        self.assertTrue(public.startswith(prefix))
        self.assertEqual(public.count('`' + self.target), 1)
        self.assertIn('``' + self.source, public)
        self.assertIn('`' + self.source + '.theorem', public)
        self.assertEqual(s.rewrite_audit_module_names(public, self.rules(), reverse=True), original)

    def test_module_rewrite_rejects_resolved_declaration_and_ambiguous_observers(self):
        for text in (f'run_cmd do\n  let declaration := ``{self.source}\n',
                     f'run_cmd do\n  let candidate := `{self.source}\nrun_cmd do\n',
                     f'elab "#one" : command => do\n  let candidate := `{self.source}\n'
                     'elab "#two" : command => do\n'):
            with self.subTest(text=text), self.assertRaises(s.ViewError):
                s.rewrite_audit_module_names(text, self.rules())

    def test_elaborated_observer_source_view_rejects_proof_tampering(self):
        original = (f'import {self.source}\n'
                    'theorem value : True := by trivial\n'
                    'elab "#audit" : command => do\n'
                    f'  let candidate := `{self.source}\n\n#audit\n')
        public = s.rewrite_audit_module_names(original, self.rules())
        public = s.transform(public, s.import_tokens(public), {self.source: self.target})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Audit.lean').write_bytes(public)
            row = {'path': 'Audit.lean', 'source_path': 'Original.lean',
                   'target_sha256': p.sha(public), 'source_sha256': p.sha(original.encode()),
                   'import_map': {self.target: self.source}, 'audit_module_rewrites': self.rules()}
            with patch.object(s, 'ROOT', root):
                self.assertEqual(s.module_views(row, {}), (original.encode(), original.encode()))
                tampered = public.replace(b': True :=', b': False :=')
                (root / 'Audit.lean').write_bytes(tampered)
                with self.assertRaises(s.ViewError):
                    s.module_views({**row, 'target_sha256': p.sha(tampered)}, {})

    def test_full_observer_keeps_proof_and_explicit_boundary_branch(self):
        prefix = 'theorem value : True := by trivial\n\n'
        original = prefix + 'open Lean Elab Command in\nrun_cmd do\n' + self.boundary()
        public = s.rewrite_audit_runtime(original, [self.variable], True)
        self.assertTrue(public.startswith(prefix))
        self.assertIn('| some paidPath => IO.FS.readFile paidPath', public)
        self.assertIn('| none => pure "[]"', public)
        self.assertIn('set_option maxHeartbeats 0 in\nrun_cmd do', public)
        self.assertEqual(s.rewrite_audit_runtime(public, [self.variable], True, reverse=True), original)

    def test_runtime_rewrites_reject_bad_metadata_or_false_matches(self):
        source = 'open Lean Elab Command in\nrun_cmd do\n' + self.boundary()
        for variables in ({}, [[self.variable]], [self.variable, self.variable], ['UNRELATED_NAMES']):
            with self.subTest(variables=variables), self.assertRaises(s.ViewError):
                s.rewrite_audit_runtime(source, variables, True)
        with self.assertRaises(s.ViewError):
            s.rewrite_audit_runtime(source, [self.variable], 'true')
        with self.assertRaises(s.ViewError):
            s.rewrite_audit_runtime(source + self.boundary(), [self.variable], True)
        fake = 'open Lean Elab Command in\nrun_cmd do\n/-\n' + self.boundary() + '-/\n'
        with self.assertRaises(s.ViewError):
            s.rewrite_audit_runtime(fake, [self.variable], True)

    def test_composed_source_view_restores_original_and_rejects_proof_tampering(self):
        original = (f'import {self.source}\n'
                    'theorem value : True := by trivial\n'
                    'open Lean Elab Command in\nrun_cmd do\n'
                    f'  let candidate := `{self.source}\n' + self.boundary())
        public = s.rewrite_audit_module_names(original, self.rules())
        public = s.rewrite_audit_runtime(public, [self.variable], True)
        public = s.transform(public, s.import_tokens(public), {self.source: self.target})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Audit.lean').write_bytes(public)
            row = {'path': 'Audit.lean', 'source_path': 'Original.lean',
                   'target_sha256': p.sha(public), 'source_sha256': p.sha(original.encode()),
                   'import_map': {self.target: self.source}, 'audit_module_rewrites': self.rules(),
                   'audit_boundary_fallbacks': [self.variable], 'audit_full_closure': True}
            with patch.object(s, 'ROOT', root):
                self.assertEqual(s.module_views(row, {}), (original.encode(), original.encode()))
                tampered = public.replace(b': True :=', b': False :=')
                (root / 'Audit.lean').write_bytes(tampered)
                with self.assertRaises(s.ViewError):
                    s.module_views({**row, 'target_sha256': p.sha(tampered)}, {})


class AuditCommandNameTests(unittest.TestCase):
    header = 'elab "#audit" : command => do'

    def rule(self):
        return {'source_declaration': self.header, 'target_name': 'H0mework.Audit.auditCommand'}

    def test_only_executable_registration_name_changes(self):
        prefix = '/-\n' + self.header + '\n-/\n' + 'theorem preserved : True := by trivial\n'
        body = '\n  logInfo "same audit"\n\n#audit\n'
        original = prefix + self.header + body
        public = s.name_audit_command(original, self.rule())
        self.assertTrue(public.startswith(prefix))
        self.assertTrue(public.endswith(body))
        self.assertIn('elab (name := H0mework.Audit.auditCommand) "#audit"', public)
        self.assertIsNotNone(s.audit_observer_start(public))
        self.assertEqual(s.name_audit_command(public, self.rule(), reverse=True), original)

    def test_invalid_or_ambiguous_registration_rejects(self):
        for rule in ({}, {'source_declaration': 'def value := 1', 'target_name': 'Good'},
                     {'source_declaration': self.header, 'target_name': '../Bad'}):
            with self.subTest(rule=rule), self.assertRaises(s.ViewError):
                s.name_audit_command(self.header + '\n', rule)
        for text in ('/-\n' + self.header + '\n-/\n', self.header + '\n' + self.header + '\n'):
            with self.subTest(text=text), self.assertRaises(s.ViewError):
                s.name_audit_command(text, self.rule())

    def test_composed_registration_and_module_names_restore_source(self):
        original = ('import SourceModule\ntheorem preserved : True := by trivial\n' + self.header +
                    '\n  let candidates := #[`SourceModule]\n\n#audit\n')
        rules = [{'source_module': 'SourceModule', 'target_module': 'H0mework.SourceModule'}]
        public = s.rewrite_audit_module_names(original, rules)
        public = s.name_audit_command(public, self.rule())
        public = s.transform(public, s.import_tokens(public), {'SourceModule': 'H0mework.SourceModule'})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Audit.lean').write_bytes(public)
            row = {'path': 'Audit.lean', 'source_path': 'Original.lean',
                   'target_sha256': p.sha(public), 'source_sha256': p.sha(original.encode()),
                   'import_map': {'H0mework.SourceModule': 'SourceModule'},
                   'audit_module_rewrites': rules, 'audit_command_name': self.rule()}
            with patch.object(s, 'ROOT', root):
                self.assertEqual(s.module_views(row, {}), (original.encode(), original.encode()))
                tampered = public.replace(b'"#audit"', b'"#other"')
                (root / 'Audit.lean').write_bytes(tampered)
                with self.assertRaises(s.ViewError):
                    s.module_views({**row, 'target_sha256': p.sha(tampered)}, {})


class LocalInstanceNameTests(unittest.TestCase):
    source = 'local instance : NormedSpace ℝ Coframe'
    name = 'coframeInverseLocalNormedSpace'

    def rules(self):
        return [{'source_declaration': self.source, 'target_name': self.name}]

    def test_only_declared_local_instance_name_changes(self):
        original = (self.source + ' := Matrix.normedSpace\n'
                    'theorem unchanged : True := by trivial\n')
        target = self.source.replace('instance', 'instance ' + self.name, 1)
        public = s.name_local_instances(original, self.rules())
        self.assertEqual(public, original.replace(self.source, target))
        self.assertEqual(s.name_local_instances(public, self.rules(), reverse=True), original)

    def test_comments_strings_and_global_instances_do_not_match(self):
        for source in ('-- ' + self.source + ' := value\n',
                       '/-\n' + self.source + ' := value\n-/\n',
                       'def quoted := "' + self.source + ' := value"\n',
                       self.source.removeprefix('local ') + ' := value\n'):
            with self.subTest(source=source), self.assertRaises(s.ViewError):
                s.name_local_instances(source, self.rules())

    def test_bad_or_ambiguous_rules_reject(self):
        text = self.source + ' := Matrix.normedSpace\n'
        for rules in ({}, [self.rules()[0], self.rules()[0]],
                      [{'source_declaration': self.source, 'target_name': 'name;bad'}],
                      [{'source_declaration': self.source + ' := bad', 'target_name': self.name}]):
            with self.subTest(rules=rules), self.assertRaises(s.ViewError):
                s.name_local_instances(text, rules)
        with self.assertRaises(s.ViewError):
            s.name_local_instances(text + text, self.rules())

    def test_all_local_matrix_instances_roundtrip_together(self):
        declarations = [('NormedAddCommGroup Coframe', 'matrixGroup'),
                        ('SeminormedAddCommGroup Coframe', 'matrixSemigroup'),
                        ('NormedSpace ℝ Coframe', 'matrixSpace')]
        rules = [{'source_declaration': 'local instance : ' + kind, 'target_name': name}
                 for kind, name in declarations]
        original = ''.join(rule['source_declaration'] + ' := originalValue\n' for rule in rules)
        public = s.name_local_instances(original, rules)
        self.assertEqual(s.name_local_instances(public, rules, reverse=True), original)
        self.assertEqual(public.count(':= originalValue'), 3)
        for _, name in declarations:
            self.assertIn('local instance ' + name + ' :', public)

    def test_record_and_multiline_instance_values_are_unchanged(self):
        rules = [{'source_declaration': 'local instance : Module.Finite ℝ Carrier',
                  'target_name': 'moduleFinite'},
                 {'source_declaration': 'local instance : IsTopologicalAddGroup Carrier',
                  'target_name': 'topologicalGroup'}]
        original = ('local instance : Module.Finite ℝ Carrier :=\n'
                    '  originalProof\n'
                    'local instance : IsTopologicalAddGroup Carrier where\n'
                    '  continuous_add := originalAdd\n'
                    '  continuous_neg := originalNeg\n')
        public = s.name_local_instances(original, rules)
        self.assertEqual(s.name_local_instances(public, rules, reverse=True), original)
        self.assertIn('where\n  continuous_add := originalAdd\n  continuous_neg := originalNeg', public)
        self.assertIn(':=\n  originalProof', public)

    def test_source_digest_still_rejects_changed_instance_value(self):
        original = (self.source + ' := Matrix.normedSpace\n').encode()
        public = s.name_local_instances(original.decode(), self.rules()).encode()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Instance.lean').write_bytes(public)
            row = {'path': 'Instance.lean', 'source_path': 'Instance.lean',
                   'target_sha256': p.sha(public), 'source_sha256': p.sha(original),
                   'local_instance_names': self.rules()}
            with patch.object(s, 'ROOT', root):
                self.assertEqual(s.module_views(row, {}), (original, original))
                changed = public.replace(b'Matrix.normedSpace', b'Other.normedSpace')
                (root / 'Instance.lean').write_bytes(changed)
                with self.assertRaises(s.ViewError):
                    s.module_views({**row, 'target_sha256': p.sha(changed)}, {})


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

    def test_shared_layout_restores_full_body_under_both_addresses(self):
        raw = b'import Mathlib\nnamespace Tail\ntheorem same : True := True.intro\nend Tail\n'
        (self.root / 'Tail.lean').write_bytes(raw)
        primary = 'Verification/Tail.lean'
        alternate = 'Lean/scratch/Original/Tail.lean'
        alias = {'source_path': alternate, 'source_sha256': p.sha(raw),
                 'source_revision': 'b' * 40, 'source_revisions': ['b' * 40],
                 'original_module_name': 'Tail'}
        row = {'source': 'file:' + primary, 'source_path': primary,
               'source_revision': 'a' * 40, 'source_revisions': ['a' * 40],
               'path': 'Tail.lean', 'target': 'H0mework.Tail',
               'source_sha256': p.sha(raw), 'target_sha256': p.sha(raw), 'source_aliases': [alias]}
        data = json.loads(self.map.read_text())
        data['modules'] = [row]
        self.map.write_text(json.dumps(data))
        restored, skipped = s.reconstruct(paths=[primary, alternate], exact=True)
        self.assertEqual(restored, {primary: raw, alternate: raw})
        self.assertEqual(skipped, [])
        self.assertEqual(s.reconstruct(paths=[alternate], at='b' * 40)[0], {alternate: raw})
        self.assertEqual(s.verify_all()['modules'], 2)
        alias['source_sha256'] = 'f' * 64
        self.map.write_text(json.dumps(data))
        with self.assertRaisesRegex(s.ViewError, 'Invalid shared'):
            s.reconstruct(paths=[alternate])

    def test_layout_cannot_redirect_the_public_body_owner(self):
        row = {'source_path': 'Verification/Tail.lean', 'source_sha256': 'a' * 64,
               'source_aliases': [{'source_path': 'Lean/scratch/Tail.lean',
                                  'source_sha256': 'a' * 64, 'source_revision': 'b' * 40,
                                  'source_revisions': ['b' * 40], 'original_module_name': 'Tail',
                                  'target': 'H0mework.Wrong'}]}
        with self.assertRaisesRegex(s.ViewError, 'Invalid shared'):
            s.source_record(row, 'Lean/scratch/Tail.lean')

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

    def test_private_owner_recovery_precedes_imports_resources_and_exact_digest(self):
        source_owner, target_owner = "_private.Engine", "_private.H0mework.Versions.AB.Engine"
        original = (b'import Engine\nimport Mathlib\n'
                    b'def owner := Name.num `_private.Engine 0\n'
                    b'def packetText := include_str "source/receipt.json"\n'
                    b'def packetSha256 := "' + p.sha(self.original).encode() + b'"\n')
        public_view = original.replace(p.sha(self.original).encode(), p.sha(self.public).encode())
        exported = (public_view.replace(b'import Engine\n', b'import H0mework.Versions.AB.Engine\n')
                    .replace(source_owner.encode(), target_owner.encode())
                    .replace(b'"source/receipt.json"', b'"receipt.json"'))
        (self.root / "Consumer.lean").write_bytes(exported)
        row = {"source": "Consumer", "source_path": "Lean/Consumer.lean",
               "source_revision": "a" * 40, "target": "H0mework.Versions.AB.Consumer",
               "path": "Consumer.lean", "source_sha256": p.sha(original),
               "target_sha256": p.sha(exported), "view_sha256": p.sha(public_view),
               "import_map": {"H0mework.Versions.AB.Engine": "Engine"},
               "private_name_rewrites": [{"source_name": source_owner, "target_name": target_owner}],
               "resource_rewrites": [{"source_address": "source/receipt.json",
                                      "target_address": "receipt.json"}],
               "resource_sha256_rewrites": [{"source": p.sha(self.original), "target": p.sha(self.public)}]}
        self.assertEqual(s.module_views(row, {}), (public_view, original))
        with self.assertRaisesRegex(s.ViewError, "Reconstructed source digest differs"):
            s.module_views({**row, "private_name_rewrites": []}, {})
        changed = exported.replace(b"Name.num `" + target_owner.encode() + b" 0",
                                   b"Name.num `" + target_owner.encode() + b" 1")
        (self.root / "Consumer.lean").write_bytes(changed)
        with self.assertRaisesRegex(s.ViewError, "Reconstructed source digest differs"):
            s.module_views({**row, "target_sha256": p.sha(changed)}, {})


if __name__ == "__main__":
    unittest.main()
