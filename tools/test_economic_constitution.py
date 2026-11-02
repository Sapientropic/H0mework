import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import economic_constitution as economic
import edition_release


class EconomicContractTests(unittest.TestCase):
    def claims(self):
        return [{"id": name, "paper": "economic-constitution", "producers": [{}],
                 "direct_consumers": [{}]} for name in sorted(economic.CLAIMS)]

    def document(self, claims):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            (root / "docs").mkdir()
            (root / economic.MAP).write_text(json.dumps({"schema": economic.SCHEMA, "claims": claims}))
            return economic.document(root)

    def test_complete_contract_and_explicit_selection(self):
        claims = self.claims()
        self.assertEqual(len(self.document(claims)["claims"]), 8)
        selected = [{**claim, "selection_status": "selected"} for claim in claims]
        self.assertEqual(len(self.document(selected)["claims"]), 8)

    def test_missing_duplicate_lookalike_and_unsupported_consumer_are_rejected(self):
        claims = self.claims()
        for changed in (claims[:-1], [*claims, copy.deepcopy(claims[0])],
                        [{**claims[0], "id": "ECN01"}, *claims[1:]],
                        [{**claims[0], "selected": False}, *claims[1:]],
                        [{**claims[0], "producers": []}, *claims[1:]],
                        [{**claims[0], "direct_consumers": []}, *claims[1:]]):
            with self.assertRaises(economic.release.ReleaseError):
                self.document(changed)

    def test_edition_registration_retains_all_original_defaults(self):
        self.assertEqual(edition_release.EDITIONS["economic-constitution"], (economic.MAP, economic.SCHEMA))
        self.assertEqual(edition_release.EDITIONS["generated-society"][0], "docs/generated-society-map.json")
        self.assertEqual(edition_release.EDITIONS["whole-ledger"][0], "docs/whole-ledger-map.json")
        self.assertEqual(economic.release.MAP, "docs/first-release-map.json")


class EconomicRecoveryTests(unittest.TestCase):
    def original_bindings(self):
        ledger = {"sources": {"Lean/Producer.lean": "a" * 64, "Lean/Actual.lean": "b" * 64},
                  "evidence": {"original-run.json": "c" * 64}}
        state = {"modules": {"Lean/Producer.lean": {"source_sha256": "a" * 64}},
                 "artifacts": {"Lean/Actual.lean": {"source_sha256": "b" * 64},
                               economic.ORIGINAL_EVIDENCE + "original-run.json": {"source_sha256": "c" * 64}}}
        return ledger, state

    def test_original_proofs_and_unexecuted_actual_program_share_exact_ledger_bindings(self):
        ledger, state = self.original_bindings()
        before = copy.deepcopy((ledger, state))
        self.assertEqual(economic.original_bindings(ledger, state),
                         {"original_sources": 2, "original_receipts": 1})
        self.assertEqual((ledger, state), before)

    def test_missing_or_replaced_original_program_and_receipt_are_rejected(self):
        for collection, path in [("modules", "Lean/Producer.lean"), ("artifacts", "Lean/Actual.lean"),
                                 ("artifacts", economic.ORIGINAL_EVIDENCE + "original-run.json")]:
            for remove in (False, True):
                ledger, state = self.original_bindings()
                if remove:
                    state[collection].pop(path)
                else:
                    state[collection][path]["source_sha256"] = "d" * 64
                with self.subTest(path=path, remove=remove), self.assertRaises(economic.release.ReleaseError):
                    economic.original_bindings(ledger, state)

    def test_recovery_selects_this_source_list_and_restores_on_failure(self):
        previous = economic.finite.SELECTION

        def inspect(root, **kwargs):
            self.assertEqual(economic.finite.SELECTION, economic.SELECTION)
            self.assertEqual(kwargs, {"exact": True, "private_originals": "originals"})
            raise economic.source_view.ViewError("incomplete original resource")

        with patch.object(economic.finite, "selected_views", side_effect=inspect):
            with self.assertRaises(economic.source_view.ViewError):
                economic.selected_views(Path("."), exact=True, private_originals="originals")
        self.assertEqual(economic.finite.SELECTION, previous)

    def test_public_source_records_its_own_schema_and_bytes(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / ".gitignore").write_text(".local/\n")
            (root / "checks").mkdir()
            selection = b'{"selection":"economic"}\n'
            (root / economic.SELECTION).write_bytes(selection)
            epoch = "1" * 40
            epochs = {epoch: {"modules": {"Lean/A.lean": {}}, "artifacts": {},
                              "outputs": {"Lean/A.lean": b"def value := 1\n"}}}
            with patch.object(economic, "selected_views", return_value=({}, {}, epochs)):
                result = economic.source(".local/source", root=root)
            self.assertEqual(result["schema"], "h0mework/economic-constitution-source-view@1")
            self.assertEqual(result["selection_sha256"], economic.release.sha(selection))
            self.assertEqual((root / ".local/source" / epoch / "Lean/A.lean").read_bytes(), b"def value := 1\n")

    def test_type_runner_uses_economic_map_and_restores_original_state(self):
        previous = economic.whole_ledger.MAP, economic.whole_ledger.SCHEMA

        def inspect(output, ids):
            self.assertEqual((economic.whole_ledger.MAP, economic.whole_ledger.SCHEMA),
                             (economic.MAP, economic.SCHEMA))
            self.assertEqual(ids, ["p"])
            return {"status": "passed"}

        with patch.object(economic.whole_ledger, "types", side_effect=inspect):
            self.assertEqual(economic.types(".local/types", ["p"])["status"], "passed")
        self.assertEqual((economic.whole_ledger.MAP, economic.whole_ledger.SCHEMA), previous)


if __name__ == "__main__":
    unittest.main()
