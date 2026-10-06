"""Focused controls for previously erased public history coordinates."""
import unittest
import hashlib
import tempfile
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch
from zipfile import ZipFile

import history_feed as primary
import history_feed_independent as independent


def raw_rows(*rows, role="local1"):
    return primary.schema.HEADERS[role] + b"".join((";".join(row) + "\n").encode("utf-8") for row in rows)


class HistoryFeedTests(unittest.TestCase):
    rows = (("123", "0", "1", "427", "0", "no", " "),
            ("124", "1", "0", "439", "1", "yes", "Maintenance"))

    def test_full_fields_recover_and_independent_observer_agrees(self):
        raw = raw_rows(*self.rows)
        history = primary.observe_bytes(raw, "synthetic", "local1", (1,))
        self.assertEqual(history.observations, independent.observe_bytes(raw, "synthetic", "local1"))
        self.assertEqual(history.recover(2).local_timestamp, "439")
        self.assertEqual(history.recover(2).comment, "Maintenance")
        self.assertEqual(history.summary()["unpaired_records"], 1)
        self.assertTrue(history.summary()["every_record_recovered"])

    def test_selected_model_view_does_not_exhaust_available_history(self):
        left = primary.observe_bytes(raw_rows(*self.rows), "synthetic", "local1", (1,))
        for column, changed in ((0, "999"), (3, "440"), (5, "no"), (6, "CEMs off")):
            with self.subTest(column=column):
                rows = [list(row) for row in self.rows]
                rows[1][column] = changed
                right = primary.observe_bytes(raw_rows(*rows), "synthetic", "local1", (1,))
                self.assertEqual(left.selected_model_view(), right.selected_model_view())
                self.assertNotEqual(left.observations, right.observations)
                self.assertNotEqual(left.summary()["observation_sequence_sha256"],
                                    right.summary()["observation_sequence_sha256"])

    def test_selected_row_timestamp_still_visible(self):
        left = primary.observe_bytes(raw_rows(*self.rows), "synthetic", "local1", (1,))
        rows = [list(row) for row in self.rows]
        rows[0][3] = "428"
        right = primary.observe_bytes(raw_rows(*rows), "synthetic", "local1", (1,))
        self.assertEqual(left.selected_model_view(), right.selected_model_view())
        self.assertNotEqual(left.observations, right.observations)

    def test_prefix_and_selection_override_preserve_all_source_rows(self):
        history = primary.observe_bytes(raw_rows(*self.rows), "synthetic", "local1", (1,))
        overridden = replace(history, paired_rows=frozenset((2,)))
        self.assertEqual(overridden.observations, history.observations)
        self.assertNotEqual(overridden.selected_model_view(), history.selected_model_view())
        self.assertEqual(history.prefix(1), history.prefix(2)[:1])
        self.assertEqual(history.prefix(0), ())

    def test_lab2_optional_empty_column_preserves_meaning(self):
        raw = raw_rows(("123", "0", "1", "427", "no", "CEMs off"), role="local2")
        history = primary.observe_bytes(raw, "synthetic", "local2")
        self.assertIsNone(history.recover(1).herald)
        self.assertEqual(history.observations, independent.observe_bytes(raw, "synthetic", "local2"))

    def test_lookalike_partial_record_and_bad_row_fail(self):
        history = primary.observe_bytes(raw_rows(*self.rows), "synthetic", "local1")
        for observations in ((history.observations[0][:-1],), tuple(reversed(history.observations))):
            with self.assertRaises(ValueError):
                replace(history, observations=observations)
        for count in (-1, 3, True):
            with self.assertRaises(ValueError):
                history.prefix(count)
        with self.assertRaises(ValueError):
            replace(history, paired_rows=frozenset((3,)))
        with self.assertRaises(ValueError):
            primary.expand_ranges(((2, 3), (3, 4)))

    def test_archive_override_source_binding_and_no_pair_access(self):
        payloads = {"left.csv": raw_rows(*self.rows),
                    "right.csv": raw_rows(("123", "0", "1", "427", "no", " "), role="local2"),
                    "pair.csv": b"not a readable pair file", "Readme.txt": b"test"}
        with tempfile.TemporaryDirectory() as directory:
            archive_path = Path(directory) / "test.zip"
            with ZipFile(archive_path, "w") as archive:
                for name, raw in payloads.items():
                    archive.writestr(name, raw)
            raw = archive_path.read_bytes()
            spec = primary.schema.ArchiveSpec("synthetic", "test.zip", len(raw),
                                             hashlib.md5(raw).hexdigest(), primary.schema.sha256(raw),
                                             "left.csv", "right.csv", "pair.csv")
            access, local = [], {}
            for role, member in (("local1", "left.csv"), ("local2", "right.csv")):
                rows = primary.schema.parse_local(payloads[member], role, "synthetic")
                local[role] = primary.schema.local_audit(rows, {1})
                access.append({"run": "synthetic", "role": role,
                               "payload_sha256": primary.schema.sha256(payloads[member])})
            paid = {"admission": "admitted", "record_access": {"members": access}, "runs": [
                {"run": "synthetic", "local_audit": {"admissible_row_offset_pairs": [[1, 1]],
                 "join_candidates": [local]}}]}
            identity = {name: getattr(spec, name) for name in ("run", "name", "bytes", "sha256", "md5", "members")}
            with patch.object(primary.schema, "ARCHIVES", (spec,)), \
                 patch.object(independent.parser, "ARCHIVE_IDENTITIES", (identity,)):
                histories = primary.load_histories(directory, paid)
                self.assertEqual(tuple(history.summary() for history in histories),
                                 independent.load_summaries(directory, paid))
                access[0]["payload_sha256"] = "0" * 64
                with self.assertRaises(ValueError):
                    primary.load_histories(directory, paid)
                with self.assertRaises(ValueError):
                    independent.load_summaries(directory, paid)

    def test_wrong_loaded_parser_owner_is_rejected(self):
        raw = raw_rows(*self.rows)
        with patch.object(primary.schema, "__file__", "/tmp/lookalike-schema.py"):
            with self.assertRaises(ValueError):
                primary.observe_bytes(raw, "synthetic", "local1")
        with patch.object(independent.parser, "__file__", "/tmp/lookalike-parser.py"):
            with self.assertRaises(ValueError):
                independent.observe_bytes(raw, "synthetic", "local1")


if __name__ == "__main__":
    unittest.main()
