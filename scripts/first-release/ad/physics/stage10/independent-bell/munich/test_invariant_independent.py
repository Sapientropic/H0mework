"""Synthetic controls for the independent parser and exact invariant scorer."""

import hashlib
import json
import unittest
from fractions import Fraction
from itertools import product

import invariant_independent as independent


def local_bytes(kind, rows):
    return independent.RAW_HEADERS[kind] + b"".join((";".join(row) + "\n").encode("utf-8") for row in rows)


def pair_bytes(rows):
    return independent.RAW_HEADERS["pairs"] + b"".join(("\t".join(row) + "\n").encode("utf-8") for row in rows)


def fixture(n=8, excluded=False):
    left, right, pairs = [], [], []
    for index in range(n):
        bit = str(index % 2)
        row, time = str(index + 1), str(1000 + index)
        left.append([time, bit, bit, "stamp" + row, bit, "0", ""])
        right.append([time, bit, bit, "stamp" + row, "0", "", ""])
        pairs.append([time, bit, bit, bit, bit, bit, row, row])
    if excluded:
        left.append(["2000", "", "", "", "", "1", "laser maintenance"])
        right.append(["2000", "", "", "", "1", "CEM failure", ""])
    return left, right, pairs


def admitted(rows):
    trials = tuple(independent.Trial(index, index, h, a, b, x, y, index, index)
                   for index, (h, a, b, x, y) in enumerate(rows, 1))
    return independent.AdmittedRun(independent.RUNS[0], trials, {}, {})


class ExactScorerControls(unittest.TestCase):
    def test_single_context_closed_form_and_crossing(self):
        source = admitted([(0, 0, 0, 0, 0)] * 16)
        report = independent.score_run(source)
        exact = Fraction(1)
        maximum, first = Fraction(1), None
        sequence = hashlib.sha256()
        for index in range(16):
            exact *= Fraction(2 * index + 1, index + 1)
            sequence.update(independent.rational_bytes(exact))
            maximum = max(maximum, exact)
            if first is None and exact >= 40:
                first = index + 1
        self.assertEqual(report["terminal_e"], independent.exact_summary(exact))
        self.assertEqual(report["max_e"], independent.exact_summary(maximum))
        self.assertEqual(report["prefix_e_sha256"], sequence.hexdigest())
        self.assertEqual(report["first_crossing"], first)
        self.assertEqual(report["status"], "rejected")
        self.assertEqual(report["trials"], 16)

    def test_balanced_complement_control(self):
        rows = [(0, 0, 0, bit, bit) for bit in (0, 1) * 100]
        result = independent.score_run(admitted(rows))
        self.assertEqual(result["status"], "not_rejected")
        self.assertIsNone(result["first_crossing"])
        self.assertEqual(result["contexts"][0]["counts"], [100, 100])
        self.assertEqual(result["four_outcomes"][0]["counts"], [100, 0, 0, 100])

    def test_fixed_arithmetic_mixture_keeps_pooled_bias_power(self):
        rows = [(i % 2, (i // 2) % 2, (i // 4) % 2, 0, i % 2) for i in range(32)]
        result = independent.score_run(admitted(rows))
        joint_counts = {tuple(row[name] for name in ("h", "a", "b", "c")): row["counts"]
                        for row in result["contexts"]}
        components = {"joint": independent.terminal_closed_form(joint_counts),
                      "alice": independent.binary_weight([32, 0]), "bob": independent.binary_weight([16, 16])}
        self.assertEqual(result["components"], {key: independent.exact_summary(value)
                                                for key, value in components.items()})
        self.assertEqual(result["terminal_e"], independent.exact_summary(sum(components.values()) / 3))
        self.assertNotEqual(sum(components.values()) / 3, components["joint"] * components["alice"] * components["bob"])
        self.assertEqual(result["status"], "rejected")

    def test_all_32_global_label_maps_preserve_every_prefix(self):
        rows = [(i % 2, (i // 2) % 2, (i // 4) % 2,
                 (i // 8) % 2, (i // 3) % 2) for i in range(320)]
        expected = independent.score_run(admitted(rows))
        for flips in product((0, 1), repeat=5):
            changed = independent.score_run(admitted([tuple(bit ^ flip for bit, flip in zip(row, flips))
                                                     for row in rows]))
            for key in ("terminal_e", "max_e", "max_prefix", "first_crossing", "first_crossing_e", "prefix_e_sha256", "status"):
                self.assertEqual(changed[key], expected[key], (flips, key))

    def test_empty_run_has_no_model_pass(self):
        result = independent.score_run(admitted([]))
        self.assertEqual(result["status"], "inconclusive")
        self.assertEqual(result["terminal_e"], independent.exact_summary(1))
        self.assertEqual(result["max_prefix"], 0)

    def test_bool_and_third_outcome_rejected(self):
        for wrong in (True, 2, -1):
            bad = independent.AdmittedRun(independent.RUNS[0],
                                          (independent.Trial(1, 1, 0, 0, 0, wrong, 0, 1, 1),), {}, {})
            with self.assertRaises(independent.AdmissionError):
                independent.score_run(bad)

    def test_exact_summary_encloses_tiny_huge_and_nondyadic_values(self):
        for exact in (Fraction(1), Fraction(40), Fraction(1, 3), Fraction(1, 2 ** 5000), Fraction(2 ** 5000, 3)):
            summary = independent.exact_summary(exact)
            dyadic = summary["dyadic"]
            unit = Fraction(2 ** dyadic["exponent"]) if dyadic["exponent"] >= 0 else Fraction(1, 2 ** -dyadic["exponent"])
            self.assertLessEqual(int(dyadic["lower_mantissa"]) * unit, exact)
            self.assertGreaterEqual(int(dyadic["upper_mantissa"]) * unit, exact)
            self.assertEqual(summary["numerator_sha256"], independent.digest(independent.unsigned_bytes(exact.numerator)))


class IndependentParserControls(unittest.TestCase):
    def parse(self, rows):
        left, right, pairs = rows
        return independent.admit_run_bytes(independent.RUNS[0], local_bytes("local1", left),
                                           local_bytes("local2", right), pair_bytes(pairs))

    def assert_rejected(self, rows, code):
        with self.assertRaises(independent.AdmissionError) as error:
            self.parse(rows)
        self.assertEqual(error.exception.detail["code"], code)

    def test_original_row_join_and_unpaired_raw_audit(self):
        result = self.parse(fixture(excluded=True))
        self.assertEqual(len(result.trials), 8)
        self.assertEqual(result.audit["admissible_row_offset_pairs"], [[0, 0]])
        joined = result.audit["join_candidates"][0]
        self.assertEqual(joined["local1"]["unpaired_original_rows_rle"], [[9, 9]])
        self.assertTrue(any(group["comment_sha256"] == independent.digest(b"CEM failure")
                            and group["records"] == 1 for group in joined["local2"]["comment_groups"]))
        self.assertEqual(result.audit["record_lines_decoded"], 26)

    def test_single_observed_token_and_empty_pairs_are_admitted(self):
        left, right, pairs = fixture(1)
        result = self.parse((left, right, []))
        self.assertEqual(result.token_dictionaries["x"], [])
        self.assertEqual(result.audit["admissible_row_offset_pairs"], [[0, 0], [0, 1], [1, 0], [1, 1]])
        self.assertEqual(independent.score_run(result)["status"], "inconclusive")

    def test_unknown_and_empty_uniform_raw_flags_have_no_invented_meaning(self):
        for flag in ("", "true", "2", " 0"):
            left, right, pairs = fixture()
            for row in left:
                row[5] = flag
            result = self.parse((left, right, pairs))
            self.assertEqual(result.audit["join_candidates"][0]["valid_pair_flags"]["lab1"], flag)

    def test_heterogeneous_valid_pair_flags_fail(self):
        left, right, pairs = fixture()
        left[0][5] = "different"
        self.assert_rejected((left, right, pairs), "no_admissible_row_offset")

    def test_duplicate_and_out_of_range_original_references_fail(self):
        left, right, pairs = fixture()
        pairs[1] = list(pairs[0])
        self.assert_rejected((left, right, pairs), "no_admissible_row_offset")
        pairs[1][6] = "999"
        self.assert_rejected((left, right, pairs), "no_admissible_row_offset")

    def test_zero_and_mixed_side_row_origins_are_paid_by_whole_file_join(self):
        left, right, pairs = fixture()
        for pair in pairs:
            pair[6] = str(int(pair[6]) - 1)
        result = self.parse((left, right, pairs))
        self.assertEqual(result.audit["admissible_row_offset_pairs"], [[1, 0]])
        self.assertEqual(len(result.trials), 8)

    def test_timestamp_window_and_raw_model_copy_fail(self):
        left, right, pairs = fixture()
        right[0][0] = "1101"
        self.assert_rejected((left, right, pairs), "no_admissible_row_offset")
        right[0][0] = "1000"
        pairs[0][3] = "1"
        self.assert_rejected((left, right, pairs), "no_admissible_row_offset")

    def test_fractional_milliseconds_and_scientific_time_have_exact_identity(self):
        left, right, pairs = fixture()
        left[0][0], right[0][0], pairs[0][0] = "1000.5", "1100.5", "1.0005e3"
        result = self.parse((left, right, pairs))
        self.assertEqual(result.trials[0].time_ms, Fraction(2001, 2))
        right[0][0] = "1100.5000000000000000001"
        self.assert_rejected((left, right, pairs), "no_admissible_row_offset")
        for bad in ("NaN", "Infinity", "-0.5"):
            with self.assertRaises(independent.AdmissionError):
                independent.timestamp(bad)

    def test_third_empty_and_nonascii_labels_fail(self):
        for bad in ("零", " 0", ""):
            left, right, pairs = fixture()
            left[0][2] = bad
            pairs[0][3] = bad
            self.assert_rejected((left, right, pairs), "missing_or_noncanonical_token")
        left, right, pairs = fixture()
        left.append(["2000", "0", "2", "newstamp", "0", "0", ""])
        unpaired = self.parse((left, right, pairs))
        self.assertNotIn("2", unpaired.token_dictionaries["x"])
        right.append(["2000", "0", "0", "newstamp", "0", "", ""])
        pairs.append(["2000", "0", "0", "2", "0", "0", "9", "9"])
        self.assert_rejected((left, right, pairs), "nonbinary_role")

    def test_opaque_none_and_click_tokens_are_legitimate_binary_labels(self):
        left, right, pairs = fixture()
        for row in left:
            row[2] = "none" if row[2] == "0" else "click"
        for row in right:
            row[2] = "none" if row[2] == "0" else "click"
        for pair in pairs:
            pair[3] = "none" if pair[3] == "0" else "click"
            pair[5] = "none" if pair[5] == "0" else "click"
        parsed = self.parse((left, right, pairs))
        self.assertEqual(parsed.token_dictionaries["x"], ["click", "none"])
        self.assertEqual(len(parsed.trials), 8)

    def test_unpaired_missing_model_time_and_flag_are_audited_without_clipping(self):
        left, right, pairs = fixture()
        left.append(["", "", "", "", "", "", ""])
        right.append(["broken", "three", "unmodeled", "", "?", "note", ""])
        result = self.parse((left, right, pairs))
        self.assertEqual(len(result.trials), 8)
        self.assertEqual(result.audit["join_candidates"][0]["local1"]["unpaired_original_rows_rle"], [[9, 9]])

    def test_empty_physical_line_and_extra_trailing_column_fail(self):
        left, right, pairs = fixture()
        raw = local_bytes("local1", left)
        changed = raw.replace(b"\n", b"\n\n", 1)
        with self.assertRaises(independent.AdmissionError):
            independent.admit_run_bytes(independent.RUNS[0], changed,
                                         local_bytes("local2", right), pair_bytes(pairs))
        right[0][-1] = "foreign"
        self.assert_rejected((left, right, pairs), "lab2_trailing_column")

    def test_six_semantic_fields_and_seventh_empty_have_identical_scores(self):
        left, right, pairs = fixture()
        seven = self.parse((left, right, pairs))
        six = self.parse((left, [row[:-1] for row in right], pairs))
        expected, actual = independent.score_run(seven), independent.score_run(six)
        for key in ("trials", "contexts", "four_outcomes", "components", "pooled_counts", "terminal_e",
                    "max_e", "max_prefix", "first_crossing", "first_crossing_e", "prefix_e_sha256", "status"):
            self.assertEqual(expected[key], actual[key], key)
        self.assertNotEqual(seven.audit["local2_original_bytes_sha256"], six.audit["local2_original_bytes_sha256"])
        self.assertEqual(seven.audit["record_lines_decoded"], six.audit["record_lines_decoded"])

    def test_only_lab2_nonsemantic_tail_is_optional(self):
        left, right, pairs = fixture()
        with self.assertRaises(independent.AdmissionError):
            self.parse(([row[:-1] for row in left], right, pairs))
        with self.assertRaises(independent.AdmissionError):
            self.parse((left, [row[:-2] for row in right], pairs))
        with self.assertRaises(independent.AdmissionError):
            self.parse((left, [row + [""] for row in right], pairs))

    def test_original_byte_override_and_foreign_archive_fail(self):
        with self.assertRaises(independent.AdmissionError) as error:
            independent.archive_run(b"look-alike", independent.ARCHIVE_IDENTITIES[0])
        self.assertEqual(error.exception.detail["code"], "archive_bytes_mismatch")

    def test_source_bindings_require_complete_two_run_inventory(self):
        original = (independent.BASE / "sources.json").read_bytes()
        document = json.loads(original)
        result = independent.method_bindings(original, document)
        self.assertEqual(len(result["archive_bindings"]), 2)
        document["archives"].pop()
        with self.assertRaises(independent.AdmissionError):
            independent.method_bindings(original, document)

    def test_duplicate_source_key_fails_before_archive_decode(self):
        with self.assertRaises(independent.AdmissionError):
            independent.source_document(b'{"schema":"a","schema":"b"}')

    def test_criterion_and_program_are_the_same_frozen_contract(self):
        raw = (independent.BASE / "criterion-mu0001.1.md").read_bytes()
        self.assertEqual(independent.criterion_contract(raw), independent.EXPECTED_CRITERION)
        changed = raw.replace(b'"per_run_threshold": "40"', b'"per_run_threshold": "400"')
        with self.assertRaises(independent.AdmissionError):
            independent.criterion_contract(changed)

    def test_theory_hash_or_identity_substitution_fails(self):
        original = (independent.BASE / "sources.json").read_bytes()
        document = json.loads(original)
        document["theory_authority"]["root_visit"] = 11
        with self.assertRaises(independent.AdmissionError):
            independent.method_bindings(original, document)
        document = json.loads(original)
        document["theory_authority"]["bindings"][0]["sha256"] = "0" * 64
        with self.assertRaises(independent.AdmissionError):
            independent.method_bindings(original, document)

    def test_scorer_does_not_import_primary_program(self):
        source = (independent.BASE / "invariant_independent.py").read_text()
        self.assertNotIn("import schema", source)
        self.assertNotIn("import invariant_primary", source)
        self.assertNotIn("primary-first.json", source)


if __name__ == "__main__":
    unittest.main()
