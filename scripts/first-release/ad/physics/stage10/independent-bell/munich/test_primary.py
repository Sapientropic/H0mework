"""Synthetic admission, exact arithmetic, and fixed-label invariance controls."""
import hashlib
import itertools
import math
import subprocess
import tempfile
import unittest
from dataclasses import replace
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

import primary
from primary import Predictor, adjudicate, exact_prefixes, exact_summary, exclusive_json, fraction_encoding, score_run
from schema import HEADERS, RUNS, AdmissionError, admit_run_bytes


def balanced_patterns(repetitions=3):
    patterns = []
    for _ in range(repetitions):
        for h, a, b, c in itertools.product(range(2), repeat=4):
            for x in (0, 1):
                patterns.append((h, a, b, x, x ^ c))
    return patterns


def fixture(patterns, *, offsets=(0, 0), flags=("", ""), extra_unpaired=False):
    local1, local2, pairs = bytearray(HEADERS["local1"]), bytearray(HEADERS["local2"]), bytearray(HEADERS["pairs"])
    for row, (h, a, b, x, y) in enumerate(patterns, 1):
        stamp = 1460000000000 + row * 1000
        local1.extend(f"{stamp};{a};{x};clock-{row};{h};{flags[0]};\n".encode("ascii"))
        local2.extend(f"{stamp+17};{b};{y};clock-{row};{flags[1]};;\n".encode("ascii"))
        pairs.extend(f"{stamp}\t{h}\t{a}\t{x}\t{b}\t{y}\t{row-offsets[0]}\t{row-offsets[1]}\n".encode("ascii"))
    if extra_unpaired:
        local1.extend(b"broken-time;;;;;maintenance;laser maintenance\n")
        local2.extend(b";;;;CEM-fault;CEM maintenance;\n")
    return {"local1": bytes(local1), "local2": bytes(local2), "pairs": bytes(pairs)}


def change(data, role, row, column, value):
    answer = dict(data)
    lines = answer[role].splitlines(keepends=True)
    delimiter = "\t" if role == "pairs" else ";"
    fields = lines[row].decode("ascii").rstrip("\n").split(delimiter)
    fields[column] = value
    lines[row] = (delimiter.join(fields) + "\n").encode("ascii")
    answer[role] = b"".join(lines)
    return answer


def admit(data, run=RUNS[0]):
    return admit_run_bytes(run, data["local1"], data["local2"], data["pairs"])


def closed_bernoulli(counts):
    total = sum(counts)
    odd_products = [math.prod(range(1, 2 * count, 2)) for count in counts]
    return Fraction(math.prod(odd_products), math.factorial(total))


class PrimaryTests(unittest.TestCase):
    def assertAdmissionFailure(self, data, expected_code):
        with self.assertRaises(AdmissionError) as caught:
            admit(data)
        self.assertEqual(caught.exception.detail["code"], expected_code)

    def test_balanced_positive_and_full_accounting(self):
        data = fixture(balanced_patterns(), extra_unpaired=True)
        first, second = admit(data), admit(data, RUNS[1])
        result = adjudicate({RUNS[0]: first, RUNS[1]: second})
        self.assertEqual(result["scientific_verdict"], "not_rejected")
        self.assertEqual(result["pair_records_scored"], 2 * len(first.trials))
        for run in result["runs"]:
            self.assertEqual(len(run["contexts"]), 16)
            self.assertEqual(len(run["four_outcomes"]), 8)
            self.assertEqual(sum(sum(row["counts"]) for row in run["contexts"]), run["trials"])
            self.assertEqual(sum(sum(row["counts"]) for row in run["four_outcomes"]), run["trials"])
            candidate = run["local_audit"]["join_candidates"][0]
            self.assertEqual(candidate["valid_pair_flags"], {"lab1": "", "lab2": ""})
            self.assertEqual(candidate["local1"]["unpaired_records"], 1)
            self.assertEqual(candidate["local2"]["unpaired_records"], 1)

    def test_source_like_biased_data_rejected_and_all_records_scored(self):
        data = fixture([(0, 0, 0, 0, 0)] * 40)
        run = score_run(admit(data))
        self.assertEqual(run["status"], "rejected")
        self.assertLess(run["first_crossing"], run["trials"])
        self.assertEqual(run["trials"], 40)
        self.assertTrue(run["all_pair_records_scored"])
        self.assertEqual(run["pooled_counts"], {"alice": [40, 0], "bob": [40, 0]})

    def test_pooled_power_catches_spread_context_bias(self):
        patterns = [(h, a, b, 0, c) for _ in range(4) for h, a, b, c in itertools.product(range(2), repeat=4)]
        admitted = admit(fixture(patterns))
        predictor = Predictor()
        for trial in admitted.trials:
            predictor.step(trial)
        self.assertGreater(predictor.alice_e, 40)
        self.assertGreater(predictor.evalue, 40)
        self.assertEqual(predictor.evalue, (predictor.joint_e + predictor.alice_e + predictor.bob_e) / 3)

    def test_all_32_global_flips_preserve_every_mixture_prefix(self):
        patterns = balanced_patterns() + [(0, 1, 0, 0, 0)] * 12
        admitted = admit(fixture(patterns))
        expected_prefixes = tuple(exact_prefixes(admitted.trials))
        expected_run = score_run(admitted)
        for fh, fa, fb, fx, fy in itertools.product(range(2), repeat=5):
            transformed = [(h ^ fh, a ^ fa, b ^ fb, x ^ fx, y ^ fy) for h, a, b, x, y in patterns]
            candidate = admit(fixture(transformed))
            self.assertEqual(tuple(exact_prefixes(candidate.trials)), expected_prefixes)
            scored = score_run(candidate)
            for field in ("terminal_e", "max_e", "max_prefix", "first_crossing", "prefix_e_sha256", "status"):
                self.assertEqual(scored[field], expected_run[field])

    def test_exact_recurrence_and_closed_form(self):
        admitted = admit(fixture(balanced_patterns() + [(1, 0, 1, 0, 1)] * 9))
        predictor = Predictor()
        for trial in admitted.trials:
            predictor.step(trial)
        joint = math.prod(closed_bernoulli(counts) for counts in predictor.counts.values())
        alice, bob = closed_bernoulli(predictor.pooled_a), closed_bernoulli(predictor.pooled_b)
        self.assertEqual(predictor.joint_e, joint)
        self.assertEqual(predictor.evalue, (joint + alice + bob) / 3)
        unary = admit(fixture([(0, 0, 0, 0, 0)] * 3))
        self.assertEqual(tuple(exact_prefixes(unary.trials)), (Fraction(1), Fraction(3, 2), Fraction(5, 2)))

    def test_exact_encoding_and_dyadic_envelope(self):
        self.assertEqual(fraction_encoding(Fraction(3, 2)), b"\0" * 7 + b"\1\3" + b"\0" * 7 + b"\1\2")
        for value in (Fraction(1), Fraction(40), Fraction(1, 3), Fraction(2**1000 + 1, 3**801)):
            summary = exact_summary(value)
            bound = summary["dyadic"]
            scale = Fraction(2**bound["exponent"]) if bound["exponent"] >= 0 else Fraction(1, 2**-bound["exponent"])
            self.assertLessEqual(bound["lower_mantissa"] * scale, value)
            self.assertLessEqual(value, bound["upper_mantissa"] * scale)
            self.assertLessEqual(bound["upper_mantissa"] - bound["lower_mantissa"], 1)
            self.assertEqual(summary["numerator_bits"], value.numerator.bit_length())

    def test_empty_pairs_and_single_label_are_not_format_failures(self):
        self.assertEqual(score_run(admit(fixture([])))["status"], "inconclusive")
        self.assertEqual(score_run(admit(fixture([(0, 0, 0, 0, 0)])))["status"], "not_rejected")

    def test_all_four_global_offsets(self):
        patterns = balanced_patterns(1)
        for offsets in itertools.product(range(2), repeat=2):
            run = admit(fixture(patterns, offsets=offsets))
            self.assertEqual(run.audit["admissible_row_offset_pairs"], [list(offsets)])

    def test_fractional_and_scientific_timestamps_compare_exactly(self):
        data = fixture([(0, 0, 0, 0, 0), (0, 0, 0, 1, 1)])
        for role, row, value in (("local1", 1, "1000.5"), ("local2", 1, "1.0005e3"),
                                 ("pairs", 1, "1000.500"), ("local1", 2, "1e3"),
                                 ("local2", 2, "1099.5"), ("pairs", 2, "1000")):
            data = change(data, role, row, 0, value)
        run = admit(data)
        self.assertEqual(run.trials[0].time_ms, Fraction(2001, 2))
        self.assertEqual(run.trials[1].time_ms, Fraction(1000))
        self.assertAdmissionFailure(change(data, "local2", 2, 0, "1100.0001"), "no_complete_local_join")
        self.assertAdmissionFailure(change(data, "pairs", 1, 0, "NaN"), "nonfinite_or_invalid_timestamp")
        self.assertAdmissionFailure(change(data, "pairs", 1, 0, "-1"), "negative_timestamp")

    def test_multiple_successful_join_candidates_preserved(self):
        data = fixture([(0, 0, 0, 0, 0)])
        for role in ("local1", "local2"):
            data[role] += data[role].splitlines(keepends=True)[1]
        self.assertEqual(admit(data).audit["admissible_row_offset_pairs"], [[0, 0], [0, 1], [1, 0], [1, 1]])

    def test_missing_run_duplicate_reference_and_bad_join(self):
        data = fixture(balanced_patterns(1))
        admitted = admit(data)
        with self.assertRaises(AdmissionError):
            adjudicate({RUNS[0]: admitted})
        self.assertAdmissionFailure(change(data, "pairs", 2, 6, "1"), "no_complete_local_join")
        self.assertAdmissionFailure(change(data, "pairs", 1, 0, "1460000001001"), "no_complete_local_join")
        self.assertAdmissionFailure(change(data, "local2", 1, 0, "1460000001101"), "no_complete_local_join")
        self.assertAdmissionFailure(change(data, "local1", 1, 2, "1"), "no_complete_local_join")

    def test_missing_nonascii_and_third_outcome(self):
        data = fixture(balanced_patterns(1))
        self.assertAdmissionFailure(change(data, "pairs", 1, 3, ""), "missing_or_noncanonical_token")
        self.assertAdmissionFailure(change(data, "pairs", 1, 3, " 0"), "missing_or_noncanonical_token")
        third = change(change(data, "pairs", 1, 3, "2"), "local1", 1, 2, "2")
        self.assertAdmissionFailure(third, "nonbinary_role")
        bad = dict(data)
        bad["pairs"] = bad["pairs"].replace(b"\t0\t", "\t零\t".encode("utf-8"), 1)
        self.assertAdmissionFailure(bad, "missing_or_noncanonical_token")

    def test_raw_flag_consistency_and_unscored_invalid_model(self):
        data = fixture(balanced_patterns(1), flags=("opaque-true", ""), extra_unpaired=True)
        admitted = admit(data)
        self.assertEqual(admitted.audit["join_candidates"][0]["valid_pair_flags"], {"lab1": "opaque-true", "lab2": ""})
        self.assertAdmissionFailure(change(data, "local1", 1, 5, "other-flag"), "no_complete_local_join")

    def test_opaque_none_click_outcomes_and_empty_failure(self):
        patterns = balanced_patterns(1)
        data = fixture(patterns)
        for row, (_, _, _, x, y) in enumerate(patterns, 1):
            labels = ("none", "click")
            data = change(change(data, "local1", row, 2, labels[x]), "pairs", row, 3, labels[x])
            data = change(change(data, "local2", row, 2, labels[y]), "pairs", row, 5, labels[y])
        self.assertEqual(tuple(exact_prefixes(admit(data).trials)), tuple(exact_prefixes(admit(fixture(patterns)).trials)))
        self.assertAdmissionFailure(change(data, "pairs", 1, 3, ""), "missing_or_noncanonical_token")

    def test_schema_and_byte_order_controls(self):
        data = fixture(balanced_patterns(1))
        self.assertAdmissionFailure(change(data, "local2", 1, 6, "not-empty"), "lab2_trailing_column")
        wrong = dict(data)
        wrong["pairs"] = b"wrong header\n" + wrong["pairs"].split(b"\n", 1)[1]
        self.assertAdmissionFailure(wrong, "header_mismatch")
        blank = dict(data)
        blank["pairs"] += b"\n"
        self.assertAdmissionFailure(blank, "empty_record")
        malformed = dict(data)
        malformed["pairs"] += b"one\ttwo\n"
        self.assertAdmissionFailure(malformed, "record_arity")
        with self.assertRaises(AdmissionError):
            Predictor().step(replace(admit(data).trials[0], x=2))

    def test_lab2_six_fields_and_empty_seventh_field_have_equal_scores(self):
        seven = fixture(balanced_patterns(1), extra_unpaired=True)
        six = dict(seven)
        lines = seven["local2"].splitlines(keepends=True)
        six["local2"] = lines[0] + b"".join(line.removesuffix(b";\n") + b"\n" for line in lines[1:])
        original, repaired = score_run(admit(seven)), score_run(admit(six))
        for field in ("trials", "contexts", "four_outcomes", "terminal_e", "max_e", "max_prefix", "first_crossing",
                      "first_crossing_e", "prefix_e_sha256", "components", "pooled_counts", "status", "token_dictionaries"):
            self.assertEqual(original[field], repaired[field])
        self.assertNotEqual(original["local_audit"]["local2_original_bytes_sha256"],
                            repaired["local_audit"]["local2_original_bytes_sha256"])
        self.assertAdmissionFailure(change(seven, "local2", 1, 6, "semantic-data"), "lab2_trailing_column")
        too_many = dict(seven)
        too_many["local2"] = lines[0] + lines[1].removesuffix(b"\n") + b";\n" + b"".join(lines[2:])
        self.assertAdmissionFailure(too_many, "record_arity")

    def test_source_guard_uses_repo_cwd_and_rejects_dirty_or_unbound_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True, capture_output=True)
            for key, value in (("user.name", "Synthetic Control"), ("user.email", "control@example.invalid")):
                subprocess.run(["git", "config", key, value], cwd=repo, check=True, capture_output=True)
            base = repo / "nested" / "science"
            base.mkdir(parents=True)
            source = base / "producer.py"
            source.write_bytes(b"original\n")
            subprocess.run(["git", "add", "nested/science/producer.py"], cwd=repo, check=True, capture_output=True)
            subprocess.run(["git", "commit", "-qm", "Synthetic committed source"], cwd=repo, check=True, capture_output=True)
            real_run = subprocess.run
            def git_response(arguments, **options):
                if arguments[:2] == ["git", "status"]:
                    return subprocess.CompletedProcess(arguments, 0, stdout="", stderr="")
                return real_run(arguments, **options)
            with patch.object(primary, "BASE", base), patch.object(primary, "SCIENTIFIC_FILES", ("producer.py",)):
                snapshot = primary.committed_snapshot()
                self.assertTrue(snapshot["last_scientific_path_commit"])
                self.assertEqual(set(snapshot["scientific_path_git_blobs"]), {"nested/science/producer.py"})
                source.write_bytes(b"changed\n")
                with self.assertRaises(AdmissionError) as dirty:
                    primary.committed_snapshot()
                self.assertEqual(dirty.exception.detail["code"], "dirty_scientific_paths")
                with patch.object(primary.subprocess, "run", side_effect=git_response):
                    with self.assertRaises(AdmissionError) as changed_bytes:
                        primary.committed_snapshot()
                self.assertEqual(changed_bytes.exception.detail["code"], "scientific_current_bytes_not_head")
                source.write_bytes(b"original\n")
                def empty_log(arguments, **options):
                    if arguments[:2] == ["git", "log"]:
                        return subprocess.CompletedProcess(arguments, 0, stdout="", stderr="")
                    return real_run(arguments, **options)
                with patch.object(primary.subprocess, "run", side_effect=empty_log):
                    with self.assertRaises(AdmissionError) as missing_commit:
                        primary.committed_snapshot()
                self.assertEqual(missing_commit.exception.detail["code"], "missing_scientific_path_commit")

    def test_prefix_digest_and_exclusive_first_receipt(self):
        admitted = admit(fixture([(0, 0, 0, 0, 0)] * 3))
        expected = hashlib.sha256(b"".join(fraction_encoding(value) for value in exact_prefixes(admitted.trials))).hexdigest()
        self.assertEqual(score_run(admitted)["prefix_e_sha256"], expected)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "first.json"
            exclusive_json(path, {"first": True})
            original = path.read_bytes()
            with self.assertRaises(FileExistsError):
                exclusive_json(path, {"first": False})
            self.assertEqual(path.read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
