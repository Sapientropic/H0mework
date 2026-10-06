"""Synthetic source, boundary and rigorous arithmetic controls; no archive access."""
import copy
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import independent as checker


def point(mu_a=Fraction(1, 5), mu_b=Fraction(-1, 4)):
    return {"alice": (checker.Effect(mu_a, Fraction(1, 4), Fraction(1, 4)),
                      checker.Effect(-mu_a, Fraction(-1, 4), Fraction(1, 4))),
            "bob": (checker.Effect(mu_b, Fraction(1, 3), Fraction(1, 4)),
                    checker.Effect(-mu_b, Fraction(-1, 3), Fraction(1, 4)))}


def trials(bits):
    return tuple(SimpleNamespace(row=i, h=h, a=a, b=b, x=x, y=y)
                 for i, (h, a, b, x, y) in enumerate(bits, 1))


def admitted(sequence):
    return SimpleNamespace(run=checker.RUNS[0], trials=sequence,
                           audit={"pair_records": len(sequence)}, token_dictionaries={})


def exact_processes(sequence, table):
    cells = {key: [0] * 4 for key in itertools.product((0, 1), repeat=3)}
    complements = {key: [0, 0] for key in itertools.product((0, 1), repeat=4)}
    counts_a, counts_b = [0, 0], [0, 0]
    wealth = {key: Fraction(1) for key in checker.COMPONENTS}
    factors = hashlib.sha256()
    for trial in sequence:
        h, a, b, x, y = trial.h, trial.a, trial.b, trial.x, trial.y
        ctx, parity = (h, a, b), x ^ y
        binary = complements[ctx + (parity,)]
        probability = table[h, a, b, x, y]
        pmass = table[h, a, b, 0, parity] + table[h, a, b, 1, 1 ^ parity]
        row = {
            "complement": Fraction(2 * binary[x] + 1, 2 * (sum(binary) + 1)) * pmass / probability,
            "alice": Fraction(2 * counts_a[x] + 1, 2 * (sum(counts_a) + 1)) /
                     sum(table[h, a, b, x, yy] for yy in (0, 1)),
            "bob": Fraction(2 * counts_b[y] + 1, 2 * (sum(counts_b) + 1)) /
                   sum(table[h, a, b, xx, y] for xx in (0, 1)),
            "full": Fraction(2 * cells[ctx][2 * x + y] + 1, 2 * sum(cells[ctx]) + 4) / probability}
        for key in checker.COMPONENTS:
            wealth[key] *= row[key]
            factors.update(checker.factor_bytes(row[key]))
        binary[x] += 1
        cells[ctx][2 * x + y] += 1
        counts_a[x] += 1
        counts_b[y] += 1
        yield sum(weight * wealth[key] for weight, key in zip(checker.WEIGHTS, checker.COMPONENTS)), factors.hexdigest()


class SourceMatrixControls(unittest.TestCase):
    def test_both_original_dirac_sectors_and_actual_color_z(self):
        a = checker.ALG
        expected = (0, Fraction(1, 2), Fraction(-1, 2), 0,
                    0, Fraction(1, 2), Fraction(-1, 2), 0)
        vector = checker.original_vector()
        self.assertEqual(vector, tuple(a.C2(a.Q2(value)) for value in expected))
        prepared = a.act(a.tensor(a.identity(4), a.axis(0, 1)), vector)
        self.assertEqual(prepared[1], -vector[1])
        self.assertEqual(prepared[2], vector[2])
        self.assertEqual(a.inner(prepared, prepared), a.C2(a.ONE))

    def test_reported_POVM_contracts_full_32_without_closed_formula_or_IO(self):
        with patch.object(checker.ALG, "table", side_effect=AssertionError("old prediction table")), \
                patch.object(checker.ALG, "prepared_vector", side_effect=AssertionError("cached prediction")), \
                patch.object(Path, "read_bytes", side_effect=AssertionError("source IO")):
            table = checker.born_table(point())
        self.assertEqual(len(table), 32)
        self.assertTrue(all(type(value) is Fraction and 0 <= value <= 1 for value in table.values()))

    def test_source_herald_sign_and_exact_marginal_bias(self):
        p = {"alice": (checker.Effect(0, Fraction(3, 5), Fraction(4, 5)),) * 2,
             "bob": (checker.Effect(0, Fraction(-4, 5), Fraction(3, 5)),) * 2}
        table = checker.born_table(p)
        self.assertEqual(table[0, 0, 0, 0, 0], Fraction(1, 4))
        self.assertEqual(table[1, 0, 0, 0, 0], Fraction(1, 100))
        p = {"alice": (checker.Effect(Fraction(1, 3), 0, 0),) * 2,
             "bob": (checker.Effect(Fraction(-1, 5), 0, 0),) * 2}
        table = checker.born_table(p)
        self.assertEqual(table[0, 0, 0, 0, 0], Fraction(4, 15))

    def test_illegal_cone_float_bool_and_target_table_rejected(self):
        for values in ((Fraction(9, 10), Fraction(2, 5), 0), (0.0, 0, 0), (False, 0, 0)):
            with self.subTest(values=values), self.assertRaises((ValueError, TypeError)):
                checker.Effect(*values)
        with self.assertRaises(ValueError):
            checker.primitive({"alice": [], "bob": [], "q": [Fraction(1, 4)] * 32})


class RigorousArithmeticControls(unittest.TestCase):
    def test_log_intervals_cover_independent_high_precision_oracle(self):
        arithmetic = checker.Arithmetic(160)
        for value in (Fraction(1, 10), Fraction(1, 2), Fraction(1), Fraction(2), Fraction(40), Fraction(2**70, 3)):
            enclosure = arithmetic.log(value)
            with localcontext() as context:
                context.prec = 100
                actual = (Decimal(value.numerator) / Decimal(value.denominator)).ln()
                lo, hi = Decimal(enclosure.lo) / Decimal(arithmetic.scale), Decimal(enclosure.hi) / Decimal(arithmetic.scale)
                self.assertLessEqual(lo, actual)
                self.assertGreaterEqual(hi, actual)

    def test_negative_exp_reduction_has_outward_tail(self):
        arithmetic = checker.Arithmetic(160)
        for value in (Fraction(0), Fraction(-1, 10), Fraction(-1), Fraction(-50), Fraction(-1000)):
            coordinate = value.numerator * arithmetic.scale // value.denominator
            enclosure = arithmetic.exp_nonpositive(coordinate)
            with localcontext() as context:
                context.prec = 100
                actual = (Decimal(coordinate) / Decimal(arithmetic.scale)).exp()
                lo, hi = Decimal(enclosure.lo) / Decimal(arithmetic.scale), Decimal(enclosure.hi) / Decimal(arithmetic.scale)
                self.assertLessEqual(lo, actual)
                self.assertGreaterEqual(hi, actual)

    def test_factorial_closed_prefixes_enclose_exact_four_recurrences(self):
        sequence = trials([(0, 0, 0, 0, 0), (1, 1, 0, 1, 0), (0, 1, 1, 0, 1),
                           (0, 0, 0, 1, 1), (1, 0, 1, 1, 0), (0, 0, 0, 0, 1)] * 3)
        table, arithmetic = checker.born_table(point()), checker.Arithmetic(160)
        prefixes = checker.Prefixes(table, arithmetic)
        for trial, (exact, factor_sha) in zip(sequence, exact_processes(sequence, table)):
            enclosure = prefixes.step(trial)
            with localcontext() as context:
                context.prec = 100
                actual = (Decimal(exact.numerator) / Decimal(exact.denominator)).ln()
                self.assertLessEqual(Decimal(enclosure.lo) / Decimal(arithmetic.scale), actual)
                self.assertGreaterEqual(Decimal(enclosure.hi) / Decimal(arithmetic.scale), actual)
            self.assertEqual(prefixes.factor_digest.hexdigest(), factor_sha)

    def test_q_zero_branch_preserves_all_records_and_never_adds_epsilon(self):
        p = {"alice": (checker.Effect(1, 0, 0),) * 2,
             "bob": (checker.Effect(0, 0, 0),) * 2}
        valid = trials([(0, 0, 0, 0, 0), (1, 1, 1, 0, 1), (0, 0, 1, 0, 1)])
        result = checker.check_run(admitted(valid), p, bits=128)
        self.assertTrue(result["all_prefixes_below_threshold_certified"])
        invalid = trials([(0, 0, 0, 0, 0), (1, 1, 1, 1, 1), (0, 0, 1, 0, 1)])
        result = checker.check_run(admitted(invalid), p, bits=128)
        self.assertEqual(result["first_zero_model_probability_prefix"], 2)
        self.assertEqual(result["prefixes_checked"], 3)
        self.assertEqual(result["factor_prefixes"], 1)
        self.assertFalse(result["source_point_certified"] if "source_point_certified" in result else
                         result["all_prefixes_below_threshold_certified"])
        self.assertFalse(result["global_domain_rejection_claimed"])

    def test_wrong_event_order_or_boolean_bit_rejected(self):
        table = checker.born_table(point())
        for sample in (SimpleNamespace(row=2, h=0, a=0, b=0, x=0, y=0),
                       SimpleNamespace(row=1, h=False, a=0, b=0, x=0, y=0)):
            with self.subTest(sample=sample), self.assertRaises(ValueError):
                checker.Prefixes(table, checker.Arithmetic(96)).step(sample)

    def test_factor_encoding_and_process_weights_are_literal(self):
        self.assertEqual(checker.factor_bytes(Fraction(3, 5)),
                         (1).to_bytes(8, "big") + b"\x03" + (1).to_bytes(8, "big") + b"\x05")
        self.assertEqual(checker.COMPONENTS, ("complement", "alice", "bob", "full"))
        self.assertEqual(checker.WEIGHTS, (Fraction(1, 6),) * 3 + (Fraction(1, 2),))
        self.assertEqual(sum(checker.WEIGHTS), 1)

    def test_ROOT_git_freeze_is_ancestor_and_metadata_only(self):
        freeze, head = "a" * 40, "b" * 40
        replies = [SimpleNamespace(returncode=0, stdout=freeze + "\n"),
                   SimpleNamespace(returncode=0, stdout=head + "\n"),
                   SimpleNamespace(returncode=0)]
        with patch.object(checker.subprocess, "run", side_effect=replies) as run:
            provenance = checker.execution_provenance(freeze)
        self.assertEqual(provenance["execution_head"], head)
        self.assertTrue(provenance["freeze_is_execution_ancestor"])
        self.assertTrue(all(call.kwargs["cwd"] == checker.ROOT for call in run.call_args_list))
        replies[-1] = SimpleNamespace(returncode=1)
        with patch.object(checker.subprocess, "run", side_effect=replies), self.assertRaises(ValueError):
            checker.execution_provenance(freeze)

    def test_witness_contains_only_primitives_and_complete_two_runs(self):
        coordinate = {"mu": "0", "u": "1/3", "z": "1/4"}
        value = {"schema": checker.WITNESS_SCHEMA, "version": checker.VERSION,
                 "runs": [{"run": run, "primitive": {"alice": [coordinate, coordinate],
                                                          "bob": [coordinate, coordinate]}}
                          for run in checker.RUNS]}
        self.assertEqual(set(checker.load_witness(json.dumps(value))), set(checker.RUNS))
        extra = copy.deepcopy(value)
        extra["primary_e"] = "1/2"
        with self.assertRaises(ValueError):
            checker.load_witness(json.dumps(extra))
        value["runs"].pop()
        with self.assertRaises(ValueError):
            checker.load_witness(json.dumps(value))


if __name__ == "__main__":
    unittest.main()
