"""Independent 8D source contraction and rigorous all-prefix point checker.

No optimizer, primary probability formula or primary numerical receipt is used.
Event access belongs solely to the explicit, frozen driver at the end of this file.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
import sys


BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[5]
PARENT = BASE.parent
VERSION = "stage10-munich-readout-rd0001"
RUNS = ("2016-04-15", "2016-06-14")
WITNESS_SCHEMA = "stage10-munich-readout-primitive-witness/v1"
SCHEMA = "stage10-munich-readout-independent-point/v1"
COMPONENTS = ("complement", "alice", "bob", "full")
WEIGHTS = (Fraction(1, 6), Fraction(1, 6), Fraction(1, 6), Fraction(1, 2))
THRESHOLD = Fraction(40)
PRECISION_BITS = 240
BORN_PATH = PARENT.parent / "theory-blind/independent_born.py"
BORN_SHA = "67349b0d8ddc7159dfde847e50aedabc64b92e4686e491a13ba612b833ebf6d9"
PARSER_PATH = PARENT / "invariant_independent.py"
PARSER_SHA = "188bca2fe65a8575f76126bd58b3262aca9c05adbb2ffc7c8615f47d45b74d18"
OLD_FIRSTS = ("primary-first-mu0001.1.json", "independent-first-mu0001.1.json")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def strict_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate_json_key")
            result[key] = value
        return result
    def invalid(_):
        raise ValueError("nonfinite_json_constant")
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=invalid)


def fixed_module(path, expected_sha, name):
    require(digest(path.read_bytes()) == expected_sha, "fixed_math_or_parser_bytes_changed")
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, "fixed_dependency_unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# This fixed dependency contains only exact arithmetic and matrix definitions.
ALG = fixed_module(BORN_PATH, BORN_SHA, "_munich_readout_original_born_algebra")


def rational(value):
    require(type(value) in (int, Fraction, str), "primitive_requires_exact_rational")
    result = Fraction(value)
    if type(value) is str:
        require(str(result) == value, "noncanonical_primitive_rational")
    return result


@dataclass(frozen=True)
class Effect:
    mu: Fraction
    u: Fraction
    z: Fraction

    def __post_init__(self):
        for key in ("mu", "u", "z"):
            object.__setattr__(self, key, rational(getattr(self, key)))
        radius2 = self.u * self.u + self.z * self.z
        require(-1 <= self.mu <= 1 and radius2 <= (1 + self.mu) ** 2
                and radius2 <= (1 - self.mu) ** 2, "effect_outside_complete_cone")


def primitive(document):
    require(type(document) is dict and set(document) == {"alice", "bob"}, "primitive_shape")
    result = {}
    for side in ("alice", "bob"):
        entries = document[side]
        require(type(entries) is list and len(entries) == 2, "complete_own_setting_inventory")
        result[side] = tuple(Effect(**entry) for entry in entries
                             if type(entry) is dict and set(entry) == {"mu", "u", "z"})
        require(len(result[side]) == 2, "primitive_effect_fields")
    return result


def original_vector():
    # Both original Dirac sectors are retained. Each product is exactly +/-1/2.
    diagonal = ALG.Q2(0, Fraction(1, 2))
    sector = (diagonal, diagonal)
    singlet = (ALG.ZERO, diagonal, -diagonal, ALG.ZERO)
    vector = tuple(ALG.C2(a * b) for a in sector for b in singlet)
    require(len(vector) == 8 and ALG.inner(vector, vector) == ALG.C2(ALG.ONE), "source_normalization")
    return vector


def reported_effect(effect, side, outcome):
    require(type(outcome) is int and outcome in (0, 1), "finite_outcome")
    unit = ALG.identity(8)
    if side == "alice":
        x = ALG.tensor(ALG.spin_axis(1, 0), ALG.identity(2))
        z = ALG.tensor(ALG.spin_axis(0, 1), ALG.identity(2))
    else:
        require(side == "bob", "local_side")
        x = ALG.tensor(ALG.identity(4), ALG.axis(1, 0))
        z = ALG.tensor(ALG.identity(4), ALG.axis(0, 1))
    sign = 1 if outcome == 0 else -1
    matrix = ALG.scale(Fraction(1, 2), ALG.add(
        ALG.scale(1 + sign * effect.mu, unit),
        ALG.add(ALG.scale(sign * effect.u, x), ALG.scale(sign * effect.z, z))))
    require(ALG.transpose(matrix) == matrix, "reported_effect_not_self_adjoint")
    return matrix


def born_table(point):
    """Pure full-source matrix contraction; the compact polynomial is not used."""
    vector = original_vector()
    color_z = ALG.tensor(ALG.identity(4), ALG.axis(0, 1))
    prepared = (vector, ALG.act(color_z, vector))
    effects = {(side, setting, outcome): reported_effect(effect, side, outcome)
               for side in ("alice", "bob") for setting, effect in enumerate(point[side])
               for outcome in (0, 1)}
    for side in ("alice", "bob"):
        for setting in (0, 1):
            require(ALG.add(effects[side, setting, 0], effects[side, setting, 1]) == ALG.identity(8),
                    "reported_POVM_incomplete")
    result = {}
    for h, a, b, x, y in itertools.product((0, 1), repeat=5):
        left, right = effects["alice", a, x], effects["bob", b, y]
        joint = ALG.matmul(left, right)
        require(joint == ALG.matmul(right, left), "local_effects_do_not_commute")
        contraction = ALG.inner(prepared[h], ALG.act(joint, prepared[h]))
        require(contraction.imag == ALG.ZERO and contraction.real.s == 0, "nonrational_Born_contraction")
        q = contraction.real.r
        require(0 <= q <= 1, "Born_probability_outside_unit_interval")
        result[h, a, b, x, y] = q
    for h, a, b in itertools.product((0, 1), repeat=3):
        require(sum(result[h, a, b, x, y] for x, y in itertools.product((0, 1), repeat=2)) == 1,
                "joint_distribution_not_normalized")
        for outcome in (0, 1):
            sign = 1 if outcome == 0 else -1
            require(sum(result[h, a, b, outcome, y] for y in (0, 1)) ==
                    (1 + sign * point["alice"][a].mu) / 2, "Alice_source_marginal_disagrees")
            require(sum(result[h, a, b, x, outcome] for x in (0, 1)) ==
                    (1 + sign * point["bob"][b].mu) / 2, "Bob_source_marginal_disagrees")
    return result


@dataclass(frozen=True)
class Bounds:
    lo: int
    hi: int

    def __post_init__(self):
        require(type(self.lo) is int and type(self.hi) is int and self.lo <= self.hi, "integer_interval")

    def __add__(self, other):
        return Bounds(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        return Bounds(self.lo - other.hi, self.hi - other.lo)

    def times(self, number):
        require(type(number) is int, "integer_interval_multiplier")
        return (Bounds(self.lo * number, self.hi * number) if number >= 0 else
                Bounds(self.hi * number, self.lo * number))


def ceil_div(numerator, denominator):
    require(denominator > 0, "positive_integer_denominator")
    return -(-numerator // denominator)


class Arithmetic:
    """Integer lattice bounds with explicit atanh and exponential tails."""
    def __init__(self, bits=PRECISION_BITS):
        require(type(bits) is int and bits >= 96, "insufficient_fixed_precision")
        self.bits, self.scale = bits, 1 << bits
        self.log_terms = bits // 3 + 10
        self.exp_terms = bits // 4 + 12
        self.logs = {}
        self.log_two = self._atanh(Fraction(1, 3))
        self.factorials = [Bounds(0, 0)]

    def _atanh(self, ratio):
        scale = self.scale
        require(0 <= ratio <= Fraction(1, 3), "atanh_range_reduction")
        lo = scale * ratio.numerator // ratio.denominator
        hi = ceil_div(scale * ratio.numerator, ratio.denominator)
        square_lo, square_hi = lo * lo // scale, ceil_div(hi * hi, scale)
        power_lo, power_hi = lo, hi
        sum_lo = sum_hi = 0
        for index in range(self.log_terms):
            divisor = 2 * index + 1
            sum_lo += power_lo // divisor
            sum_hi += ceil_div(power_hi, divisor)
            power_lo = power_lo * square_lo // scale
            power_hi = ceil_div(power_hi * square_hi, scale)
        tail = ceil_div(2 * power_hi * scale,
                        (2 * self.log_terms + 1) * (scale - square_hi))
        return Bounds(2 * sum_lo, 2 * sum_hi + tail)

    def log(self, number):
        number = rational(number)
        require(number > 0, "log_of_nonpositive_probability")
        if number in self.logs:
            return self.logs[number]
        n, d = number.numerator, number.denominator
        power = n.bit_length() - d.bit_length()
        below = n < (d << power) if power >= 0 else (n << -power) < d
        power -= int(below)
        mantissa = number / (1 << power) if power >= 0 else number * (1 << -power)
        require(1 <= mantissa < 2, "log_mantissa")
        value = self._atanh((mantissa - 1) / (mantissa + 1)) + self.log_two.times(power)
        self.logs[number] = value
        return value

    def log_factorial(self, number):
        require(type(number) is int and number >= 0, "factorial_index")
        while len(self.factorials) <= number:
            self.factorials.append(self.factorials[-1] + self.log(len(self.factorials)))
        return self.factorials[number]

    def half_pochhammer(self, number):
        return self.log_factorial(2 * number) - self.log_factorial(number) - self.log_two.times(2 * number)

    def predictor_log(self, counts, dimension):
        require(dimension in (2, 4) and len(counts) == dimension, "predictor_dimension")
        require(all(type(n) is int and n >= 0 for n in counts), "predictor_counts")
        answer = Bounds(0, 0)
        for n in counts:
            answer += self.half_pochhammer(n)
        return answer - self.log_factorial(sum(counts) + int(dimension == 4))

    def _small_positive_exp(self, lo, hi):
        scale = self.scale
        require(0 <= lo <= hi <= scale // 2, "exponential_small_range")
        term_lo = term_hi = total_lo = total_hi = scale
        for index in range(1, self.exp_terms + 1):
            term_lo = term_lo * lo // (scale * index)
            term_hi = ceil_div(term_hi * hi, scale * index)
            total_lo += term_lo
            total_hi += term_hi
        next_term = ceil_div(term_hi * hi, scale * (self.exp_terms + 1))
        tail = ceil_div(next_term * scale * (self.exp_terms + 2),
                        scale * (self.exp_terms + 2) - hi)
        return Bounds(total_lo, total_hi + tail)

    def exp_nonpositive(self, value):
        require(type(value) is int and value <= 0, "nonpositive_exponential_input")
        if value == 0:
            return Bounds(self.scale, self.scale)
        magnitude, reductions = -value, 0
        while 2 * magnitude > self.scale << reductions:
            reductions += 1
        divisor = 1 << reductions
        positive = self._small_positive_exp(magnitude // divisor, ceil_div(magnitude, divisor))
        result = Bounds(self.scale * self.scale // positive.hi,
                        ceil_div(self.scale * self.scale, positive.lo))
        for _ in range(reductions):
            result = Bounds(result.lo * result.lo // self.scale,
                            min(self.scale, ceil_div(result.hi * result.hi, self.scale)))
        return result

    def mixture_log(self, values):
        require(len(values) == 4, "four_process_mixture")
        offset = max(value.hi for value in values)
        lo = hi = 0
        for weight, value in zip(WEIGHTS, values):
            lower = self.exp_nonpositive(value.lo - offset).lo
            upper = self.exp_nonpositive(value.hi - offset).hi
            lo += lower * weight.numerator // weight.denominator
            hi += ceil_div(upper * weight.numerator, weight.denominator)
        require(lo > 0, "mixture_underflow")
        return Bounds(offset + self.log(Fraction(lo, self.scale)).lo,
                      offset + self.log(Fraction(hi, self.scale)).hi)

    def record(self, value):
        return {"lower": str(Fraction(value.lo, self.scale)),
                "upper": str(Fraction(value.hi, self.scale))}


def factor_bytes(number):
    require(type(number) is Fraction and number > 0, "positive_reduced_factor")
    answer = bytearray()
    for integer in (number.numerator, number.denominator):
        raw = integer.to_bytes((integer.bit_length() + 7) // 8, "big")
        answer.extend(len(raw).to_bytes(8, "big"))
        answer.extend(raw)
    return bytes(answer)


def trial_bits(trial, prefix):
    require(type(trial.row) is int and trial.row == prefix, "original_pair_order")
    values = (trial.h, trial.a, trial.b, trial.x, trial.y)
    require(all(type(n) is int and n in (0, 1) for n in values), "canonical_event_bits")
    return values


class Prefixes:
    def __init__(self, table, arithmetic):
        self.q, self.arithmetic = table, arithmetic
        self.cells = {key: [0] * 4 for key in itertools.product((0, 1), repeat=3)}
        self.complements = {key: [0, 0] for key in itertools.product((0, 1), repeat=4)}
        self.alice, self.bob = [0, 0], [0, 0]
        self.denominators = {key: Bounds(0, 0) for key in COMPONENTS}
        self.event_digest, self.factor_digest, self.interval_digest = (hashlib.sha256() for _ in range(3))
        self.factor_prefixes, self.count, self.first_zero = 0, 0, None

    def step(self, trial):
        h, a, b, x, y = trial_bits(trial, self.count + 1)
        self.count += 1
        self.event_digest.update(bytes((h, a, b, x, y)))
        context, parity = (h, a, b), x ^ y
        old_cells = self.cells[context]
        # Both complete binary forecasts are constructed from the preceding prefix.
        parity_forecasts = {
            c: tuple(Fraction(2 * n + 1, 2 * (sum(self.complements[context + (c,)]) + 1))
                     for n in self.complements[context + (c,)]) for c in (0, 1)}
        forecasts = {
            "complement": parity_forecasts[parity][x],
            "alice": Fraction(2 * self.alice[x] + 1, 2 * (sum(self.alice) + 1)),
            "bob": Fraction(2 * self.bob[y] + 1, 2 * (sum(self.bob) + 1)),
            "full": Fraction(2 * old_cells[2 * x + y] + 1, 2 * sum(old_cells) + 4)}
        probability = self.q[h, a, b, x, y]
        if probability == 0 and self.first_zero is None:
            self.first_zero = self.count
        self.cells[context][2 * x + y] += 1
        self.complements[context + (parity,)][x] += 1
        self.alice[x] += 1
        self.bob[y] += 1
        if self.first_zero is not None:
            self.interval_digest.update(canonical([self.count, "infinite"]).encode("ascii") + b"\n")
            return None
        parity_mass = self.q[h, a, b, 0, parity] + self.q[h, a, b, 1, 1 ^ parity]
        denominators = {
            "complement": probability / parity_mass,
            "alice": sum(self.q[h, a, b, x, yy] for yy in (0, 1)),
            "bob": sum(self.q[h, a, b, xx, y] for xx in (0, 1)),
            "full": probability}
        for key in COMPONENTS:
            self.factor_digest.update(factor_bytes(forecasts[key] / denominators[key]))
            self.denominators[key] += self.arithmetic.log(denominators[key])
        self.factor_prefixes += 1
        numerators = {"alice": self.arithmetic.predictor_log(self.alice, 2),
                      "bob": self.arithmetic.predictor_log(self.bob, 2)}
        for name, values, dimension in (("full", self.cells.values(), 4),
                                        ("complement", self.complements.values(), 2)):
            numerators[name] = sum((self.arithmetic.predictor_log(counts, dimension) for counts in values),
                                   start=Bounds(0, 0))
        components = [numerators[key] - self.denominators[key] for key in COMPONENTS]
        result = self.arithmetic.mixture_log(components)
        self.interval_digest.update(canonical([self.count, result.lo, result.hi]).encode("ascii") + b"\n")
        return result


def check_run(admitted, point, *, bits=PRECISION_BITS):
    table = born_table(point)
    arithmetic = Arithmetic(bits)
    prefixes = Prefixes(table, arithmetic)
    threshold = arithmetic.log(THRESHOLD)
    maximum_upper = maximum_lower = maximum_prefix = 0
    crossing, uncertain, terminal = None, 0, None
    for trial in admitted.trials:
        value = prefixes.step(trial)
        if value is None:
            continue
        terminal = value
        if value.hi > maximum_upper:
            maximum_upper, maximum_prefix = value.hi, prefixes.count
        maximum_lower = max(maximum_lower, value.lo)
        if crossing is None and value.lo >= threshold.hi:
            crossing = prefixes.count
        if value.hi >= threshold.lo and value.lo < threshold.hi:
            uncertain += 1
    require(prefixes.count == len(admitted.trials) and prefixes.count > 0, "complete_nonempty_run_required")
    qualified = prefixes.first_zero is None and maximum_upper < threshold.lo
    status = ("certified_all_prefix_point" if qualified else
              "zero_model_probability_observed" if prefixes.first_zero is not None else
              "point_outside_confidence_domain" if crossing is not None else "precision_unresolved")
    return {
        "run": admitted.run, "status": status, "trials": prefixes.count,
        "all_prefixes_below_threshold_certified": qualified,
        "all_pair_records_scored": prefixes.count == admitted.audit["pair_records"],
        "prefixes_checked": prefixes.count, "factor_prefixes": prefixes.factor_prefixes,
        "factor_order": list(COMPONENTS), "factor_sequence_sha256": prefixes.factor_digest.hexdigest(),
        "trial_bit_sequence_sha256": prefixes.event_digest.hexdigest(),
        "prefix_interval_sha256": prefixes.interval_digest.hexdigest(),
        "first_zero_model_probability_prefix": prefixes.first_zero,
        "first_lower_bound_crossing_prefix": crossing, "uncertain_prefixes": uncertain,
        "max_prefix_upper": maximum_prefix,
        "max_log_e": None if prefixes.first_zero is not None else arithmetic.record(Bounds(maximum_lower, maximum_upper)),
        "terminal_log_e": None if terminal is None or prefixes.first_zero is not None else arithmetic.record(terminal),
        "threshold": "40", "per_run_alpha": "1/40", "precision_bits": bits,
        "four_outcomes": [dict(zip(("h", "a", "b"), key), counts=values)
                          for key, values in sorted(prefixes.cells.items())],
        "pooled_counts": {"alice": prefixes.alice, "bob": prefixes.bob},
        "source_probabilities": [dict(zip(("h", "a", "b", "x", "y"), key), q=str(q))
                                 for key, q in sorted(table.items())],
        "local_audit": admitted.audit, "token_dictionaries": admitted.token_dictionaries,
        "source_checks": {"dimension": 8, "probabilities": 32, "normalized_distributions": 8,
                          "complete_effect_cone": True, "source_marginals_checked": True,
                          "primary_probability_formula_used": False},
        "global_domain_rejection_claimed": False,
    }


def certify_run(admitted, point):
    attempts = []
    for precision in (PRECISION_BITS, 320, 384):
        result = check_run(admitted, point, bits=precision)
        attempts.append(precision)
        if result["status"] != "precision_unresolved":
            break
    result["precision_attempts"] = attempts
    return result


def frozen_bytes(path, commit="HEAD"):
    relative = path.relative_to(ROOT).as_posix()
    saved = subprocess.run(["git", "show", f"{commit}:{relative}"], cwd=ROOT,
                           capture_output=True, check=False)
    raw = path.read_bytes()
    require(saved.returncode == 0 and saved.stdout == raw, "scientific_input_not_frozen")
    return raw


def execution_provenance(commit):
    def git_text(*arguments):
        result = subprocess.run(["git", *arguments], cwd=ROOT, capture_output=True,
                                text=True, check=False)
        require(result.returncode == 0, "scientific_git_provenance")
        return result.stdout.strip()
    freeze = git_text("rev-parse", "--verify", f"{commit}^{{commit}}")
    head = git_text("rev-parse", "--verify", "HEAD^{commit}")
    ancestor = subprocess.run(["git", "merge-base", "--is-ancestor", freeze, head],
                              cwd=ROOT, capture_output=True, check=False)
    require(ancestor.returncode == 0, "freeze_not_ancestor_of_execution_head")
    return {"freeze_commit": freeze, "execution_head": head,
            "git_cwd": "repository_root", "freeze_is_execution_ancestor": True}


def freeze_bindings(commit):
    files = [BASE / name for name in ("criterion.md", "sources.json", "method-constraints.md",
                                      "independent.py", "test_independent.py", "source-certification-first.json",
                                      "likelihood_certify.py", "likelihood-certification-first.json",
                                      "LikelihoodCertification.lean")]
    files += [BORN_PATH, PARSER_PATH, PARENT / "sources.json", PARENT / "criterion-mu0001.1.md",
              ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutLikelihood.lean"]
    bindings = []
    for path in files:
        raw = frozen_bytes(path, commit)
        require(frozen_bytes(path) == raw, "scientific_execution_HEAD_changed")
        bindings.append({"path": str(path.relative_to(ROOT)), "sha256": digest(raw)})
    return bindings


def load_witness(raw):
    value = strict_json(raw)
    require(type(value) is dict and set(value) == {"schema", "version", "runs"}, "witness_shape")
    require(value["schema"] == WITNESS_SCHEMA and value["version"] == VERSION, "witness_identity")
    require(type(value["runs"]) is list and len(value["runs"]) == 2, "whole_run_witness_family")
    result = {}
    for expected, entry in zip(RUNS, value["runs"]):
        require(type(entry) is dict and set(entry) == {"run", "primitive"} and entry["run"] == expected,
                "witness_run_identity")
        result[expected] = primitive(entry["primitive"])
    return result


def legacy_cross(admitted, firsts):
    counts = {key: [0] * 4 for key in itertools.product((0, 1), repeat=3)}
    for prefix, trial in enumerate(admitted.trials, 1):
        h, a, b, x, y = trial_bits(trial, prefix)
        counts[h, a, b][2 * x + y] += 1
    expected = [dict(zip(("h", "a", "b"), key), counts=values) for key, values in sorted(counts.items())]
    old_hashes = []
    for first in firsts:
        require(first.get("admission") == "admitted" and first.get("scientific_adjudication_completed") is True,
                "legacy_complete_admission_required")
        require(tuple(run["run"] for run in first["runs"]) == RUNS, "legacy_run_inventory")
        old = next(run for run in first["runs"] if run["run"] == admitted.run)
        require(canonical(old["four_outcomes"]) == canonical(expected) and
                type(old["trials"]) is int and old["trials"] == len(admitted.trials), "legacy_endpoint_counts_changed")
        require(canonical(old["local_audit"]) == canonical(admitted.audit) and
                canonical(old["token_dictionaries"]) == canonical(admitted.token_dictionaries), "legacy_data_identity_changed")
        old_hashes.append(old["prefix_e_sha256"])
    require(old_hashes[0] == old_hashes[1], "legacy_prefix_cross_changed")
    return {"old_counts_and_original_pair_bytes_checked": True,
            "original_token_dictionary_checked": True, "old_statistic_rescored": False,
            "legacy_balanced_prefix_sha256": old_hashes[0]}


def exclusive_json(path, value):
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, sort_keys=True, indent=2)
        stream.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive-dir", type=Path, required=True)
    parser.add_argument("--witness", type=Path, required=True)
    parser.add_argument("--freeze-commit", required=True)
    args = parser.parse_args()
    attempt, first = BASE / "independent-attempt.json", BASE / "independent-first.json"
    try:
        require(not attempt.exists() and not first.exists(), "independent_first_already_reserved")
        provenance = execution_provenance(args.freeze_commit)
        bindings = freeze_bindings(provenance["freeze_commit"])
        legacy_raw = [frozen_bytes(PARENT / name) for name in OLD_FIRSTS]
        legacy_bindings = [{"path": str((PARENT / name).relative_to(ROOT)), "sha256": digest(raw)}
                           for name, raw in zip(OLD_FIRSTS, legacy_raw)]
        witness_raw = args.witness.read_bytes()
        point_family = load_witness(witness_raw)
        exclusive_json(attempt, {"schema": "stage10-munich-readout-independent-attempt/v1",
                                "version": VERSION, "freeze_commit": args.freeze_commit,
                                "program_bindings": bindings, "provenance": provenance,
                                "witness_sha256": digest(witness_raw),
                                "event_records_decoded_at_reservation": 0})
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(canonical({"schema": SCHEMA, "status": "not_started", "reason": str(error)}))
        return 2
    try:
        old_parser = fixed_module(PARSER_PATH, PARSER_SHA, "_munich_readout_legacy_archive_parser")
        old_firsts = [strict_json(raw) for raw in legacy_raw]
        results = []
        archive_bindings = []
        for spec in old_parser.ARCHIVE_IDENTITIES:
            raw = (args.archive_dir / spec["name"]).read_bytes()
            admitted = old_parser.archive_run(raw, spec)
            old_cross = legacy_cross(admitted, old_firsts)
            result = certify_run(admitted, point_family[spec["run"]])
            result["legacy_cross"] = old_cross
            results.append(result)
            archive_bindings.append({"run": spec["run"], "bytes": len(raw), "sha256": digest(raw)})
        qualified = all(run["all_prefixes_below_threshold_certified"] is True for run in results)
        report = {"schema": SCHEMA, "version": VERSION, "status": "certified_source_point" if qualified else "point_not_certified",
                  "source_point_certified": qualified, "familywise_alpha": "1/20", "runs": results,
                  "archive_bindings": archive_bindings,
                  "scope": {"independent_8D_Born_contraction": True, "all_original_prefixes_checked": True,
                            "primary_numeric_receipt_read": False, "optimizer_run": False,
                            "global_domain_rejection_claimed": False, "finite_grid_is_continuous_cover": False,
                            "actual_hardware_identity_claimed": False, "controller_advance": False,
                            "conditional_selected_fixed_run_source_contract_required": True}}
    except Exception as error:
        report = {"schema": SCHEMA, "version": VERSION, "status": "execution_failed",
                  "source_point_certified": False, "reason": str(error), "error_type": type(error).__name__,
                  "global_domain_rejection_claimed": False}
    report.update({"program_bindings": bindings, "witness_sha256": digest(witness_raw),
                   "provenance": provenance,
                   "attempt_sha256": digest(attempt.read_bytes()),
                   "legacy_first_bindings": legacy_bindings})
    exclusive_json(first, report)
    print(canonical({"schema": SCHEMA, "status": report["status"], "source_point_certified": report["source_point_certified"]}))
    return 0 if report["source_point_certified"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
