"""Independent exact checker for the Munich balanced-complement contract.

Archives are decoded only by the explicit driver.  The scorer reconstructs each
context's Jeffreys weight from odd products and factorials; it does not import
the primary parser, scorer, numerical code, or primary receipt.
"""

from __future__ import annotations

import argparse
import base64
import csv
import hashlib
import io
import json
import math
import re
import subprocess
import sys
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from zipfile import BadZipFile, ZipFile


BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[4]
RUNS = ("2016-04-15", "2016-06-14")
VERSION = "stage10-munich-mu0001.1"
ALPHA = "1/40"
THRESHOLD = Fraction(40)
EXPECTED_CRITERION = {
    "version": VERSION, "source": "positiveSmoothUnifiedSource", "root_visit": 10,
    "current_tick": 16, "next_tick": 17, "controller_advance": False,
    "runs": ["2016-04-15", "2016-06-14"],
    "null": "conditional_balanced_complement_all_unit_XZ_axes_both_heralds",
    "encoding": "per_run_per_role_ascii_byte_sorted_at_most_two_raw_tokens", "finite_global_label_maps": 32,
    "selection": "all_official_pairs_strict_original_local_row_join", "per_lab_global_row_offsets": [0, 1],
    "pair_window_ms": 100, "valid_pair_flag": "per_lab_constant_raw_token_including_empty",
    "lab2_record_tail": "six_semantic_fields_optional_seventh_empty",
    "predictor": "context_herald_settingA_settingB_parity_Jeffreys_past_only", "per_run_alpha": "1/40",
    "familywise_alpha": "1/20", "per_run_threshold": "40",
    "e_process": "equal_mixture_joint_Alice_marginal_Bob_marginal", "component_weights": ["1/3", "1/3", "1/3"],
    "anytime": True, "exact_prefix_arithmetic": "fractions.Fraction", "score_all_records_after_crossing": True,
    "empirical_fit_parameters": 0, "actual_angles_required": False, "physical_label_dictionary_required": False,
    "hardware_identity_validated": False, "full_joint_validated": False, "theory_validated": False,
    "human_outcome_unexposed_claimed": False,
}
README_SHA256 = "aec6c3be8b4f63f2fb33622665d5882cf7b566796ad152b6472276ffeca772a5"
RAW_HEADERS = {
    "local1": b"time (Unix time in ms);setting;result; local timestamp;Bell-state;excluded from evaluation; comment\n",
    "local2": b"time (Unix time in ms);setting;result;local timestamp;excluded from evaluation;comment;\n",
    "pairs": b"timestamp lab 1 (unix time ms)\tBell-state\tsetting lab 1\tresult lab 1\tsetting lab 2\tresult lab 2\tline in lab 1 file\tline in lab 2 file\n",
}
ARCHIVE_IDENTITIES = (
    {
        "run": RUNS[0], "name": "Bell_2016-04-15.zip", "bytes": 369992,
        "md5": "53544819317d4dcfbe5c63e039a8aa38",
        "sha256": "da9e1125034e5e61a177ae1796f6362ab312bbfbc5947aeec0b09a85e67b8656",
        "members": ["Bell_2016-04-15_9_lab_1.csv", "Bell_2016-04-15_9_lab_2.csv",
                    "Bell_2016-04-15_9_pairs.csv", "Readme.txt"],
    },
    {
        "run": RUNS[1], "name": "Bell_2016-06-14.zip", "bytes": 391935,
        "md5": "030ce1a0c6c6cc7f1107e1cd608cce77",
        "sha256": "b24fb1693dfd14bc4d2b05df6bb23a53fc1e77b3d932c67668c2b7b9515bd84a",
        "members": ["Bell_2016-06-14_16_lab_1.csv", "Bell_2016-06-14_16_lab_2.csv",
                    "Bell_2016-06-14_16_pairs.csv", "Readme.txt"],
    },
)
CONTEXTS = tuple(product((0, 1), repeat=4))
CELLS = tuple(product((0, 1), repeat=3))


class AdmissionError(ValueError):
    def __init__(self, code, **location):
        self.detail = {"code": code, **{k: v for k, v in location.items() if v is not None}}
        super().__init__(code)


def demand(condition, code, **location):
    if not condition:
        raise AdmissionError(code, **location)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def unsigned_bytes(number):
    if type(number) is not int or number < 0:
        raise ValueError("unsigned integer required")
    return number.to_bytes(max(1, (number.bit_length() + 7) // 8), "big")


def rational_bytes(value):
    value = Fraction(value)
    if value <= 0:
        raise ValueError("positive reduced rational required")
    numerator = unsigned_bytes(value.numerator)
    denominator = unsigned_bytes(value.denominator)
    return (len(numerator).to_bytes(8, "big") + numerator
            + len(denominator).to_bytes(8, "big") + denominator)


def exact_summary(value):
    value = Fraction(value)
    if value <= 0:
        raise ValueError("positive rational required")
    numerator, denominator = value.numerator, value.denominator
    power = numerator.bit_length() - denominator.bit_length()
    if ((numerator < denominator << power) if power >= 0
            else (numerator << -power < denominator)):
        power -= 1
    exponent = power - 48
    if exponent < 0:
        floor, remainder = divmod(numerator << -exponent, denominator)
    else:
        floor, remainder = divmod(numerator, denominator << exponent)
    return {
        "numerator_sha256": digest(unsigned_bytes(numerator)),
        "denominator_sha256": digest(unsigned_bytes(denominator)),
        "numerator_bits": numerator.bit_length(), "denominator_bits": denominator.bit_length(),
        "dyadic": {"lower_mantissa": floor,
                   "upper_mantissa": floor + int(bool(remainder)), "exponent": exponent},
    }


@dataclass(frozen=True)
class Trial:
    row: int
    time_ms: Fraction
    h: int
    a: int
    b: int
    x: int
    y: int
    row_a: int
    row_b: int


@dataclass(frozen=True)
class LocalRecord:
    row: int
    time: str
    setting: str
    result: str
    timestamp: str
    herald: str | None
    flag: str
    comment: str
    raw_sha256: str


@dataclass(frozen=True)
class AdmittedRun:
    run: str
    trials: tuple[Trial, ...]
    token_dictionaries: dict
    audit: dict


def integer(text, *, positive=False, **location):
    demand(type(text) is str and re.fullmatch(r"[0-9]+", text) is not None,
           "noninteger_field", **location)
    number = int(text)
    demand(not positive or number > 0, "nonpositive_row_reference", **location)
    return number


def model_label(text, **location):
    demand(type(text) is str and bool(text) and text.isascii() and text == text.strip(),
           "missing_or_noncanonical_token", **location)
    return text


def timestamp(text, **location):
    demand(type(text) is str and re.fullmatch(
        r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?", text) is not None,
        "nonfinite_or_nonnumeric_timestamp", **location)
    try:
        value = Fraction(text)
    except (ValueError, ZeroDivisionError):
        raise AdmissionError("nonfinite_or_nonnumeric_timestamp", **location) from None
    demand(value >= 0, "negative_timestamp", **location)
    return value


def csv_records(raw, kind, run):
    physical = raw.splitlines(keepends=True)
    demand(bool(physical) and physical[0] == RAW_HEADERS[kind], "header_mismatch", run=run, member=kind)
    try:
        reader = csv.DictReader(io.StringIO(raw.decode("utf-8"), newline=""),
                                delimiter="\t" if kind == "pairs" else ";", strict=True)
        expected = RAW_HEADERS[kind].decode("ascii").rstrip("\n").split("\t" if kind == "pairs" else ";")
        demand(reader.fieldnames == expected, "header_mismatch", run=run, member=kind)
        number = 0
        for row in reader:
            number += 1
            location = {"run": run, "member": kind, "row": number}
            demand(reader.line_num == number + 1 and len(physical) > number,
                   "nonphysical_record_numbering", **location)
            if kind == "local2" and row.get("") is None:
                row[""] = ""
            demand(physical[number].strip() != b"" and None not in row and None not in row.values(),
                   "record_arity", **location)
            if kind == "local2":
                demand(row[""] == "", "lab2_trailing_column", **location)
            yield number, row, digest(physical[number]), location
        demand(len(physical) == number + 1, "empty_or_unparsed_record", run=run, member=kind)
    except (UnicodeError, csv.Error):
        raise AdmissionError("record_encoding_or_csv", run=run, member=kind) from None


def local_records(raw, kind, run):
    result = []
    for number, fields, raw_sha, location in csv_records(raw, kind, run):
        flag = fields["excluded from evaluation"]
        comment = fields[" comment" if kind == "local1" else "comment"]
        setting, outcome = fields["setting"], fields["result"]
        stamp = fields[" local timestamp" if kind == "local1" else "local timestamp"]
        herald = fields["Bell-state"] if kind == "local1" else None
        result.append(LocalRecord(number, fields["time (Unix time in ms)"],
                                  setting, outcome, stamp, herald, flag, comment, raw_sha))
    return tuple(result)


def row_ranges(numbers):
    numbers = list(numbers)
    if not numbers:
        return []
    result = []
    start = last = numbers[0]
    for number in numbers[1:]:
        if number == last + 1:
            last = number
        else:
            result.append([start, last])
            start = last = number
    result.append([start, last])
    return result


def audit_local(records, used):
    unmatched = [record for record in records if record.row not in used]
    flags, comments = {}, {}
    for record in records:
        flags.setdefault(record.flag, []).append(record.row)
        comments.setdefault(digest(record.comment.encode("utf-8")), []).append(record.row)
    def sequence_sha(rows):
        answer = hashlib.sha256()
        for record in rows:
            answer.update(f"{record.row}:{record.raw_sha256}\n".encode("ascii"))
        return answer.hexdigest()
    def group_details(key, numbers, key_name):
        paired = sum(number in used for number in numbers)
        return {key_name: key, "records": len(numbers), "paired_records": paired,
                "unpaired_records": len(numbers) - paired, "original_rows_rle": row_ranges(numbers)}
    return {
        "total_records": len(records), "paired_records": len(used), "unpaired_records": len(unmatched),
        "paired_original_rows_rle": row_ranges(record.row for record in records if record.row in used),
        "unpaired_original_rows_rle": row_ranges(record.row for record in unmatched),
        "all_original_row_sequence_sha256": sequence_sha(records),
        "unpaired_original_row_sequence_sha256": sequence_sha(unmatched),
        "raw_flag_groups": [group_details(key, flags[key], "raw_flag")
                            for key in sorted(flags, key=lambda value: value.encode("utf-8"))],
        "comment_groups": [group_details(key, comments[key], "comment_sha256") for key in sorted(comments)],
    }


def admit_run_bytes(run, raw_local1, raw_local2, raw_pairs):
    demand(run in RUNS, "unknown_run", run=run)
    left = local_records(raw_local1, "local1", run)
    right = local_records(raw_local2, "local2", run)
    pairs = []
    for row_number, fields, _, location in csv_records(raw_pairs, "pairs", run):
        row_a = integer(fields["line in lab 1 file"], field="row_a", **location)
        row_b = integer(fields["line in lab 2 file"], field="row_b", **location)
        time = timestamp(fields["timestamp lab 1 (unix time ms)"], field="time", **location)
        role_values = (fields["Bell-state"], fields["setting lab 1"], fields["setting lab 2"],
                       fields["result lab 1"], fields["result lab 2"])
        for role, value in zip(("h", "a", "b", "x", "y"), role_values):
            model_label(value, field=role, **location)
        pairs.append((row_number, time, role_values, row_a, row_b))
    candidates = []
    for offset_a, offset_b in product((0, 1), repeat=2):
        used_left, used_right = set(), set()
        valid = True
        for number, time, labels, raw_a, raw_b in pairs:
            row_a, row_b = raw_a + offset_a, raw_b + offset_b
            if not (1 <= row_a <= len(left) and 1 <= row_b <= len(right)):
                valid = False
                break
            if row_a in used_left or row_b in used_right:
                valid = False
                break
            arow, brow = left[row_a - 1], right[row_b - 1]
            try:
                time_a = timestamp(arow.time, field="time")
                time_b = timestamp(brow.time, field="time")
            except AdmissionError:
                valid = False
                break
            if (time != time_a or abs(time_a - time_b) > 100
                    or labels != (arow.herald, arow.setting, brow.setting, arow.result, brow.result)):
                valid = False
                break
            used_left.add(row_a)
            used_right.add(row_b)
        flags_a = {left[number - 1].flag for number in used_left}
        flags_b = {right[number - 1].flag for number in used_right}
        if valid and len(flags_a) <= 1 and len(flags_b) <= 1:
            candidates.append({
                "lab1_offset": offset_a, "lab2_offset": offset_b,
                "valid_pair_flags": {"lab1": next(iter(flags_a)) if flags_a else None,
                                     "lab2": next(iter(flags_b)) if flags_b else None},
                "local1": audit_local(left, used_left), "local2": audit_local(right, used_right),
            })
    demand(bool(candidates), "no_admissible_row_offset", run=run)
    role_sets = {role: set() for role in ("h", "a", "b", "x", "y")}
    for _, _, labels, _, _ in pairs:
        for role, label in zip(("h", "a", "b", "x", "y"), labels):
            role_sets[role].add(label)
    dictionaries = {}
    for role, labels in role_sets.items():
        demand(len(labels) <= 2 and (bool(labels) or not pairs), "nonbinary_role", run=run, field=role)
        dictionaries[role] = sorted(labels, key=lambda text: text.encode("ascii"))
    lookup = {role: {label: bit for bit, label in enumerate(labels)} for role, labels in dictionaries.items()}
    trials = tuple(Trial(number, time, *(lookup[role][label] for role, label in
                                        zip(("h", "a", "b", "x", "y"), labels)), row_a, row_b)
                   for number, time, labels, row_a, row_b in pairs)
    audit = {
        "pair_records": len(pairs), "pairs_original_bytes_sha256": digest(raw_pairs),
        "local1_original_bytes_sha256": digest(raw_local1), "local2_original_bytes_sha256": digest(raw_local2),
        "admissible_row_offset_pairs": [[candidate["lab1_offset"], candidate["lab2_offset"]]
                                        for candidate in candidates],
        "join_candidates": candidates,
        "record_lines_decoded": len(left) + len(right) + len(pairs),
        "all_pairs_joined": True, "original_pair_order_preserved": True, "additional_outcome_selection": False,
    }
    return AdmittedRun(run, trials, dictionaries, audit)


def archive_run(raw, spec):
    run = spec["run"]
    demand(len(raw) == spec["bytes"] and digest(raw) == spec["sha256"]
           and hashlib.md5(raw).hexdigest() == spec["md5"], "archive_bytes_mismatch", run=run)
    try:
        with ZipFile(io.BytesIO(raw)) as archive:
            names = archive.namelist()
            demand(len(names) == len(set(names)) and set(names) == set(spec["members"]),
                   "archive_member_inventory", run=run)
            readme = archive.read("Readme.txt")
            demand(len(readme) == 1302 and digest(readme) == README_SHA256, "archive_readme", run=run)
            demand(b"line number starts after the header line" in readme
                   and b"valid atom-atom events" in readme, "readme_join_semantics", run=run)
            raw_members = [archive.read(name) for name in spec["members"][:3]]
    except (BadZipFile, KeyError, OSError, RuntimeError):
        raise AdmissionError("archive_container", run=run) from None
    return admit_run_bytes(run, *raw_members)


def terminal_closed_form(context_counts):
    answer = Fraction(1)
    for counts in context_counts.values():
        demand(len(counts) == 2 and all(type(n) is int and n >= 0 for n in counts), "invalid_context_counts")
        odd = [math.prod(range(1, 2 * n, 2)) for n in counts]
        answer *= Fraction(odd[0] * odd[1], math.factorial(sum(counts)))
    return answer


def binary_weight(counts):
    demand(len(counts) == 2 and all(type(n) is int and n >= 0 for n in counts), "invalid_binary_counts")
    return Fraction(math.prod(range(1, 2 * counts[0], 2)) * math.prod(range(1, 2 * counts[1], 2)),
                    math.factorial(sum(counts)))


def score_run(admitted):
    counts = {context: [0, 0] for context in CONTEXTS}
    odd_products = {context: [1, 1] for context in CONTEXTS}
    factorials = {context: 1 for context in CONTEXTS}
    context_wealth = {context: Fraction(1) for context in CONTEXTS}
    outcomes = {cell: [0, 0, 0, 0] for cell in CELLS}
    joint = alice = bob = maximum = Fraction(1)
    wealth = Fraction(1)
    pooled_counts = {"alice": [0, 0], "bob": [0, 0]}
    pooled_odd = {"alice": [1, 1], "bob": [1, 1]}
    pooled_factorial = 1
    maximum_prefix, first_crossing, first_crossing_e = 0, None, None
    sequence = hashlib.sha256()
    for prefix, trial in enumerate(admitted.trials, 1):
        bits = (trial.h, trial.a, trial.b, trial.x, trial.y)
        demand(all(type(bit) is int and bit in (0, 1) for bit in bits), "nonbinary_trial")
        context = (trial.h, trial.a, trial.b, trial.x ^ trial.y)
        old = context_wealth[context]
        odd_products[context][trial.x] *= 2 * counts[context][trial.x] + 1
        factorials[context] *= sum(counts[context]) + 1
        counts[context][trial.x] += 1
        context_wealth[context] = Fraction(math.prod(odd_products[context]), factorials[context])
        joint = joint / old * context_wealth[context]
        pooled_odd["alice"][trial.x] *= 2 * pooled_counts["alice"][trial.x] + 1
        pooled_odd["bob"][trial.y] *= 2 * pooled_counts["bob"][trial.y] + 1
        pooled_counts["alice"][trial.x] += 1
        pooled_counts["bob"][trial.y] += 1
        pooled_factorial *= prefix
        alice = Fraction(math.prod(pooled_odd["alice"]), pooled_factorial)
        bob = Fraction(math.prod(pooled_odd["bob"]), pooled_factorial)
        wealth = (joint + alice + bob) / 3
        outcomes[(trial.h, trial.a, trial.b)][2 * trial.x + trial.y] += 1
        sequence.update(rational_bytes(wealth))
        if wealth > maximum:
            maximum, maximum_prefix = wealth, prefix
        if first_crossing is None and wealth >= THRESHOLD:
            first_crossing = prefix
            first_crossing_e = exact_summary(wealth)
    demand(terminal_closed_form(counts) == joint and binary_weight(pooled_counts["alice"]) == alice
           and binary_weight(pooled_counts["bob"]) == bob, "terminal_closed_form_mismatch")
    status = ("inconclusive" if not admitted.trials else
              "rejected" if first_crossing is not None else "not_rejected")
    result = {
        "run": admitted.run, "trials": len(admitted.trials),
        "contexts": [{"h": h, "a": a, "b": b, "c": c, "counts": counts[(h, a, b, c)]}
                     for h, a, b, c in CONTEXTS],
        "four_outcomes": [{"h": h, "a": a, "b": b, "counts": outcomes[(h, a, b)]}
                          for h, a, b in CELLS],
        "terminal_e": exact_summary(wealth), "max_e": exact_summary(maximum),
        "components": {"joint": exact_summary(joint), "alice": exact_summary(alice), "bob": exact_summary(bob)},
        "pooled_counts": pooled_counts,
        "max_prefix": maximum_prefix, "first_crossing": first_crossing,
        "first_crossing_e": first_crossing_e,
        "prefix_e_sha256": sequence.hexdigest(), "alpha": ALPHA, "threshold": "40", "status": status,
        "token_dictionaries": admitted.token_dictionaries, "local_audit": admitted.audit,
        "all_pair_records_scored": True,
    }
    return result


def method_bindings(raw, document):
    demand(document.get("schema") == "munich-bell-method-source-bindings/v1", "source_schema")
    demand(document.get("metadata_access_commit") == "2268d2aae8"
           and document.get("header_access_commit") == "3471ee8db8", "source_access_commits")
    archives = document.get("archives")
    demand(type(archives) is list and len(archives) == 2, "archive_inventory")
    for recorded, fixed in zip(archives, ARCHIVE_IDENTITIES):
        demand(all(type(recorded.get(key)) is type(value) and recorded.get(key) == value
                   for key, value in fixed.items()), "archive_binding", run=fixed["run"])
    headers = document.get("headers")
    demand(type(headers) is list and len(headers) == 6, "header_inventory")
    index = {(row.get("run"), row.get("member")): row for row in headers}
    demand(len(index) == 6, "duplicate_header_binding")
    for fixed in ARCHIVE_IDENTITIES:
        for member, kind in zip(fixed["members"][:3], ("local1", "local2", "pairs")):
            header = index.get((fixed["run"], member), {})
            expected = RAW_HEADERS[kind]
            demand(header.get("header") == expected.decode("ascii")
                   and header.get("raw_header_base64") == base64.b64encode(expected).decode("ascii")
                   and header.get("sha256") == digest(expected) and header.get("bytes") == len(expected)
                   and header.get("record_lines_read") == 0 and header.get("empty_lines_skipped") == 0,
                   "header_binding", run=fixed["run"], member=member)
    readmes = [item for item in document.get("methods", ()) if item.get("name") == "Readme.txt"]
    demand(len(readmes) == 1, "readme_binding")
    try:
        readme = base64.b64decode(readmes[0]["raw_bytes_base64"], validate=True)
    except (KeyError, ValueError):
        raise AdmissionError("readme_binding") from None
    demand(len(readme) == 1302 and digest(readme) == README_SHA256
           and readmes[0].get("sha256") == README_SHA256
           and readmes[0].get("same_in_both_archives") is True, "readme_binding")
    authority = document.get("theory_authority", {})
    identities = {"source": "positiveSmoothUnifiedSource", "root_visit": 10, "current_tick": 16, "next_tick": 17,
                  "controller_advance": False, "source_theorem_changed": False,
                  "probability_declaration": "SaturationMonoid.PhysicsCore.Stage10.Bell.probability",
                  "runtime_declaration": "SaturationMonoid.PhysicsCore.Stage10.Bell.sameOccurrenceBellPrediction",
                  "original_certification_commit": "79efabda45"}
    for key, value in identities.items():
        demand(type(authority.get(key)) is type(value) and authority.get(key) == value,
               "theory_authority_identity", field=key)
    prefix = "Lean/SaturationMonoid/PhysicsCore/"
    expected_paths = {
        prefix + "Stage10/Bell/" + name + ".lean"
        for name in ("Runtime", "Probabilities", "Source", "Herald", "Operators", "Effects", "TheoryBlind")}
    expected_paths.update({prefix + "Stage9C/Material/SpinPair/Spinor.lean",
                           prefix + "Stage9DEF/Source/Coefficients.lean", prefix + "Stage10/Runtime/Occurrence.lean"})
    theory_directory = "Verification/physics/stage10/independent-bell/theory-blind/"
    expected_paths.update(theory_directory + name for name in
                          ("Certification.lean", "verification.json", "kernel-certification-first.json"))
    bindings = authority.get("bindings", ())
    demand(len(bindings) == 13 and {item.get("path") for item in bindings} == expected_paths,
           "theory_binding_inventory")
    for binding in bindings:
        path = ROOT / binding["path"]
        demand(digest(path.read_bytes()) == binding.get("sha256"), "theory_binding_bytes", file=binding["path"])
    return {"sources_json_sha256": digest(raw), "archive_bindings": archives,
            "header_bindings": headers, "readme_sha256": README_SHA256,
            "metadata_access_commit": "2268d2aae8", "header_access_commit": "3471ee8db8", "theory_authority": authority}


def criterion_contract(raw):
    try:
        text = raw.decode("utf-8")
    except UnicodeError:
        raise AdmissionError("criterion_encoding") from None
    begin, end = "<!-- MUNICH-MU0001.1-FROZEN-BEGIN -->", "<!-- MUNICH-MU0001.1-FROZEN-END -->"
    demand(text.count(begin) == text.count(end) == 1 and text.index(begin) < text.index(end),
           "criterion_frozen_block")
    fragment = text[text.index(begin) + len(begin):text.index(end)].strip()
    demand(fragment.startswith("```json\n") and fragment.endswith("\n```"), "criterion_json_block")
    def unique_pairs(items):
        result = {}
        for key, value in items:
            demand(key not in result, "criterion_duplicate_key")
            result[key] = value
        return result
    try:
        decoded = json.loads(fragment[8:-4], object_pairs_hook=unique_pairs)
    except ValueError:
        raise AdmissionError("criterion_json_block") from None
    demand(json.dumps(decoded, sort_keys=True, separators=(",", ":"))
           == json.dumps(EXPECTED_CRITERION, sort_keys=True, separators=(",", ":")), "criterion_program_mismatch")
    return decoded


def source_document(raw):
    def unique(items):
        result = {}
        for key, value in items:
            demand(key not in result, "duplicate_source_key")
            result[key] = value
        return result
    try:
        return json.loads(raw, object_pairs_hook=unique)
    except (UnicodeError, ValueError):
        raise AdmissionError("source_schema") from None


def frozen_files(commit):
    demand(re.fullmatch(r"[0-9a-f]{7,40}", commit or "") is not None, "freeze_commit")
    bindings = []
    for name in ("criterion-mu0001.1.md", "sources.json", "source-methods.md", "invariant_independent.py",
                 "test_invariant_independent.py", "format-repair-mu0001.1.json"):
        path = BASE / name
        relative = path.relative_to(ROOT).as_posix()
        try:
            frozen = subprocess.run(["git", "show", f"{commit}:{relative}"], cwd=ROOT, check=True,
                                    capture_output=True, timeout=20).stdout
            current = path.read_bytes()
        except (OSError, subprocess.SubprocessError):
            raise AdmissionError("missing_scientific_freeze", file=relative) from None
        demand(frozen == current, "science_changed_since_freeze", file=relative)
        bindings.append({"path": relative, "sha256": digest(current), "freeze_commit": commit})
    return bindings


def git_provenance():
    names = ("criterion-mu0001.1.md", "sources.json", "source-methods.md", "schema.py", "primary.py",
             "invariant_independent.py", "test_invariant_independent.py", "verify.py", "test_verify.py",
             "format-repair-mu0001.1.json")
    paths = [(BASE / name).relative_to(ROOT).as_posix() for name in names]
    blobs = {}
    try:
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, check=True,
                              capture_output=True, text=True, timeout=20).stdout.strip()
        for relative in paths:
            current = subprocess.run(["git", "hash-object", "--no-filters", relative], cwd=ROOT, check=True,
                                     capture_output=True, text=True, timeout=20).stdout.strip()
            committed = subprocess.run(["git", "rev-parse", f"HEAD:{relative}"], cwd=ROOT, check=True,
                                       capture_output=True, text=True, timeout=20).stdout.strip()
            demand(current == committed, "unfrozen_scientific_path", file=relative)
            blobs[relative] = current
        epoch = subprocess.run(["git", "log", "-1", "--format=%H", "--", *paths], cwd=ROOT,
                               check=True, capture_output=True, text=True, timeout=20).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        raise AdmissionError("missing_scientific_provenance") from None
    demand(bool(epoch), "missing_scientific_epoch")
    return {"execution_head": head, "scientific_path_git_blobs": blobs, "last_scientific_path_commit": epoch}


def generate(archive_directory, freeze_commit):
    program_bindings = frozen_files(freeze_commit)
    provenance = git_provenance()
    attempt = BASE / "independent-attempt-mu0001.1.json"
    demand(attempt.is_file(), "missing_independent_attempt")
    criterion_raw = (BASE / "criterion-mu0001.1.md").read_bytes()
    criterion_contract(criterion_raw)
    sources_raw = (BASE / "sources.json").read_bytes()
    document = source_document(sources_raw)
    bindings = method_bindings(sources_raw, document)
    bindings["criterion_sha256"] = digest(criterion_raw)
    format_raw = (BASE / "format-repair-mu0001.1.json").read_bytes()
    format_document = source_document(format_raw)
    demand(format_document.get("schema") == "munich-mu0001.1-format-repair/v1"
           and format_document.get("parent_scientific_freeze") == "fc4305fe13"
           and format_document.get("parent_first_admission") == "failed_without_statistical_verdict",
           "format_repair_parent_binding")
    for field in ("physics_prediction_changed", "e_process_changed", "alpha_changed", "pairs_denominator_changed"):
        demand(format_document.get(field) is False, "format_repair_changed_science", field=field)
    observations = format_document.get("observations", ())
    demand(len(observations) == 2 and tuple(row.get("run") for row in observations) == RUNS,
           "format_repair_family")
    for observation, archive in zip(observations, ARCHIVE_IDENTITIES):
        demand(observation.get("member") == archive["members"][1]
               and observation.get("header_fields") == 7 and observation.get("first_record_fields") == 6
               and observation.get("row_model_values_reported") == 0 and observation.get("statistics_computed") == 0,
               "format_repair_scope")
    bindings["format_repair_sha256"] = digest(format_raw)
    raw_archives = []
    for spec in ARCHIVE_IDENTITIES:
        try:
            raw = (Path(archive_directory) / spec["name"]).read_bytes()
        except OSError:
            raise AdmissionError("missing_or_unreadable_archive", run=spec["run"]) from None
        demand(len(raw) == spec["bytes"] and digest(raw) == spec["sha256"]
               and hashlib.md5(raw).hexdigest() == spec["md5"], "archive_bytes_mismatch", run=spec["run"])
        raw_archives.append(raw)
    runs = [score_run(archive_run(raw, spec)) for raw, spec in zip(raw_archives, ARCHIVE_IDENTITIES)]
    status = ("rejected" if any(run["status"] == "rejected" for run in runs) else
              "inconclusive" if any(run["status"] == "inconclusive" for run in runs) else "not_rejected")
    return {
        "schema": "stage10-munich-balanced-invariant-independent/v1", "version": VERSION,
        "status": "adjudication_completed", "admission": "admitted", "scientific_verdict": status,
        "scientific_adjudication_completed": True, "real_instrument_empirical_verdict_executed": True, "runs": runs,
        "familywise_alpha": "1/20", "source_bindings": bindings, "program_bindings": program_bindings,
        "provenance": provenance, "attempt_sha256": digest(attempt.read_bytes()),
        "checks": {"independent_original_archive_parse": True, "all_original_prefixes_scored": True,
                   "terminal_context_closed_form_checked": True, "primary_receipt_read": False},
        "scope": {"conditional_balanced_complement_instrument_contract": True,
                  "continuous_XZ_geometry_eliminated": True, "empirical_parameters_used": False,
                  "encoding_selected_by_outcomes": False, "full_joint_model_validated": False,
                  "underlying_theory_validated": False, "hardware_identity_validated": False,
                  "source_theorem_changed": False, "controller_advance": False,
                  "event_record_lines_decoded": sum(run["local_audit"]["record_lines_decoded"] for run in runs),
                  "actual_empirical_adjudication_executed": any(run["trials"] > 0 for run in runs)},
    }


def write_first(path, payload):
    with path.open("x", encoding="utf-8") as stream:
        json.dump(payload, stream, indent=2, sort_keys=True)
        stream.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive-dir", type=Path, required=True)
    parser.add_argument("--freeze-commit", required=True)
    args = parser.parse_args()
    attempt = BASE / "independent-attempt-mu0001.1.json"
    first = BASE / "independent-first-mu0001.1.json"
    if attempt.exists() or first.exists():
        parser.error("the independent first attempt is already present")
    try:
        bindings = frozen_files(args.freeze_commit)
    except AdmissionError as error:
        print(json.dumps({"status": "not_started", "error": error.detail}), file=sys.stderr)
        return 2
    write_first(attempt, {"schema": "stage10-munich-independent-attempt/v1", "program_bindings": bindings,
                          "event_record_lines_decoded_before_attempt": 0, "freeze_commit": args.freeze_commit})
    try:
        report = generate(args.archive_dir, args.freeze_commit)
    except AdmissionError as error:
        report = {"schema": "stage10-munich-balanced-invariant-independent/v1", "version": VERSION,
                  "status": "admission_failed", "admission": "failed", "scientific_verdict": "inconclusive",
                  "scientific_adjudication_completed": False, "error": error.detail,
                  "real_instrument_empirical_verdict_executed": False,
                  "program_bindings": bindings, "scope": {"statistical_verdict_generated": False,
                  "source_theorem_changed": False, "hardware_identity_validated": False}}
    write_first(first, report)
    print(json.dumps({"status": report["status"], "scientific_verdict": report["scientific_verdict"]}, sort_keys=True))
    return 0 if report["status"] == "adjudication_completed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
