"""Fixed Munich archive/schema admission; no records are read at import time."""
from __future__ import annotations

import base64
import csv
import hashlib
import io
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from zipfile import BadZipFile, ZipFile


@dataclass(frozen=True)
class ArchiveSpec:
    run: str
    name: str
    bytes: int
    md5: str
    sha256: str
    local1: str
    local2: str
    pairs: str

    @property
    def members(self):
        return [self.local1, self.local2, self.pairs, "Readme.txt"]


ARCHIVES = (
    ArchiveSpec("2016-04-15", "Bell_2016-04-15.zip", 369992,
                "53544819317d4dcfbe5c63e039a8aa38",
                "da9e1125034e5e61a177ae1796f6362ab312bbfbc5947aeec0b09a85e67b8656",
                "Bell_2016-04-15_9_lab_1.csv", "Bell_2016-04-15_9_lab_2.csv",
                "Bell_2016-04-15_9_pairs.csv"),
    ArchiveSpec("2016-06-14", "Bell_2016-06-14.zip", 391935,
                "030ce1a0c6c6cc7f1107e1cd608cce77",
                "b24fb1693dfd14bc4d2b05df6bb23a53fc1e77b3d932c67668c2b7b9515bd84a",
                "Bell_2016-06-14_16_lab_1.csv", "Bell_2016-06-14_16_lab_2.csv",
                "Bell_2016-06-14_16_pairs.csv"),
)
RUNS = tuple(spec.run for spec in ARCHIVES)
HEADERS = {
    "local1": b"time (Unix time in ms);setting;result; local timestamp;Bell-state;excluded from evaluation; comment\n",
    "local2": b"time (Unix time in ms);setting;result;local timestamp;excluded from evaluation;comment;\n",
    "pairs": b"timestamp lab 1 (unix time ms)\tBell-state\tsetting lab 1\tresult lab 1\tsetting lab 2\tresult lab 2\tline in lab 1 file\tline in lab 2 file\n",
}
README_SHA256 = "aec6c3be8b4f63f2fb33622665d5882cf7b566796ad152b6472276ffeca772a5"


class AdmissionError(ValueError):
    def __init__(self, code, *, run=None, member=None, row=None, field=None):
        self.detail = {"code": code}
        self.detail.update({k: v for k, v in
                            (("run", run), ("member", member), ("row", row), ("field", field))
                            if v is not None})
        super().__init__(code)


def require(condition, code, **location):
    if not condition:
        raise AdmissionError(code, **location)


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def validate_bindings(document):
    require(document.get("schema") == "munich-bell-method-source-bindings/v1", "source_schema")
    require(document.get("metadata_access_commit") == "2268d2aae8", "metadata_access_commit")
    require(document.get("header_access_commit") == "3471ee8db8", "header_access_commit")
    require(len(document.get("archives", ())) == 2, "archive_inventory")
    for actual, spec in zip(document["archives"], ARCHIVES):
        for key in ("run", "name", "bytes", "md5", "sha256"):
            require(actual.get(key) == getattr(spec, key), "archive_binding", run=spec.run, field=key)
        require(actual.get("members") == spec.members, "archive_member_binding", run=spec.run)
    header_entries = document.get("headers", ())
    require(len(header_entries) == 6, "header_inventory")
    index = {(item.get("run"), item.get("member")): item for item in header_entries}
    require(len(index) == 6, "duplicate_header_binding")
    for spec in ARCHIVES:
        for role in HEADERS:
            member = getattr(spec, role)
            bound = index.get((spec.run, member), {})
            raw = HEADERS[role]
            require(bound.get("header") == raw.decode("ascii") and
                    bound.get("raw_header_base64") == base64.b64encode(raw).decode("ascii") and
                    bound.get("bytes") == len(raw) and bound.get("sha256") == sha256(raw) and
                    bound.get("empty_lines_skipped") == 0 and bound.get("record_lines_read") == 0,
                    "header_binding", run=spec.run, member=member)
    readmes = [item for item in document.get("methods", ()) if item.get("name") == "Readme.txt"]
    require(len(readmes) == 1, "readme_binding")
    readme = readmes[0]
    try:
        raw = base64.b64decode(readme["raw_bytes_base64"], validate=True)
    except (ValueError, KeyError):
        raise AdmissionError("readme_binding") from None
    require(len(raw) == 1302 and sha256(raw) == README_SHA256 and
            readme.get("sha256") == README_SHA256 and readme.get("same_in_both_archives") is True,
            "readme_binding")
    expected_format = {
        "pair_window_ms": 100, "row_reference_origin": "after header line",
        "lab_delimiter": ";", "pairs_delimiter": "\t", "lab2_trailing_empty_column": True,
        "lab1_columns": HEADERS["local1"].decode("ascii").rstrip("\n").split(";"),
        "lab2_columns": HEADERS["local2"].decode("ascii").rstrip("\n").split(";"),
        "pairs_columns": HEADERS["pairs"].decode("ascii").rstrip("\n").split("\t"),
    }
    for key, value in expected_format.items():
        require(document.get("format", {}).get(key) == value, "format_binding", field=key)


@dataclass(frozen=True)
class LocalRow:
    row: int
    time_raw: str
    setting: str
    result: str
    local_timestamp: str
    herald: str | None
    raw_flag: str
    comment: str
    raw_sha256: str


@dataclass(frozen=True)
class PairRow:
    row: int
    time_ms: Fraction
    herald: str
    setting_a: str
    result_a: str
    setting_b: str
    result_b: str
    row_a: int
    row_b: int


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
class AdmittedRun:
    run: str
    trials: tuple[Trial, ...]
    token_dictionaries: dict
    audit: dict


def token(value, field, **location):
    require(bool(value) and value.isascii() and value == value.strip(),
            "missing_or_noncanonical_token", field=field, **location)
    return value


def integer(value, field, *, positive=False, **location):
    require(re.fullmatch(r"[0-9]+", value) is not None, "noninteger_field", field=field, **location)
    number = int(value)
    require(not positive or number > 0, "nonpositive_row_reference", field=field, **location)
    return number


def timestamp(value, field, **location):
    numeric = value.strip()
    require(re.fullmatch(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?", numeric) is not None,
            "nonfinite_or_invalid_timestamp", field=field, **location)
    number = Fraction(numeric)
    require(number >= 0, "negative_timestamp", field=field, **location)
    return number


def records(raw, role, run, access=None):
    lines = raw.splitlines(keepends=True)
    require(bool(lines) and lines[0] == HEADERS[role], "header_mismatch", run=run, member=role)
    for number, line in enumerate(lines[1:], 1):
        location = {"run": run, "member": role, "row": number}
        require(line.strip() != b"", "empty_record", **location)
        try:
            text = line.decode("utf-8").removesuffix("\n").removesuffix("\r")
            if access is not None:
                access[(run, role)]["record_lines_decoded"] += 1
            fields = next(csv.reader([text], delimiter="\t" if role == "pairs" else ";", strict=True))
        except (UnicodeError, csv.Error, StopIteration):
            raise AdmissionError("record_encoding_or_csv", **location) from None
        if role == "local2":
            require(len(fields) in (6, 7), "record_arity", **location)
            if len(fields) == 6:
                fields.append("")
            else:
                require(fields[-1] == "", "lab2_trailing_column", **location)
        else:
            require(len(fields) == (8 if role == "pairs" else 7), "record_arity", **location)
        yield number, fields, sha256(line), location
    if access is not None:
        access[(run, role)]["fully_decoded"] = True


def parse_local(raw, role, run, access=None):
    result = []
    for number, fields, digest, _ in records(raw, role, run, access):
        flag_column, comment_column = (5, 6) if role == "local1" else (4, 5)
        flag = fields[flag_column]
        comment = fields[comment_column]
        result.append(LocalRow(
            number, fields[0], fields[1], fields[2], fields[3],
            fields[4] if role == "local1" else None, flag, comment, digest))
    return tuple(result)


def parse_pairs(raw, run, access=None):
    result = []
    for number, fields, _, location in records(raw, "pairs", run, access):
        result.append(PairRow(
            number, timestamp(fields[0], "time", **location), token(fields[1], "herald", **location),
            token(fields[2], "setting_a", **location), token(fields[3], "result_a", **location),
            token(fields[4], "setting_b", **location), token(fields[5], "result_b", **location),
            integer(fields[6], "row_a", **location), integer(fields[7], "row_b", **location)))
    return tuple(result)


def ranges(numbers):
    answer = []
    for number in numbers:
        if answer and answer[-1][1] + 1 == number:
            answer[-1][1] = number
        else:
            answer.append([number, number])
    return answer


def local_audit(rows, used):
    unpaired = [row for row in rows if row.row not in used]
    flags, comments = {}, {}
    for row in rows:
        flags.setdefault(row.raw_flag, []).append(row.row)
        comments.setdefault(sha256(row.comment.encode("utf-8")), []).append(row.row)
    def sequence_digest(selected):
        digest = hashlib.sha256()
        for row in selected:
            digest.update(f"{row.row}:{row.raw_sha256}\n".encode("ascii"))
        return digest.hexdigest()
    def group_counts(numbers):
        paired = sum(number in used for number in numbers)
        return {"records": len(numbers), "paired_records": paired, "unpaired_records": len(numbers) - paired,
                "original_rows_rle": ranges(numbers)}
    return {
        "total_records": len(rows), "paired_records": len(used), "unpaired_records": len(unpaired),
        "paired_original_rows_rle": ranges(sorted(used)),
        "unpaired_original_rows_rle": ranges(row.row for row in unpaired),
        "all_original_row_sequence_sha256": sequence_digest(rows),
        "unpaired_original_row_sequence_sha256": sequence_digest(unpaired),
        "raw_flag_groups": [dict(raw_flag=flag, **group_counts(numbers))
                            for flag, numbers in sorted(flags.items(), key=lambda item: item[0].encode("utf-8"))],
        "comment_groups": [dict(comment_sha256=digest, **group_counts(numbers))
                           for digest, numbers in sorted(comments.items())],
    }


def join_candidate(run, first, second, pairs, offset_a, offset_b):
    used_a, used_b = set(), set()
    flags_a, flags_b = set(), set()
    for pair in pairs:
        location = {"run": run, "member": "pairs", "row": pair.row}
        row_a, row_b = pair.row_a + offset_a, pair.row_b + offset_b
        require(1 <= row_a <= len(first) and 1 <= row_b <= len(second), "row_reference_out_of_range", **location)
        require(row_a not in used_a and row_b not in used_b, "duplicate_local_reference", **location)
        left, right = first[row_a - 1], second[row_b - 1]
        left_time = timestamp(left.time_raw, "local1_time", **location)
        right_time = timestamp(right.time_raw, "local2_time", **location)
        require(pair.time_ms == left_time and abs(left_time - right_time) <= 100,
                "timestamp_join", **location)
        require((pair.herald, pair.setting_a, pair.result_a, pair.setting_b, pair.result_b) ==
                (left.herald, left.setting, left.result, right.setting, right.result), "model_field_join", **location)
        used_a.add(row_a)
        used_b.add(row_b)
        flags_a.add(left.raw_flag)
        flags_b.add(right.raw_flag)
    require(len(flags_a) <= 1 and len(flags_b) <= 1, "nonconstant_valid_pair_flags", run=run)
    return {
        "lab1_offset": offset_a, "lab2_offset": offset_b,
        "valid_pair_flags": {"lab1": next(iter(flags_a)) if flags_a else None,
                             "lab2": next(iter(flags_b)) if flags_b else None},
        "local1": local_audit(first, used_a), "local2": local_audit(second, used_b),
    }


def admit_run_bytes(run, raw_local1, raw_local2, raw_pairs, access=None):
    require(run in RUNS, "unknown_run", run=run)
    if access is not None:
        for role, raw in (("local1", raw_local1), ("local2", raw_local2), ("pairs", raw_pairs)):
            access[(run, role)] = {"run": run, "role": role, "payload_bytes": len(raw),
                                  "payload_sha256": sha256(raw), "record_lines_in_payload": max(0, len(raw.splitlines()) - 1),
                                  "record_lines_decoded": 0, "fully_decoded": False}
    first = parse_local(raw_local1, "local1", run, access)
    second = parse_local(raw_local2, "local2", run, access)
    pairs = parse_pairs(raw_pairs, run, access)
    candidates = []
    for offset_a in (0, 1):
        for offset_b in (0, 1):
            try:
                candidates.append(join_candidate(run, first, second, pairs, offset_a, offset_b))
            except AdmissionError:
                continue
    require(bool(candidates), "no_complete_local_join", run=run)
    raw_roles = {
        "h": {row.herald for row in pairs}, "a": {row.setting_a for row in pairs},
        "b": {row.setting_b for row in pairs}, "x": {row.result_a for row in pairs}, "y": {row.result_b for row in pairs},
    }
    dictionaries = {}
    for role, values in raw_roles.items():
        require(len(values) <= 2, "nonbinary_role", run=run, field=role)
        dictionaries[role] = sorted(values)
    encode = {role: {value: bit for bit, value in enumerate(values)} for role, values in dictionaries.items()}
    trials = tuple(Trial(pair.row, pair.time_ms, encode["h"][pair.herald], encode["a"][pair.setting_a],
                         encode["b"][pair.setting_b], encode["x"][pair.result_a], encode["y"][pair.result_b],
                         pair.row_a, pair.row_b) for pair in pairs)
    audit = {
        "pair_records": len(pairs), "pairs_original_bytes_sha256": sha256(raw_pairs),
        "local1_original_bytes_sha256": sha256(raw_local1), "local2_original_bytes_sha256": sha256(raw_local2),
        "admissible_row_offset_pairs": [[candidate["lab1_offset"], candidate["lab2_offset"]] for candidate in candidates],
        "join_candidates": candidates,
        "record_lines_decoded": len(first) + len(second) + len(pairs),
        "all_pairs_joined": True, "original_pair_order_preserved": True,
        "additional_outcome_selection": False,
    }
    return AdmittedRun(run, trials, dictionaries, audit)


def admit_archive(directory, spec, access=None):
    path = Path(directory) / spec.name
    try:
        raw_archive = path.read_bytes()
    except OSError:
        raise AdmissionError("missing_or_unreadable_archive", run=spec.run) from None
    require(len(raw_archive) == spec.bytes and sha256(raw_archive) == spec.sha256 and
            hashlib.md5(raw_archive).hexdigest() == spec.md5, "archive_bytes_mismatch", run=spec.run)
    try:
        with ZipFile(io.BytesIO(raw_archive)) as archive:
            names = archive.namelist()
            require(len(names) == len(set(names)) and sorted(names) == sorted(spec.members),
                    "archive_member_inventory", run=spec.run)
            readme = archive.read("Readme.txt")
            require(len(readme) == 1302 and sha256(readme) == README_SHA256, "archive_readme", run=spec.run)
            return admit_run_bytes(spec.run, archive.read(spec.local1), archive.read(spec.local2), archive.read(spec.pairs), access)
    except (BadZipFile, KeyError, OSError):
        raise AdmissionError("archive_container", run=spec.run) from None
