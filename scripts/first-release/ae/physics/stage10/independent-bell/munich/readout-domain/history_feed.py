"""Full local record observer; archive order is recorded order, not physical action."""
from __future__ import annotations

import hashlib
import io
import json
import sys
from types import ModuleType
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from zipfile import ZipFile

MUNICH = Path(__file__).resolve().parent.parent
PARSER_PATH = MUNICH / "schema.py"
PARSER_SOURCE = PARSER_PATH.read_bytes()
schema = ModuleType("_bell_hr0001_primary_schema")
schema.__file__ = str(PARSER_PATH)
sys.modules[schema.__name__] = schema
exec(compile(PARSER_SOURCE, str(PARSER_PATH), "exec"), schema.__dict__)

FIELDS = ("row", "time_raw", "setting", "result", "local_timestamp", "herald",
          "raw_flag", "comment", "raw_sha256")


def validate_parser_binding():
    if Path(schema.__file__).resolve() != PARSER_PATH or PARSER_PATH.read_bytes() != PARSER_SOURCE:
        raise ValueError("loaded primary parser differs from bound source")


@dataclass(frozen=True)
class RecordHistory:
    run: str
    role: str
    observations: tuple[tuple, ...]
    paired_rows: frozenset[int]

    def __post_init__(self):
        if self.role not in ("local1", "local2"):
            raise ValueError("local record role required")
        if any(len(values) != len(FIELDS) or values[0] != index
               for index, values in enumerate(self.observations, 1)):
            raise ValueError("complete original row sequence required")
        if not self.paired_rows <= frozenset(range(1, len(self.observations) + 1)):
            raise ValueError("paired row outside original history")

    def prefix(self, count):
        if type(count) is not int or not 0 <= count <= len(self.observations):
            raise ValueError("prefix outside observed history")
        return self.observations[:count]

    def recover(self, row):
        if type(row) is not int or not 1 <= row <= len(self.observations):
            raise ValueError("row outside observed history")
        return schema.LocalRow(*self.observations[row - 1])

    def selected_model_view(self):
        return tuple((values[0], values[2], values[3], values[5])
                     for values in self.observations if values[0] in self.paired_rows)

    def summary(self):
        raw = json.dumps(self.observations, ensure_ascii=False,
                         separators=(",", ":")).encode("utf-8")
        return {
            "run": self.run, "role": self.role, "records": len(self.observations),
            "paired_records": len(self.paired_rows),
            "unpaired_records": len(self.observations) - len(self.paired_rows),
            "fields": list(FIELDS), "observation_sequence_sha256": schema.sha256(raw),
            "record_sequence_sha256": schema.sha256(b"".join(
                f"{values[0]}:{values[-1]}\n".encode("ascii") for values in self.observations)),
            "comment_tags": dict(sorted(Counter(values[7].strip()
                                                 for values in self.observations).items())),
            "every_record_recovered": all(
                tuple(getattr(self.recover(index), field) for field in FIELDS) == values
                for index, values in enumerate(self.observations, 1)),
        }


def observe_bytes(raw, run, role, paired_rows=()):
    validate_parser_binding()
    rows = schema.parse_local(raw, role, run)
    return RecordHistory(run, role, tuple(tuple(getattr(row, field) for field in FIELDS)
                                        for row in rows), frozenset(paired_rows))


def expand_ranges(ranges):
    result = set()
    previous = 0
    for first, last in ranges:
        if type(first) is not int or type(last) is not int or not previous < first <= last:
            raise ValueError("original row ranges required")
        result.update(range(first, last + 1))
        previous = last
    return frozenset(result)


def load_histories(directory, paid_receipt):
    validate_parser_binding()
    if paid_receipt.get("admission") != "admitted":
        raise ValueError("paid archive admission required")
    runs = {item["run"]: item for item in paid_receipt["runs"]}
    access = {(item["run"], item["role"]): item
              for item in paid_receipt["record_access"]["members"]}
    histories = []
    for spec in schema.ARCHIVES:
        raw_archive = (Path(directory) / spec.name).read_bytes()
        schema.require(len(raw_archive) == spec.bytes and schema.sha256(raw_archive) == spec.sha256
                       and hashlib.md5(raw_archive).hexdigest() == spec.md5,
                       "archive_bytes_mismatch", run=spec.run)
        audit = runs[spec.run]["local_audit"]
        schema.require(audit["admissible_row_offset_pairs"] == [[1, 1]], "paid_join_identity")
        with ZipFile(io.BytesIO(raw_archive)) as archive:
            schema.require(sorted(archive.namelist()) == sorted(spec.members), "archive_member_inventory")
            for role in ("local1", "local2"):
                raw = archive.read(getattr(spec, role))
                schema.require(schema.sha256(raw) == access[spec.run, role]["payload_sha256"],
                               "paid_record_binding", run=spec.run, member=role)
                local = audit["join_candidates"][0][role]
                selected = expand_ranges(local["paired_original_rows_rle"])
                history = observe_bytes(raw, spec.run, role, selected)
                summary = history.summary()
                schema.require(summary["records"] == local["total_records"]
                               and summary["record_sequence_sha256"] == local["all_original_row_sequence_sha256"]
                               and summary["paired_records"] == local["paired_records"],
                               "paid_history_identity", run=spec.run, member=role)
                histories.append(history)
    return tuple(histories)
