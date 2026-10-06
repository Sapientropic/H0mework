"""Independent full local observer using the already paid dictionary parser."""
import hashlib
import io
import json
import sys
from types import ModuleType
from collections import Counter
from pathlib import Path
from zipfile import ZipFile

MUNICH = Path(__file__).resolve().parent.parent
PARSER_PATH = MUNICH / "invariant_independent.py"
PARSER_SOURCE = PARSER_PATH.read_bytes()
parser = ModuleType("_bell_hr0001_independent_parser")
parser.__file__ = str(PARSER_PATH)
sys.modules[parser.__name__] = parser
exec(compile(PARSER_SOURCE, str(PARSER_PATH), "exec"), parser.__dict__)

FIELDS = ("row", "time_raw", "setting", "result", "local_timestamp", "herald",
          "raw_flag", "comment", "raw_sha256")
ATTRIBUTES = ("row", "time", "setting", "result", "timestamp", "herald", "flag", "comment", "raw_sha256")


def validate_parser_binding():
    if Path(parser.__file__).resolve() != PARSER_PATH or PARSER_PATH.read_bytes() != PARSER_SOURCE:
        raise ValueError("loaded independent parser differs from bound source")


def observe_bytes(raw, run, role):
    validate_parser_binding()
    return tuple(tuple(getattr(record, name) for name in ATTRIBUTES)
                 for record in parser.local_records(raw, role, run))


def load_summaries(directory, paid_receipt):
    validate_parser_binding()
    if paid_receipt.get("admission") != "admitted":
        raise ValueError("paid archive admission required")
    runs = {item["run"]: item for item in paid_receipt["runs"]}
    access = {(item["run"], item["role"]): item
              for item in paid_receipt["record_access"]["members"]}
    summaries = []
    for spec in parser.ARCHIVE_IDENTITIES:
        run = spec["run"]
        path = Path(directory) / spec["name"]
        raw = path.read_bytes()
        parser.demand(len(raw) == spec["bytes"] and parser.digest(raw) == spec["sha256"]
                      and hashlib.md5(raw).hexdigest() == spec["md5"], "archive_bytes_mismatch")
        audit = runs[run]["local_audit"]
        parser.demand(audit["admissible_row_offset_pairs"] == [[1, 1]], "paid_join_identity")
        with ZipFile(io.BytesIO(raw)) as archive:
            parser.demand(sorted(archive.namelist()) == sorted(spec["members"]), "archive_member_inventory")
            for role in ("local1", "local2"):
                payload = archive.read(spec["members"][0 if role == "local1" else 1])
                parser.demand(parser.digest(payload) == access[run, role]["payload_sha256"],
                              "paid_record_binding")
                observed = observe_bytes(payload, run, role)
                parser.demand(tuple(row[0] for row in observed) == tuple(range(1, len(observed) + 1)),
                              "original_row_order")
                local = audit["join_candidates"][0][role]
                numbers = [number for first, last in local["paired_original_rows_rle"]
                           for number in range(first, last + 1)]
                parser.demand(len(numbers) == len(set(numbers)) and
                              all(1 <= n <= len(observed) for n in numbers), "paired_row_inventory")
                stream = hashlib.sha256()
                for row in observed:
                    stream.update(str(row[0]).encode("ascii"))
                    stream.update(b":")
                    stream.update(row[-1].encode("ascii"))
                    stream.update(b"\n")
                parser.demand(stream.hexdigest() == local["all_original_row_sequence_sha256"]
                              and len(observed) == local["total_records"]
                              and len(numbers) == local["paired_records"], "paid_history_identity")
                rehydrated = tuple(parser.LocalRecord(*row) for row in observed)
                summaries.append({
                    "run": run, "role": role, "records": len(observed),
                    "paired_records": len(numbers), "unpaired_records": len(observed) - len(numbers),
                    "fields": list(FIELDS), "observation_sequence_sha256": parser.digest(
                        json.dumps(observed, ensure_ascii=False, separators=(",", ":")).encode("utf-8")),
                    "record_sequence_sha256": stream.hexdigest(),
                    "comment_tags": dict(sorted(Counter(row[7].strip() for row in observed).items())),
                    "every_record_recovered": tuple(tuple(getattr(row, name) for name in ATTRIBUTES)
                                                    for row in rehydrated) == observed,
                })
    return tuple(summaries)
