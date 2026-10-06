"""ETH Storz 2023 main stream, from the custodian's documented schema."""

import csv
import io
from zipfile import ZipFile


MEMBER = "ETH_repo_upload/main_dataset_all_events.txt"


def parse_rows(stream):
    for line in range(1, 4):
        if not stream.readline():
            raise ValueError(f"missing documented header line {line}")
    for line, text in enumerate(stream, 4):
        fields = next(csv.reader([text], strict=True))
        if len(fields) != 4:
            raise ValueError(f"line {line}: expected four fields")
        a, x, b, y = (int(field.strip()) for field in fields)
        if a not in (0, 1) or b not in (0, 1) or x not in (-1, 1) or y not in (-1, 1):
            raise ValueError(f"line {line}: value outside documented input/output domains")
        yield {"herald": 1, "a": a, "b": b, "x": x, "y": y,
               "source_file": MEMBER, "source_line": line}


def trials(archive_path):
    with ZipFile(archive_path) as archive:
        with archive.open(MEMBER) as binary:
            with io.TextIOWrapper(binary, encoding="utf-8", newline="") as stream:
                yield from parse_rows(stream)
