"""Exact counter/Unix-time observations; candidate scales do not identify a clock unit."""
from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from fractions import Fraction

import history_feed


CANDIDATE_TICKS_PER_MS = (1, 50000, 100000, 12500000)
PAIR_STATUSES = ("valid_uid_pair", "invalid_uid_a", "invalid_uid_b", "invalid_uid_both")


def uid(value):
    if type(value) is not str or re.fullmatch(r"[0-9]+", value) is None:
        return None
    try:
        return int(value)
    except ValueError:
        return None


def unix_ms(value):
    if type(value) is not str:
        return None
    try:
        return history_feed.schema.timestamp(value, "Unix_ms")
    except (TypeError, ValueError):
        return None


def _text(value):
    return None if value is None else str(value)


def _update_digest(digest, item):
    digest.update(json.dumps(item, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
    digest.update(b"\n")


def _origin(run, role, row):
    return [run, role, row[0], row[-1]]


def _history(run, role, rows, paired_rows):
    rows = tuple(rows)
    selected = tuple(paired_rows)
    if any(type(number) is not int for number in selected):
        raise ValueError("integer original paired rows required")
    if any(len(row) != len(history_feed.FIELDS) or type(row[0]) is not int or row[0] != index
           for index, row in enumerate(rows, 1)):
        raise ValueError("complete original row sequence required")
    if len(selected) != len(set(selected)):
        raise ValueError("duplicate original paired row")
    return history_feed.RecordHistory(run, role, rows, frozenset(selected))


@dataclass
class _Extrema:
    usable: int = 0
    minimum: Fraction | int | None = None
    maximum: Fraction | int | None = None
    min_origin: list | None = None
    max_origin: list | None = None

    def add(self, value, origin):
        self.usable += 1
        if self.minimum is None or value < self.minimum:
            self.minimum, self.min_origin = value, origin
        if self.maximum is None or value > self.maximum:
            self.maximum, self.max_origin = value, origin

    def result(self):
        return {
            "min": _text(self.minimum), "max": _text(self.maximum),
            "width": _text(None if self.minimum is None else self.maximum - self.minimum),
            "min_origin": self.min_origin, "max_origin": self.max_origin,
        }

    def counted(self, records):
        return {"usable": self.usable, "omitted": records - self.usable, **self.result()}


def local_summary(run, role, rows, paired_rows=()):
    """Observe every original row; no flag, comment, or paired selection filters a counter."""
    history_feed.validate_parser_binding()
    history = _history(run, role, rows, paired_rows)
    digest = hashlib.sha256()
    ranges = [_Extrema() for _ in CANDIDATE_TICKS_PER_MS]
    numeric = {"uid": {"valid": 0, "invalid": 0}, "unix_ms": {"valid": 0, "invalid": 0}}
    adjacent = {"negative": 0, "zero": 0, "positive": 0, "invalid": 0}
    invalid = []
    endpoints = []
    first = last = None
    previous = None
    for index, row in enumerate(history.observations):
        counter, time = uid(row[4]), unix_ms(row[1])
        origin = _origin(run, role, row)
        invalid_fields = []
        for name, value in (("uid", counter), ("unix_ms", time)):
            numeric[name]["invalid" if value is None else "valid"] += 1
            if value is None:
                invalid_fields.append(name)
        if invalid_fields:
            invalid.append({"origin": origin, "uid_raw": row[4], "unix_ms_raw": row[1],
                            "invalid": invalid_fields})
        if index:
            if previous is None or counter is None:
                adjacent["invalid"] += 1
            else:
                difference = counter - previous
                adjacent["negative" if difference < 0 else "positive" if difference > 0 else "zero"] += 1
        previous = counter
        endpoint = {"origin": origin, "uid": _text(counter), "unix_ms": _text(time)}
        if index == 0 or index == len(history.observations) - 1:
            endpoints.append(endpoint)
        if counter is not None and time is not None:
            if first is None:
                first = endpoint
            last = endpoint
            for ticks, extrema in zip(CANDIDATE_TICKS_PER_MS, ranges):
                extrema.add(time - Fraction(counter, ticks), origin)
        _update_digest(digest, (row, row[0] in history.paired_rows, _text(counter), _text(time)))
    span = {}
    for name in ("uid", "unix_ms"):
        span[name] = (None if first is None or first[name] is None or last[name] is None
                      else str(Fraction(last[name]) - Fraction(first[name])))
    return {
        "run": run, "role": role, "records": len(history.observations),
        "paired_records": len(history.paired_rows),
        "unpaired_records": len(history.observations) - len(history.paired_rows),
        "counter_observations_sha256": digest.hexdigest(), "numeric": numeric,
        "invalid_records": invalid, "first": first, "last": last, "span": span,
        "raw_endpoints": {"first": endpoints[0] if endpoints else None,
                          "last": endpoints[-1] if endpoints else None},
        "adjacent_uid": adjacent,
        "candidates": [{"ticks_per_ms": str(ticks), "usable": extrema.usable,
                        "omitted": len(history.observations) - extrema.usable,
                        "residual_ms": extrema.result()}
                       for ticks, extrema in zip(CANDIDATE_TICKS_PER_MS, ranges)],
    }


def summarize(history):
    return local_summary(history.run, history.role, history.observations, history.paired_rows)


def _original_pair_offsets(audit):
    offsets = audit.get("admissible_row_offset_pairs")
    return (type(offsets) is list and len(offsets) == 1 and type(offsets[0]) is list
            and len(offsets[0]) == 2 and all(type(value) is int and value == 1 for value in offsets[0]))


def _pair_reference(number, rows):
    if type(number) is not int or not 0 <= number < len(rows):
        raise ValueError("zero-based original pair row required")
    return rows[number]


def _pair_status(counter_a, counter_b):
    if counter_a is None and counter_b is None:
        return "invalid_uid_both"
    if counter_a is None:
        return "invalid_uid_a"
    if counter_b is None:
        return "invalid_uid_b"
    return "valid_uid_pair"


def pair_summary(first, second, admitted):
    """Use admitted zero-based addresses, preserving trial order and every context/outcome."""
    history_feed.validate_parser_binding()
    a = _history(first.run, first.role, first.observations, first.paired_rows)
    b = _history(second.run, second.role, second.observations, second.paired_rows)
    if a.run != b.run or a.role != "local1" or b.role != "local2":
        raise ValueError("same-run ordered local1/local2 histories required")
    if getattr(admitted, "run", a.run) != a.run or not _original_pair_offsets(admitted.audit):
        raise ValueError("admitted original pair identity required")
    statuses = dict.fromkeys(PAIR_STATUSES, 0)
    overall = _Extrema()
    cells = {}
    digest = hashlib.sha256()
    records = 0
    for trial in admitted.trials:
        row_a = _pair_reference(trial.row_a, a.observations)
        row_b = _pair_reference(trial.row_b, b.observations)
        key = (trial.h, trial.a, trial.b, trial.x, trial.y)
        if type(trial.row) is not int or trial.row < 1 or any(type(value) is not int for value in key):
            raise ValueError("admitted pair row/context required")
        if not isinstance(trial.time_ms, Fraction):
            raise ValueError("exact admitted pair Unix-ms required")
        counter_a, counter_b = uid(row_a[4]), uid(row_b[4])
        status = _pair_status(counter_a, counter_b)
        origin = [a.run, trial.row, _origin(a.run, a.role, row_a), _origin(b.run, b.role, row_b)]
        cell = cells.setdefault(key, {"records": 0, "statuses": dict.fromkeys(PAIR_STATUSES, 0),
                                      "extrema": _Extrema()})
        records += 1
        statuses[status] += 1
        cell["records"] += 1
        cell["statuses"][status] += 1
        difference = None if status != "valid_uid_pair" else counter_b - counter_a
        if difference is not None:
            overall.add(difference, origin)
            cell["extrema"].add(difference, origin)
        _update_digest(digest, (origin, key, str(trial.time_ms), row_a, row_b,
                               row_a[0] in a.paired_rows, row_b[0] in b.paired_rows,
                               _text(counter_a), _text(counter_b), _text(difference)))
    return {
        "run": a.run, "pairs": records, "pair_counter_observations_sha256": digest.hexdigest(),
        "token_dictionaries": admitted.token_dictionaries, "statuses": statuses,
        "uid_difference": overall.counted(records),
        "cells": [{"context_outcome": list(key), "records": cell["records"],
                   "statuses": cell["statuses"],
                   "uid_difference": cell["extrema"].counted(cell["records"])}
                  for key, cell in sorted(cells.items())],
    }
