"""Original paired next-record clocks with their complete joint observation.

The next raw local row and next original pair-file row are distinct observers.
Their join uses admitted source addresses, never timestamp agreement.  UID
differences keep their integer coordinate; only Unix-ms enters the fixed CDF.
"""
from collections import Counter
from fractions import Fraction
import hashlib
from itertools import product
import json

import clock_observation as clocks
import counter_mapping as counters
import history_feed as history


CUTS_MS = clocks.CUTS_MS
CONTEXTS = tuple(product((0, 1), repeat=5))
TUPLE_FIELDS = ("pair_origin", "next_raw_local1", "next_raw_local2", "next_admitted_pair", "next_raw_join")


def _require(condition, reason):
    if not condition:
        raise ValueError(reason)


def _history(value, role):
    _require(type(value) is history.RecordHistory and value.role == role,
             "original ordered RecordHistory required")
    _require(type(value.observations) is tuple and all(
        type(row) is tuple and len(row) == 9 and type(row[0]) is int and row[0] == index
        and all(type(row[k]) is str for k in (1, 2, 3, 4, 6, 7, 8))
        and (type(row[5]) is str or row[5] is None)
        for index, row in enumerate(value.observations, 1)), "complete original local row sequence required")
    _require(all(type(row) is int and 1 <= row <= len(value.observations) for row in value.paired_rows),
             "original paired-view row addresses required")
    return value


def _intake(first, second, admitted):
    history.validate_parser_binding()
    first, second = _history(first, "local1"), _history(second, "local2")
    _require(first.run == second.run and type(admitted) is history.schema.AdmittedRun and admitted.run == first.run,
             "same-run original admitted pair source required")
    offsets = admitted.audit.get("admissible_row_offset_pairs")
    _require(type(offsets) is list and len(offsets) == 1 and type(offsets[0]) is list
             and len(offsets[0]) == 2 and all(type(n) is int and n == 1 for n in offsets[0]),
             "original zero-based pair-address dictionary required")
    _require(type(admitted.audit.get("pair_records")) is int
             and admitted.audit["pair_records"] == len(admitted.trials), "all original admitted pair records required")
    used_a, used_b = set(), set()
    for number, trial in enumerate(admitted.trials, 1):
        _require(type(trial) is history.schema.Trial and type(trial.row) is int and trial.row == number
                 and type(trial.time_ms) is Fraction, "original ordered pair-file trial required")
        _require(all(type(bit) is int and bit in (0, 1) for bit in (trial.h, trial.a, trial.b, trial.x, trial.y)),
                 "original binary pair context/outcome required")
        for address, rows, used in ((trial.row_a, first.observations, used_a),
                                    (trial.row_b, second.observations, used_b)):
            _require(type(address) is int and 0 <= address < len(rows) and address not in used,
                     "unique zero-based original pair reference required")
            used.add(address)
    return first, second, tuple(admitted.trials)


def _origin(run, trial):
    return (run, trial.row, str(trial.time_ms), trial.row_a, trial.row_b,
            trial.h, trial.a, trial.b, trial.x, trial.y)


def _delta(current, following, parser, label):
    if following is None:
        return "right_censored", None
    left, right = parser(current), parser(following)
    if left is None or right is None:
        return "invalid_" + label + "_retained", None
    value = right - left
    status = "negative_" + label + "_retained" if value < 0 else "zero_" + label + "_retained" if value == 0 else "positive"
    return status, str(value) if label == "clock" else value


def _transition(value, current, following):
    unix_status, unix_delta = _delta(current[1], None if following is None else following[1], clocks.clock, "clock")
    uid_status, uid_delta = _delta(current[4], None if following is None else following[4], counters.uid, "uid")
    return (value.run, value.role, current, current[0] in value.paired_rows,
            following, None if following is None else following[0] in value.paired_rows,
            unix_status, unix_delta, uid_status, uid_delta)


def _events(first, second, trials):
    maps = ({trial.row_a: trial.row for trial in trials}, {trial.row_b: trial.row for trial in trials})
    origins = {trial.row: _origin(first.run, trial) for trial in trials}
    for index, trial in enumerate(trials):
        current_a, current_b = first.observations[trial.row_a], second.observations[trial.row_b]
        next_a = first.observations[trial.row_a + 1] if trial.row_a + 1 < len(first.observations) else None
        next_b = second.observations[trial.row_b + 1] if trial.row_b + 1 < len(second.observations) else None
        following = trials[index + 1] if index + 1 < len(trials) else None
        admitted_a = None if following is None else first.observations[following.row_a]
        admitted_b = None if following is None else second.observations[following.row_b]
        next_admitted = (None if following is None else origins[following.row],
                         _transition(first, current_a, admitted_a), _transition(second, current_b, admitted_b))
        row_a, row_b = maps[0].get(trial.row_a + 1), maps[1].get(trial.row_b + 1)
        common = origins[row_a] if row_a is not None and row_a == row_b else None
        immediate = None if following is None else common is not None and common[1] == following.row
        raw_join = (row_a, row_b, common, immediate)
        yield (origins[trial.row], _transition(first, current_a, next_a),
               _transition(second, current_b, next_b), next_admitted, raw_join)


def observations(first, second, admitted):
    first, second, trials = _intake(first, second, admitted)
    yield from _events(first, second, trials)


def _update(digest, value):
    digest.update(json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8") + b"\n")


def _local_summary(value, pair_count):
    digest = hashlib.sha256()
    for item in local_observations(value):
        _update(digest, item)
    return {"run": value.run, "role": value.role, "records": len(value.observations),
            "paired_view_records": len(value.paired_rows),
            "unpaired_view_records": len(value.observations) - len(value.paired_rows),
            "joined_pair_records": pair_count, "original_unpaired_records": len(value.observations) - pair_count,
            "ordered_full_rows_sha256": digest.hexdigest()}


def local_observations(value):
    """Keep every original local row, including rows absent from all pairs."""
    _require(type(value) is history.RecordHistory, "original RecordHistory required")
    value = _history(value, value.role)
    for row in value.observations:
        unix, uid = clocks.clock(row[1]), counters.uid(row[4])
        yield (value.run, value.role, row, row[0] in value.paired_rows,
               None if unix is None else str(unix), uid)


def _stats():
    return {"records": 0, "local1_unix_statuses": Counter(), "local2_unix_statuses": Counter(),
            "local1_uid_statuses": Counter(), "local2_uid_statuses": Counter(),
            "unix_outer_statuses": Counter(), "uid_outer_statuses": Counter(),
            "joint_cdf_eligible": 0, "joint_cdf_counts": [[0] * len(CUTS_MS) for _ in CUTS_MS]}


def _observe(stats, first, second):
    stats["records"] += 1
    for role, sample in (("local1", first), ("local2", second)):
        stats[role + "_unix_statuses"][sample[6]] += 1
        stats[role + "_uid_statuses"][sample[8]] += 1
    stats["unix_outer_statuses"][first[6] + "|" + second[6]] += 1
    stats["uid_outer_statuses"][first[8] + "|" + second[8]] += 1
    allowed = ("positive", "zero_clock_retained")
    if first[6] in allowed and second[6] in allowed:
        stats["joint_cdf_eligible"] += 1
        a, b = Fraction(first[7]), Fraction(second[7])
        for i, cutoff_a in enumerate(CUTS_MS):
            if a <= cutoff_a:
                for j, cutoff_b in enumerate(CUTS_MS):
                    stats["joint_cdf_counts"][i][j] += int(b <= cutoff_b)


def _encode(stats):
    return {key: dict(sorted(value.items())) if isinstance(value, Counter) else value
            for key, value in stats.items()}


def _join_status(item):
    if item[1][4] is None or item[2][4] is None:
        return "right_censored"
    a, b, common, immediate = item[4]
    if common is not None:
        return "same_next_admitted" if immediate else "same_other_admitted"
    if a is not None and b is not None:
        return "different_admitted_pairs"
    return "one_or_both_unpaired"


def pair_summary(first, second, admitted):
    first, second, trials = _intake(first, second, admitted)
    relations = {name: _stats() for name in ("next_raw", "next_admitted")}
    joins, digest = Counter(), hashlib.sha256()
    cells = {key: {"context_outcome": list(key), "records": 0,
                   "relations": {name: _stats() for name in relations}, "next_raw_join_statuses": Counter()}
             for key in CONTEXTS}
    for item in _events(first, second, trials):
        _update(digest, item)
        cell = cells[item[0][5:]]
        cell["records"] += 1
        join = _join_status(item)
        joins[join] += 1
        cell["next_raw_join_statuses"][join] += 1
        samples = {"next_raw": item[1:3], "next_admitted": item[3][1:]}
        for name, (left, right) in samples.items():
            _observe(relations[name], left, right)
            _observe(cell["relations"][name], left, right)
    return {"schema": "stage10-joint-clock-observation/v1", "run": first.run, "pairs": len(trials),
            "cuts_ms": list(map(str, CUTS_MS)), "token_dictionaries": admitted.token_dictionaries,
            "ordered_paired_joint_observations_sha256": digest.hexdigest(), "tuple_fields": list(TUPLE_FIELDS),
            "histories": [_local_summary(value, len(trials)) for value in (first, second)],
            "relations": {name: _encode(value) for name, value in relations.items()},
            "next_raw_join_statuses": dict(sorted(joins.items())),
            "cells": [dict(cell, relations={name: _encode(value) for name, value in cell["relations"].items()},
                           next_raw_join_statuses=dict(sorted(cell["next_raw_join_statuses"].items())))
                      for cell in cells.values()],
            "all_original_local_rows_committed": True, "all_original_pairs_observed": True,
            "next_admitted_pair_definition": "next original pair-file row; not next raw local row",
            "paired_joint_record_observer": True, "paired_clock_joint_cdf_preserved": True,
            "uid_physical_unit_identified": False, "source_physical_successor_identified": False,
            "physical_clock_source_joint_square_certified": False, "fit_executed": False,
            "new_confidence_budget_spent": False, "controller_advance": False}
