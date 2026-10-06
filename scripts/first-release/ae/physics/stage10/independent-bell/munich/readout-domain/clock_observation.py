"""CEM/context plus next recorded clock; no physical successor or loss label is inferred."""
from collections import Counter
from fractions import Fraction
import hashlib
import json

import history_feed

CUTS_MS = tuple(Fraction(n) for n in (100, 500, 1000, 2000, 3000, 5000,
                                     10000, 20000, 40000, 80000, 160000, 320000, 640000))


def clock(value):
    try:
        return history_feed.schema.timestamp(value, "Unix_ms")
    except (TypeError, ValueError):
        return None


def observations(history):
    for index, before in enumerate(history.observations):
        after = history.observations[index + 1] if index + 1 < len(history.observations) else None
        origin = (history.run, history.role, before[0], before[-1],
                  None if after is None else after[0], None if after is None else after[-1])
        current = (before[2], before[3], before[5], before[0] in history.paired_rows,
                   before[6], before[7])
        if after is None:
            yield origin, current, None, "right_censored", None
            continue
        following = (after[2], after[3], after[5], after[0] in history.paired_rows,
                     after[6], after[7])
        start, end = clock(before[1]), clock(after[1])
        if start is None or end is None:
            yield origin, current, following, "invalid_clock_retained", None
        else:
            delta = end - start
            status = "negative_clock_retained" if delta < 0 else "zero_clock_retained" if delta == 0 else "positive"
            yield origin, current, following, status, str(delta)


def summarize(history):
    stream = hashlib.sha256()
    status_counts = Counter()
    groups = {}
    for item in observations(history):
        origin, current, following, status, delta = item
        stream.update(json.dumps(item, ensure_ascii=False, separators=(",", ":")).encode("utf-8") + b"\n")
        status_counts[status] += 1
        key = json.dumps((current, following), ensure_ascii=False, separators=(",", ":"))
        group = groups.setdefault(key, {"current": list(current),
                                       "following": None if following is None else list(following),
                                       "records": 0, "statuses": Counter(), "cdf_counts": [0] * len(CUTS_MS)})
        group["records"] += 1
        group["statuses"][status] += 1
        if status in ("positive", "zero_clock_retained"):
            value = Fraction(delta)
            for position, cutoff in enumerate(CUTS_MS):
                group["cdf_counts"][position] += int(value <= cutoff)
    return {"run": history.run, "role": history.role,
            "records": len(history.observations), "ordered_clock_observations_sha256": stream.hexdigest(),
            "statuses": dict(sorted(status_counts.items())), "cuts_ms": list(map(str, CUTS_MS)),
            "groups": [dict(group, statuses=dict(sorted(group["statuses"].items())))
                       for _, group in sorted(groups.items())]}


def pair_summary(first, second, admitted):
    history_feed.schema.require(admitted.audit["admissible_row_offset_pairs"] == [[1, 1]], "clock_pair_identity")
    rows_a, rows_b = tuple(observations(first)), tuple(observations(second))
    stream = hashlib.sha256()
    cells, statuses = {}, Counter()
    for trial in admitted.trials:
        a, b = rows_a[trial.row_a], rows_b[trial.row_b]
        item = (trial.row, (trial.h, trial.a, trial.b, trial.x, trial.y), a, b)
        stream.update(json.dumps(item, ensure_ascii=False, separators=(",", ":")).encode("utf-8") + b"\n")
        key = (trial.h, trial.a, trial.b, trial.x, trial.y)
        cell = cells.setdefault(key, {"context_outcome": list(key), "records": 0,
                                      "local1_statuses": Counter(), "local2_statuses": Counter(),
                                      "local1_cdf_counts": [0] * len(CUTS_MS),
                                      "local2_cdf_counts": [0] * len(CUTS_MS)})
        cell["records"] += 1
        for role, observation in (("local1", a), ("local2", b)):
            status, delta = observation[-2:]
            statuses[role + ":" + status] += 1
            cell[role + "_statuses"][status] += 1
            if status in ("positive", "zero_clock_retained"):
                value = Fraction(delta)
                for index, cutoff in enumerate(CUTS_MS):
                    cell[role + "_cdf_counts"][index] += int(value <= cutoff)
    return {"run": first.run, "pairs": len(admitted.trials), "cuts_ms": list(map(str, CUTS_MS)),
            "pair_clock_observations_sha256": stream.hexdigest(),
            "token_dictionaries": admitted.token_dictionaries,
            "statuses": dict(sorted(statuses.items())),
            "cells": [dict(cell, local1_statuses=dict(sorted(cell["local1_statuses"].items())),
                           local2_statuses=dict(sorted(cell["local2_statuses"].items())))
                      for _, cell in sorted(cells.items())]}
