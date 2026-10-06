"""Independent dictionary-parser clock observer and integer CDF counts."""
import bisect
from collections import Counter
from fractions import Fraction
import hashlib
import json

import history_feed_independent

CUTS = (100, 500, 1000, 2000, 3000, 5000, 10000, 20000, 40000, 80000, 160000, 320000, 640000)


def number(text):
    try:
        return history_feed_independent.parser.timestamp(text.strip())
    except (AttributeError, TypeError, ValueError):
        return None


def observations(run, role, rows, selected):
    result = []
    for position in range(len(rows)):
        current = rows[position]
        following = rows[position + 1] if position + 1 < len(rows) else None
        origin = (run, role, current[0], current[8],
                  following[0] if following else None, following[8] if following else None)
        before_context = (current[2], current[3], current[5], current[0] in selected, current[6], current[7])
        after_context = ((following[2], following[3], following[5], following[0] in selected,
                          following[6], following[7]) if following else None)
        delta = None
        if following is None:
            status = "right_censored"
        else:
            left, right = number(current[1]), number(following[1])
            if left is None or right is None:
                status = "invalid_clock_retained"
            else:
                delta = str(right - left)
                status = ("negative_clock_retained" if right < left else
                          "zero_clock_retained" if right == left else "positive")
        result.append((origin, before_context, after_context, status, delta))
    return tuple(result)


def summarize(run, role, rows, selected):
    observed = observations(run, role, rows, selected)
    groups, statuses = {}, Counter()
    digest = hashlib.sha256()
    for record in observed:
        _, current, following, status, delta = record
        digest.update(json.dumps(record, ensure_ascii=False, separators=(",", ":")).encode("utf-8") + b"\n")
        statuses[status] += 1
        key = json.dumps((current, following), ensure_ascii=False, separators=(",", ":"))
        group = groups.setdefault(key, [current, following, Counter(), [0] * (len(CUTS) + 1)])
        group[2][status] += 1
        if status in ("positive", "zero_clock_retained"):
            group[3][bisect.bisect_left(CUTS, Fraction(delta))] += 1
    result = []
    for _, (current, following, counts, bins) in sorted(groups.items()):
        cdf, total = [], 0
        for n in bins[:-1]:
            total += n
            cdf.append(total)
        result.append({"current": list(current), "following": list(following) if following else None,
                       "records": sum(counts.values()), "statuses": dict(sorted(counts.items())), "cdf_counts": cdf})
    return {"run": run, "role": role, "records": len(rows), "ordered_clock_observations_sha256": digest.hexdigest(),
            "statuses": dict(sorted(statuses.items())), "cuts_ms": list(map(str, CUTS)), "groups": result}


def pair_summary(run, rows_a, rows_b, selected_a, selected_b, admitted):
    history_feed_independent.parser.demand(admitted.audit["admissible_row_offset_pairs"] == [[1, 1]], "clock_pair_identity")
    left = observations(run, "local1", rows_a, selected_a)
    right = observations(run, "local2", rows_b, selected_b)
    cells, statuses, digest = {}, Counter(), hashlib.sha256()
    for trial in admitted.trials:
        a, b = left[trial.row_a], right[trial.row_b]
        key = (trial.h, trial.a, trial.b, trial.x, trial.y)
        digest.update(json.dumps((trial.row, key, a, b), ensure_ascii=False, separators=(",", ":")).encode("utf-8") + b"\n")
        cell = cells.setdefault(key, [0, [0] * (len(CUTS) + 1), [0] * (len(CUTS) + 1), Counter(), Counter()])
        cell[0] += 1
        for index, (role, observation) in enumerate((("local1", a), ("local2", b)), 1):
            status, delta = observation[3:]
            statuses[role + ":" + status] += 1
            cell[index + 2][status] += 1
            if status in ("positive", "zero_clock_retained"):
                cell[index][bisect.bisect_left(CUTS, Fraction(delta))] += 1
    output = []
    for key, (count, a_bins, b_bins, a_status, b_status) in sorted(cells.items()):
        item = {"context_outcome": list(key), "records": count,
                "local1_statuses": dict(sorted(a_status.items())), "local2_statuses": dict(sorted(b_status.items()))}
        for role, bins in (("local1", a_bins), ("local2", b_bins)):
            cdf, total = [], 0
            for n in bins[:-1]:
                total += n
                cdf.append(total)
            item[role + "_cdf_counts"] = cdf
        output.append(item)
    return {"run": run, "pairs": len(admitted.trials), "cuts_ms": list(map(str, CUTS)),
            "pair_clock_observations_sha256": digest.hexdigest(), "token_dictionaries": admitted.token_dictionaries,
            "statuses": dict(sorted(statuses.items())), "cells": output}
