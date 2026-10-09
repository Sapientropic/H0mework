"""Exact stride certificates for the complete original UID history.

For UID_i = b + c*n_i with integer b, positive integer c and strictly
increasing integer n_i, the admissible c are exactly the positive divisors
of the adjacent-difference gcd.  A fixed b adds (UID_0-b) divisible by c.
Bezout and universal divisibility certify that gcd without repeating its
producer's Euclidean search.  The integer family assigns no physical clock.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

import history_feed


SCHEMA = "stage10-bell-uid-stride-certificate/v1"
FAMILY = "UID_i=b+c*n_i; b in Z; c in Z_>0; n_i in Z; n_(i+1)>n_i"
STATUSES = ("positive", "zero", "negative", "invalid")


def _bytes(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def _update(digest, value):
    digest.update(_bytes(value) + b"\n")


def _history(history):
    history_feed.validate_parser_binding()
    if type(history) is not history_feed.RecordHistory:
        raise TypeError("complete original RecordHistory required")
    rows = history.observations
    if (type(rows) is not tuple or type(history.run) is not str or
            type(history.paired_rows) is not frozenset or
            any(type(number) is not int or not 1 <= number <= len(rows)
                for number in history.paired_rows)):
        raise ValueError("original history identity required")
    for index, row in enumerate(rows, 1):
        if (type(row) is not tuple or len(row) != len(history_feed.FIELDS) or
                type(row[0]) is not int or row[0] != index or type(row[4]) is not str or
                type(row[-1]) is not str or re.fullmatch(r"[0-9a-f]{64}", row[-1]) is None):
            raise ValueError("complete original row and raw SHA256 required")
    return rows


def _uid(value):
    if re.fullmatch(r"[0-9]+", value) is None:
        return None
    try:
        return int(value)
    except ValueError:
        return None


def _checked_uid(value):
    # This recognizer is separate from the producer's regular expression.
    if not value or any(not 48 <= ord(char) <= 57 for char in value):
        return None
    try:
        return int(value)
    except ValueError:
        return None


def _edge(rows, values, index):
    first, second = rows[index], rows[index + 1]
    delta = None if values[index] is None or values[index + 1] is None else values[index + 1] - values[index]
    status = "invalid" if delta is None else "positive" if delta > 0 else "negative" if delta < 0 else "zero"
    return {"left_row": first[0], "right_row": second[0],
            "left_raw_sha256": first[-1], "right_raw_sha256": second[-1],
            "delta": None if delta is None else str(delta), "status": status}


def source_bindings():
    root = Path(__file__).resolve().parents[6]
    paths = (Path(__file__).resolve(), Path(history_feed.__file__).resolve(), history_feed.PARSER_PATH)
    return [{"path": str(path.relative_to(root)),
             "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for path in paths]


def _binding(history, rows, values):
    records, uids, edges = hashlib.sha256(), hashlib.sha256(), hashlib.sha256()
    counts = dict.fromkeys(STATUSES, 0)
    for row in rows:
        records.update(f"{row[0]}:{row[-1]}\n".encode("ascii"))
        _update(uids, [row[0], row[4], row[-1]])
    for index in range(len(rows) - 1):
        edge = _edge(rows, values, index)
        counts[edge["status"]] += 1
        _update(edges, edge)
    return {"run": history.run, "role": history.role, "records": len(rows),
            "paired_records": len(history.paired_rows),
            "unpaired_records": len(rows) - len(history.paired_rows),
            "adjacent_records": max(0, len(rows) - 1),
            "uid_records": {"valid": sum(value is not None for value in values),
                            "invalid": sum(value is None for value in values)},
            "adjacent_uid": counts,
            "complete_observations_sha256": hashlib.sha256(_bytes(rows)).hexdigest(),
            "original_row_sequence_sha256": records.hexdigest(),
            "uid_row_sequence_sha256": uids.hexdigest(),
            "complete_adjacent_difference_sequence_sha256": edges.hexdigest(),
            "raw_endpoints": {"first": [rows[0][0], rows[0][4], rows[0][-1]] if rows else None,
                              "last": [rows[-1][0], rows[-1][4], rows[-1][-1]] if rows else None},
            "source_bindings": source_bindings()}


def _extended_euclid(first, second):
    r0, r1, s0, s1, t0, t1 = first, second, 1, 0, 0, 1
    while r1:
        quotient = r0 // r1
        r0, r1 = r1, r0 - quotient * r1
        s0, s1 = s1, s0 - quotient * s1
        t0, t1 = t1, t0 - quotient * t1
    return r0, s0, t0


def certify(history):
    rows = _history(history)
    values = tuple(_uid(row[4]) for row in rows)
    binding = _binding(history, rows, values)
    resolved = len(rows) >= 2 and binding["adjacent_uid"]["positive"] == len(rows) - 1
    gcd, weights = 0, {}
    if resolved:
        for index in range(len(rows) - 1):
            delta = values[index + 1] - values[index]
            if gcd == 1:
                break
            if gcd == 0:
                gcd, weights = delta, {index: 1}
            elif delta % gcd:
                gcd, first, second = _extended_euclid(gcd, delta)
                weights = {key: weight * first for key, weight in weights.items() if weight * first}
                if second:
                    weights[index] = second
    witness = [{**_edge(rows, values, index), "coefficient": str(weight)}
               for index, weight in sorted(weights.items())]
    return {"schema": SCHEMA, **binding,
            "status": "stride_divisibility_certified" if resolved else "unresolved",
            "gcd": str(gcd) if resolved else None, "bezout_witness": witness,
            "family": FAMILY,
            "family_admissible_strides": "positive_integer_divisors_of_gcd" if resolved else "unresolved",
            "conditional_positive_integer_stride_unique": resolved and gcd == 1,
            "conditional_positive_integer_stride": "1" if resolved and gcd == 1 else None,
            "all_original_records_retained": True, "unpaired_and_flagged_records_retained": True,
            "physical_sample_clock_identified": False, "actual_integer_encoder_identified": False,
            "actual_hardware_uniquely_identified": False, "controller_advance": False}


def _integer(value):
    if type(value) is not str:
        raise ValueError("canonical integer certificate required")
    try:
        parsed = int(value)
    except ValueError as error:
        raise ValueError("canonical integer certificate required") from error
    if str(parsed) != value:
        raise ValueError("canonical integer certificate required")
    return parsed


def verify_certificate(certificate, history):
    """Check the original inputs, Bezout identity and every adjacent divisibility."""
    if type(certificate) is not dict:
        raise TypeError("UID stride certificate required")
    rows = _history(history)
    values = tuple(_checked_uid(row[4]) for row in rows)
    binding = _binding(history, rows, values)
    if any(certificate.get(key) != value for key, value in binding.items()):
        raise ValueError("UID certificate differs from the complete original history")
    resolved = len(rows) >= 2 and all(values[i] is not None and values[i + 1] is not None
                                    and values[i] < values[i + 1] for i in range(len(rows) - 1))
    witness = certificate.get("bezout_witness")
    if type(witness) is not list:
        raise ValueError("original adjacent Bezout witness required")
    gcd = None
    if resolved:
        gcd = _integer(certificate.get("gcd"))
        if gcd <= 0 or not witness or any((values[i + 1] - values[i]) % gcd
                                        for i in range(len(rows) - 1)):
            raise ValueError("candidate gcd does not divide every original UID difference")
        total, seen = 0, set()
        for item in witness:
            if type(item) is not dict or type(item.get("left_row")) is not int:
                raise ValueError("original adjacent Bezout witness required")
            index = item["left_row"] - 1
            if not 0 <= index < len(rows) - 1 or index in seen:
                raise ValueError("distinct original adjacent Bezout addresses required")
            coefficient = _integer(item.get("coefficient"))
            if not coefficient or item != {**_edge(rows, values, index), "coefficient": str(coefficient)}:
                raise ValueError("Bezout term differs from its original row restriction")
            total += coefficient * (values[index + 1] - values[index])
            seen.add(index)
        if total != gcd:
            raise ValueError("original UID differences fail the Bezout identity")
    elif certificate.get("gcd") is not None or witness:
        raise ValueError("unresolved history cannot carry a filtered stride certificate")
    expected = {"schema": SCHEMA, "status": "stride_divisibility_certified" if resolved else "unresolved",
                "family": FAMILY,
                "family_admissible_strides": "positive_integer_divisors_of_gcd" if resolved else "unresolved",
                "conditional_positive_integer_stride_unique": resolved and gcd == 1,
                "conditional_positive_integer_stride": "1" if resolved and gcd == 1 else None,
                "all_original_records_retained": True, "unpaired_and_flagged_records_retained": True,
                "physical_sample_clock_identified": False, "actual_integer_encoder_identified": False,
                "actual_hardware_uniquely_identified": False, "controller_advance": False}
    if any(certificate.get(key) != value for key, value in expected.items()):
        raise ValueError("UID certificate claim differs from its integer-family scope")
    if set(certificate) != set(binding) | set(expected) | {"gcd", "bezout_witness"}:
        raise ValueError("unexpected UID certificate fields")
    return True


def divides_stride_iff(certificate, history, stride, *, offset=None):
    """Exact existence of this integer affine realization, with optional fixed b."""
    verify_certificate(certificate, history)
    if certificate["status"] != "stride_divisibility_certified":
        raise ValueError("complete strictly increasing UID history is unresolved")
    if type(stride) is not int or stride <= 0 or (offset is not None and type(offset) is not int):
        raise ValueError("positive integer stride and optional integer offset required")
    divides = _integer(certificate["gcd"]) % stride == 0
    return divides and (offset is None or (_checked_uid(history.observations[0][4]) - offset) % stride == 0)
