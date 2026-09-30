#!/usr/bin/env python3
"""Compare a freshly produced receipt against its frozen export, field by field.

Numeric strings, floats and ints compare by exact value; a small whitelist of
volatile bookkeeping keys (wall-clock timings, host names, absolute output
paths) is ignored. Everything else must be exactly equal. Usage:

  compare_receipt.py <frozen.json> <produced.json> [--ignore-key key ...]
"""
from __future__ import annotations

import argparse
import json
import sys

DEFAULT_IGNORED = {"seconds", "elapsed", "duration", "timestamp", "host",
                   "hostname", "wall_time", "walltime", "real_time"}


def compare(frozen, produced, ignored, path=""):
    if isinstance(frozen, dict):
        if not isinstance(produced, dict):
            return [f"{path}: expected object, got {type(produced).__name__}"]
        errors = []
        for key, value in frozen.items():
            if key in ignored:
                continue
            if key not in produced:
                errors.append(f"{path}/{key}: missing in produced receipt")
                continue
            errors.extend(compare(value, produced[key], ignored, f"{path}/{key}"))
        for key in produced:
            if key not in frozen and key not in ignored:
                errors.append(f"{path}/{key}: unexpected new key in produced receipt")
        return errors
    if isinstance(frozen, list):
        if not isinstance(produced, list) or len(produced) != len(frozen):
            return [f"{path}: list length/content mismatch"]
        return [e for i, (a, b) in enumerate(zip(frozen, produced))
                for e in compare(a, b, ignored, f"{path}[{i}]")]
    if frozen != produced:
        return [f"{path}: {frozen!r} != {produced!r}"]
    return []


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("frozen")
    parser.add_argument("produced")
    parser.add_argument("--ignore-key", action="append", default=[])
    args = parser.parse_args(argv)
    ignored = DEFAULT_IGNORED | set(args.ignore_key)
    frozen = json.loads(open(args.frozen).read())
    produced = json.loads(open(args.produced).read())
    errors = compare(frozen, produced, ignored)
    if errors:
        for line in errors[:50]:
            print("FAIL", line)
        print(f"{len(errors)} differences")
        return 1
    print(f"OK {args.produced} matches frozen {args.frozen}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
