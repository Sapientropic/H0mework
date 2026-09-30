#!/usr/bin/env python3
"""Compare a freshly recomputed evidence receipt with its frozen export.

Comparison recursively omits the fields listed in VOLATILE, including timing,
host paths and revision metadata, then compares all remaining fields. Pinned
source identity is checked separately by source_view.py and the export map.
"""
import json
import sys

VOLATILE = {"elapsed_seconds", "elapsed", "seconds", "duration", "timestamp",
            "time", "host", "hostname", "cwd", "root", "repository", "revision"}


def normalize(value):
    if isinstance(value, dict):
        return {k: normalize(v) for k, v in value.items() if k not in VOLATILE}
    if isinstance(value, list):
        return [normalize(v) for v in value]
    return value


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: compare_evidence.py FRESH FROZEN", file=sys.stderr)
        return 2
    fresh = normalize(json.loads(open(sys.argv[1]).read()))
    frozen = normalize(json.loads(open(sys.argv[2]).read()))
    if fresh == frozen:
        print(f"receipt matches frozen evidence: {sys.argv[2]}")
        return 0
    keys = sorted(set(fresh) | set(frozen)) if isinstance(fresh, dict) else []
    diff = [k for k in keys if fresh.get(k) != frozen.get(k)]
    print(f"evidence mismatch in {diff or '<value>'}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
