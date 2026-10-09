#!/usr/bin/env python3
"""Run the existing isolated proof acceptance for an explicit new edition.

The first-release executable and its defaults retain their original contract.
This entry selects only a separately registered claim map and schema.
"""
from __future__ import annotations

import argparse

import first_release

EDITIONS = {
    "second": ("docs/second-edition-map.json", "h0mework/second-edition-map@1"),
    "low-energy": ("docs/low-energy-release-map.json", "h0mework/low-energy-release-map@1"),
}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, add_help=False)
    parser.add_argument("--edition", choices=EDITIONS, required=True)
    parser.add_argument("--paper", help="build or audit the paper's separately registered epoch packages")
    args, remaining = parser.parse_known_args(argv)
    path, schema = EDITIONS[args.edition]
    if args.paper:
        if not remaining or remaining[0] not in {"build", "trust"}:
            parser.error("--paper requires build or trust")
        data = first_release.read_json(first_release.ROOT / path)
        if data.get("schema") != schema:
            parser.error("edition map schema differs")
        selected = [package["id"] for package in first_release.packages(data)
                    if package.get("paper") == args.paper]
        if not selected:
            parser.error("paper has no registered packages in this edition")
        packages = argparse.ArgumentParser(add_help=False)
        packages.add_argument("--package", action="append")
        requested, _ = packages.parse_known_args(remaining)
        if requested.package:
            if not set(requested.package) <= set(selected):
                parser.error("explicit package does not belong to the selected paper")
        else:
            remaining += [argument for package in selected for argument in ("--package", package)]
    original = first_release.MAP, first_release.SCHEMA
    try:
        first_release.MAP, first_release.SCHEMA = path, schema
        return first_release.main(remaining)
    finally:
        first_release.MAP, first_release.SCHEMA = original


if __name__ == "__main__":
    raise SystemExit(main())
