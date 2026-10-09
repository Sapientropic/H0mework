#!/usr/bin/env python3
"""Restore a registered edition view and its original frozen resource bytes."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path

import first_release as release
import source_view
from edition_release import EDITIONS


def restore_bundle(root: Path, output: Path, bundle: dict, artifacts: dict) -> dict:
    path = release.relative_path(bundle["artifact"])
    destination = release.repo_file(output, bundle["destination"])
    row = artifacts.get(path)
    if row is None:
        raise release.ReleaseError(f"Frozen resource is not registered: {path}")
    source_view.artifact_views(row)
    if destination.exists():
        raise release.ReleaseError(f"Frozen resource collides with the source view: {bundle['destination']}")
    if bundle.get("codec") not in {"gzip", "copy"}:
        raise release.ReleaseError("Frozen resource codec must be gzip or copy")
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_name(destination.name + ".partial")
    digest = hashlib.sha256()
    size = 0
    opener = gzip.open if bundle["codec"] == "gzip" else open
    try:
        with opener(root / path, "rb") as source, temporary.open("xb") as target:
            for block in iter(lambda: source.read(1 << 20), b""):
                size += len(block)
                if size > bundle["bytes"]:
                    raise release.ReleaseError("Frozen resource exceeds its registered original size")
                digest.update(block)
                target.write(block)
        if size != bundle["bytes"] or digest.hexdigest() != bundle["sha256"]:
            raise release.ReleaseError("Restored frozen resource differs from its original identity")
        temporary.replace(destination)
    finally:
        temporary.unlink(missing_ok=True)
    return {"artifact": path, "destination": bundle["destination"], "bytes": size,
            "sha256": digest.hexdigest(), "status": "verified"}


def restore(edition: str, view_name: str, output: str | Path) -> dict:
    root = release.ROOT
    map_path, schema = EDITIONS[edition]
    data = release.read_json(root / map_path)
    if data.get("schema") != schema:
        raise release.ReleaseError("Edition map schema differs")
    view = data.get("runtime_views", {}).get(view_name)
    if not isinstance(view, dict):
        raise release.ReleaseError(f"Unknown registered runtime view: {view_name}")
    original, _ = source_view.reconstruct(paths=view.get("paths", []), at=view["source_commit"])
    destination = release.new_output(root, output)
    identities = {}
    for name, raw in original.items():
        file = release.repo_file(destination, name)
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_bytes(raw)
        identities[name] = release.sha(raw)
    exported = release.read_json(root / release.EXPORT_MAP)
    artifacts = {row["path"]: row for row in exported["artifacts"]}
    resources = [restore_bundle(root, destination, bundle, artifacts)
                 for bundle in view.get("resource_bundles", [])]
    result = {"schema": "h0mework/edition-material-view@1", "edition": edition,
              "view": view_name, "source_commit": view["source_commit"],
              "claim_map_sha256": release.sha((root / map_path).read_bytes()),
              "source_files": identities, "resources": resources, "status": "verified",
              "scientific_recalculation": False}
    (destination / "view-identity.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edition", choices=EDITIONS, required=True)
    parser.add_argument("--view", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv)
    try:
        result = restore(args.edition, args.view, args.output)
    except (OSError, ValueError, KeyError, release.ReleaseError, source_view.ViewError) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, ensure_ascii=False))
        return 1
    print(json.dumps({key: value for key, value in result.items() if key != "source_files"}, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
