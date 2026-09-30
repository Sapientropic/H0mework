"""Publish receipt metadata without machine paths, retaining source identities.

The payload digest preserves every byte except registered runtime path labels
and declared receipt digest bindings. Original source digests remain unchanged.
"""
from __future__ import annotations

import hashlib
import json
import re

KIND = "relative-runtime-paths/v1"
PRIVATE_PATH = re.compile(r"^/(?:Users|home)/[^/]+/")
JSON_STRING = re.compile(r'"(?:[^"\\]|\\.)*"')
PROJECTS = {"Homework", "H0mework"}
PIN_TABLES = {"source_inputs", "input_sha256"}


class PublicationError(ValueError):
    pass


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def relative_path(value: str) -> str:
    if not PRIVATE_PATH.match(value):
        return value
    parts = value.split("/")
    for index, part in enumerate(parts):
        if part in PROJECTS:
            return "/".join(parts[index + 1:]) or "."
    raise PublicationError("Runtime path has no recognized project root")


def normalize_paths(raw: bytes) -> tuple[bytes, int]:
    """Relabel runtime metadata while preserving all other serialized bytes."""
    document = json.loads(raw)
    replacements = {}

    def walk(value, role=None):
        if isinstance(value, dict):
            keys = set()
            for key, item in value.items():
                new_key = key
                if PRIVATE_PATH.match(key):
                    if role not in PIN_TABLES:
                        raise PublicationError("Machine path outside an input identity table")
                    new_key = relative_path(key)
                    replacements[key] = new_key
                if new_key in keys:
                    raise PublicationError("Relative input path collision")
                keys.add(new_key)
                walk(item, key)
        elif isinstance(value, list):
            for item in value:
                walk(item, role)
        elif isinstance(value, str) and PRIVATE_PATH.match(value):
            if role not in {"root", "command"}:
                raise PublicationError("Machine path outside runtime metadata")
            relative = relative_path(value)
            replacements[value] = "." if role == "root" else relative

    walk(document)
    count = 0

    def replace(match):
        nonlocal count
        value = json.loads(match.group())
        if value not in replacements:
            return match.group()
        count += 1
        return json.dumps(replacements[value], ensure_ascii=False)

    result = JSON_STRING.sub(replace, raw.decode("utf-8")).encode("utf-8")
    return result, count


def digest_rewrite(raw: bytes, rule: dict, reverse=False) -> bytes:
    """Rewrite one declared JSON digest binding, with its field identity checked."""
    field = rule["field"]
    if len(field) != 2 or field[0] != "bindings" or not isinstance(field[1], str):
        raise PublicationError("Digest rewrite must identify a receipt binding")
    if any(not re.fullmatch(r"[0-9a-f]{64}", rule[k]) for k in ("source", "target")):
        raise PublicationError("Invalid receipt digest rewrite")
    value = json.loads(raw)
    for key in field:
        value = value[key]
    source, target = rule["source"], rule["target"]
    if reverse:
        source, target = target, source
    if value != source:
        raise PublicationError("Receipt digest binding differs from its declaration")
    old, new = json.dumps(source).encode(), json.dumps(target).encode()
    if raw.count(old) != 1:
        raise PublicationError("Receipt digest binding is not unique")
    return raw.replace(old, new)


def payload_bytes(raw: bytes, publication: dict) -> bytes:
    if publication.get("kind") != KIND:
        raise PublicationError("Unsupported publication transform")
    for rule in reversed(publication.get("digest_rewrites", [])):
        raw = digest_rewrite(raw, rule, reverse=True)
    return normalize_paths(raw)[0]


def verify_artifact(raw: bytes, row: dict, original: bytes | None = None):
    if sha(raw) != row["target_sha256"]:
        raise PublicationError("Published artifact digest differs")
    publication = row.get("publication")
    if publication is None:
        if sha(raw) != row["source_sha256"]:
            raise PublicationError("Original artifact digest differs")
        return
    normalized, count = normalize_paths(raw)
    if count:
        raise PublicationError("Published artifact still contains machine paths")
    if sha(payload_bytes(normalized, publication)) != publication["payload_sha256"]:
        raise PublicationError("Published receipt payload differs")
    if original is not None:
        if sha(original) != row["source_sha256"]:
            raise PublicationError("Private original digest differs")
        if sha(normalize_paths(original)[0]) != publication["payload_sha256"]:
            raise PublicationError("Private original and public payload differ")


def publish_outputs(outputs: dict[str, bytes], modules: list[dict],
                    artifacts: list[dict], original_module) -> dict:
    """Apply the publication transform to a freshly produced export plan."""
    by_source = {row["source"]: row for row in artifacts}
    changed = []
    occurrences = 0
    for row in artifacts:
        raw = outputs[row.get("path", row["target"])]
        normalized, count = normalize_paths(raw) if row["target"].endswith(".json") else (raw, 0)
        row.pop("publication", None)
        if count:
            row["publication"] = {"kind": KIND, "payload_sha256": sha(normalized)}
            changed.append(row)
            occurrences += count
        outputs[row["target"]] = normalized
        row["target_sha256"] = sha(normalized)
    # A verifier's binding refers to the public replay it actually reads.
    # Input identity tables keep the digests of the original calculation inputs.
    for row in changed:
        raw = outputs[row["target"]]
        document = json.loads(raw)
        for name, digest in document.get("bindings", {}).items():
            source = row["source"].rsplit("/", 1)[0] + "/" + name
            bound = by_source.get(source)
            if bound and digest == bound["source_sha256"] and digest != bound["target_sha256"]:
                rule = {"field": ["bindings", name], "source": digest,
                        "target": bound["target_sha256"]}
                raw = digest_rewrite(raw, rule)
                row["publication"].setdefault("digest_rewrites", []).append(rule)
        outputs[row["target"]] = raw
        row["target_sha256"] = sha(raw)
        verify_artifact(raw, row)
    by_target = {row["target"]: row for row in artifacts}
    changed_modules = 0
    for row in modules:
        raw = outputs[row["path"]]
        rewrites = []
        for resource in row.get("resource_rewrites", []):
            artifact = by_target[resource["target_artifact"]]
            source, target = resource["data_sha256"], artifact["target_sha256"]
            old = json.dumps(source).encode()
            if source != target and old in raw:
                if raw.count(old) != 1:
                    raise PublicationError("Module resource digest is not unique")
                raw = raw.replace(old, json.dumps(target).encode())
                rewrites.append({"source": source, "target": target})
        row.pop("resource_sha256_rewrites", None)
        row.pop("view_sha256", None)
        if rewrites:
            original = original_module(row)
            if sha(original) != row["source_sha256"]:
                raise PublicationError("Module source digest differs")
            view = original
            for rewrite in rewrites:
                old, new = json.dumps(rewrite["source"]).encode(), json.dumps(rewrite["target"]).encode()
                if view.count(old) != 1:
                    raise PublicationError("Original module resource digest is not unique")
                view = view.replace(old, new)
            row["resource_sha256_rewrites"] = rewrites
            row["view_sha256"] = sha(view)
            changed_modules += 1
        outputs[row["path"]] = raw
        row["target_sha256" if "target_sha256" in row else "transformed_sha256"] = sha(raw)
    return {"artifacts": len(changed), "machine_paths": occurrences,
            "resource_modules": changed_modules}
