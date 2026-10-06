"""Publish receipt metadata without machine paths, retaining source identities.

The payload digest preserves every byte except registered runtime path labels
and declared receipt digest bindings. Original source digests remain unchanged.
"""
from __future__ import annotations

import hashlib
import json
import re

KIND = "relative-runtime-paths/v1"
DECLARED_KIND = "declared-runtime-paths/v2"
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


def declared_runtime_paths(raw: bytes, declarations: list[dict]) -> tuple[bytes, int]:
    """Replace registered JSON string spans, preserving numbers and other fields."""
    text = raw.decode("utf-8")
    json.loads(text)
    replacements = {}
    keys = {}
    for row in declarations:
        pointer, relative = row["pointer"], row["relative"]
        if not isinstance(pointer, str) or (pointer and not pointer.startswith("/")):
            raise PublicationError("Runtime path needs an exact JSON pointer")
        if not isinstance(relative, str) or re.search(r"/(?:Users|home)/[^/]+/", relative):
            raise PublicationError("Runtime replacement contains a machine address")
        identity = (pointer, row.get("key_index"))
        table = keys if "key_index" in row else replacements
        if identity in table and table[identity] != relative:
            raise PublicationError("Runtime location has competing addresses")
        table[identity] = relative
    edits = []
    found = set()
    length = len(text)
    def space(index):
        while index < length and text[index].isspace():
            index += 1
        return index
    def quoted(index, pointer, key_index=None):
        match = JSON_STRING.match(text, index)
        if match is None:
            raise PublicationError("Runtime JSON string cannot be located")
        value = json.loads(match.group())
        identity = (pointer, key_index)
        table = replacements if key_index is None else keys
        if identity in table:
            relative = table[identity]
            found.add(identity)
            if value != relative:
                edits.append((match.start(), match.end(), json.dumps(relative, ensure_ascii=False)))
        return value, match.end()
    def visit(index, pointer):
        index = space(index)
        character = text[index]
        if character == '"':
            return quoted(index, pointer)[1]
        if character == '{':
            index = space(index + 1)
            count = 0
            while text[index] != '}':
                key, index = quoted(index, pointer, count)
                index = space(index)
                if text[index] != ':':
                    raise PublicationError("Runtime JSON object separator differs")
                child = pointer + '/' + key.replace('~', '~0').replace('/', '~1')
                index = space(visit(index + 1, child))
                count += 1
                if text[index] == ',':
                    index = space(index + 1)
                else:
                    break
            return index + 1
        if character == '[':
            index = space(index + 1)
            count = 0
            while text[index] != ']':
                index = space(visit(index, pointer + '/' + str(count)))
                count += 1
                if text[index] == ',':
                    index = space(index + 1)
                else:
                    break
            return index + 1
        end = index
        while end < length and text[end] not in ',]} \r\n\t':
            end += 1
        return end
    if declarations:
        visit(0, '')
    expected = set(keys) | set(replacements)
    if found != expected:
        raise PublicationError("Declared runtime string location is absent or not a string")
    for begin, end, value in sorted(edits, reverse=True):
        text = text[:begin] + value + text[end:]
    def unique_keys(pairs):
        if len({key for key, value in pairs}) != len(pairs):
            raise PublicationError("Relative runtime input path collision")
        return dict(pairs)
    json.loads(text, object_pairs_hook=unique_keys)
    return text.encode("utf-8"), len(edits)


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
    if publication.get("kind") not in {KIND, DECLARED_KIND}:
        raise PublicationError("Unsupported publication transform")
    for rule in reversed(publication.get("digest_rewrites", [])):
        raw = digest_rewrite(raw, rule, reverse=True)
    if publication.get("kind") == DECLARED_KIND:
        return declared_runtime_paths(raw, publication.get("runtime_paths", []))[0]
    return normalize_paths(raw)[0]


def verify_artifact(raw: bytes, row: dict, original: bytes | None = None):
    if sha(raw) != row["target_sha256"]:
        raise PublicationError("Published artifact digest differs")
    publication = row.get("publication")
    if publication is None:
        if sha(raw) != row["source_sha256"]:
            raise PublicationError("Original artifact digest differs")
        return
    normalized, count = (declared_runtime_paths(raw, publication.get("runtime_paths", []))
                         if publication.get("kind") == DECLARED_KIND else normalize_paths(raw))
    if count:
        raise PublicationError("Published artifact still contains machine paths")
    if sha(payload_bytes(normalized, publication)) != publication["payload_sha256"]:
        raise PublicationError("Published receipt payload differs")
    if original is not None:
        if sha(original) != row["source_sha256"]:
            raise PublicationError("Private original digest differs")
        original_payload = (declared_runtime_paths(original, publication.get("runtime_paths", []))[0]
                            if publication.get("kind") == DECLARED_KIND else normalize_paths(original)[0])
        if sha(original_payload) != publication["payload_sha256"]:
            raise PublicationError("Private original and public payload differ")


def publish_outputs(outputs: dict[str, bytes], modules: list[dict],
                    artifacts: list[dict], original_module, runtime_declarations: dict | None = None) -> dict:
    """Apply the publication transform to a freshly produced export plan."""
    by_source = {row["source"]: row for row in artifacts}
    changed = []
    occurrences = 0
    for row in artifacts:
        raw = outputs[row.get("path", row["target"])]
        declarations = (runtime_declarations or {}).get((row.get("source_revision"), row["source"]))
        normalized, count = (declared_runtime_paths(raw, declarations) if declarations is not None
                             else normalize_paths(raw) if row["target"].endswith(".json") else (raw, 0))
        row.pop("publication", None)
        if count:
            row["publication"] = {"kind": DECLARED_KIND if declarations is not None else KIND,
                                  "payload_sha256": sha(normalized)}
            if declarations is not None:
                row["publication"]["runtime_paths"] = declarations
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
