#!/usr/bin/env python3
"""Check public claim identities and run isolated proof-package acceptance.

Identity checks read only this repository. Build and trust receipts are separate
executions in new ignored directories; this tool never edits the claim map or
interprets identity verification as scientific or publication readiness.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import subprocess
import sys
import time
import tomllib

from source_view import EXTERNAL, MODULE, ViewError, import_tokens, row_at, source_record

ROOT = Path(__file__).resolve().parents[1]
MAP = "docs/first-release-map.json"
EXPORT_MAP = "tools/export-map.json"
SCHEMA = "h0mework/first-release-map@1"
BUILD_COMPATIBILITY = "checks/build-configuration-compatibility.json"
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")


class ReleaseError(Exception):
    pass


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_json(path: Path) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise ReleaseError(f"Cannot read JSON {path.name}: {error}") from error
    if not isinstance(value, dict):
        raise ReleaseError(f"Expected JSON object: {path.name}")
    return value


def relative_path(value: str) -> str:
    if not isinstance(value, str) or not value or "\\" in value or ":" in value:
        raise ReleaseError(f"Unsafe repository path: {value!r}")
    path = PurePosixPath(value)
    if path.is_absolute() or any(part in {".", ".."} for part in value.split("/")):
        raise ReleaseError(f"Unsafe repository path: {value!r}")
    if any(ord(char) < 32 for char in value):
        raise ReleaseError(f"Unsafe repository path: {value!r}")
    return path.as_posix()


def repo_file(root: Path, value: str) -> Path:
    path = root / relative_path(value)
    resolved = path.resolve()
    if not resolved.is_relative_to(root.resolve()):
        raise ReleaseError(f"Path escapes repository: {value}")
    return path


def map_file(root: Path, value: Path | str) -> Path:
    path = Path(value)
    if path.is_absolute():
        try:
            value = path.relative_to(root.resolve()).as_posix()
        except ValueError as error:
            raise ReleaseError("Map must be inside this repository") from error
    return repo_file(root, str(value))


def module_name(value: str) -> str:
    if not isinstance(value, str) or not MODULE.fullmatch(value):
        raise ReleaseError(f"Invalid Lean module: {value!r}")
    return value


def module_path(value: str) -> str:
    return "Lean/" + module_name(value).replace(".", "/") + ".lean"


def declaration_name(value: dict | str) -> str:
    if isinstance(value, dict):
        name = value.get("qualified_name")
        if name is None:
            short = value.get("name", "")
            namespace = value.get("namespace", "")
            name = short if not namespace or short.startswith(namespace + ".") else namespace + "." + short
    else:
        name = value
    if (not isinstance(name, str) or not name or any(not part for part in name.split("."))
            or any(char.isspace() or ord(char) < 32 or char in '"\\/:;()[]{}«»' for char in name)):
        raise ReleaseError(f"Invalid declaration name: {name!r}")
    return name


def selected_claims(data: dict) -> list[dict]:
    claims = data.get("claims")
    if not isinstance(claims, list) or not claims:
        raise ReleaseError("Claim map needs a nonempty claims array")
    ids = set()
    selected = []
    for claim in claims:
        if not isinstance(claim, dict) or not isinstance(claim.get("id"), str) or not claim["id"]:
            raise ReleaseError("Every claim needs an id")
        if claim["id"] in ids:
            raise ReleaseError(f"Duplicate claim id: {claim['id']}")
        ids.add(claim["id"])
        if claim.get("selection_status") in {"excluded", "not-selected"} or claim.get("selected") is False:
            continue
        if not isinstance(claim.get("paper"), str) or not claim["paper"]:
            raise ReleaseError(f"Claim has no paper: {claim['id']}")
        selected.append(claim)
    if not selected:
        raise ReleaseError("Claim map contains no selected claims")
    return selected


def claim_entries(claims: list[dict]):
    for claim in claims:
        for role in ("producers", "direct_consumers", "resources"):
            entries = claim.get(role, [])
            if not isinstance(entries, list):
                raise ReleaseError(f"{claim['id']}.{role} must be an array")
            if role == "producers" and not entries:
                raise ReleaseError(f"Selected claim has no producer: {claim['id']}")
            for index, entry in enumerate(entries):
                if not isinstance(entry, dict):
                    raise ReleaseError(f"Invalid entry: {claim['id']}.{role}[{index}]")
                yield claim, role, index, entry


def entry_kind(role: str, entry: dict) -> str:
    kind = entry.get("kind", "artifact" if role == "resources" else "lean")
    if kind not in {"lean", "artifact"} or role == "resources" and kind != "artifact":
        raise ReleaseError(f"Invalid entry kind for {role}: {kind!r}")
    if role != "resources" and kind == "artifact" and str(entry.get("source_path", "")).endswith(".lean"):
        raise ReleaseError("Lean proof producers and consumers must retain their kernel gate")
    return kind


def load_maps(root: Path, path: Path | str = MAP) -> tuple[dict, dict]:
    data = read_json(map_file(root, path))
    if data.get("schema") != SCHEMA:
        raise ReleaseError(f"Unsupported claim map schema: {data.get('schema')!r}")
    exported = read_json(repo_file(root, EXPORT_MAP))
    for key in ("modules", "artifacts"):
        if not isinstance(exported.get(key), list):
            raise ReleaseError(f"Export map needs a {key} array")
    return data, exported


def export_indexes(exported: dict) -> dict[str, dict[str, list[dict]]]:
    indexes = {"modules": {}, "artifacts": {}}
    for kind in indexes:
        for row in exported[kind]:
            if not isinstance(row, dict):
                raise ReleaseError(f"Invalid {kind} export row")
            path = relative_path(row.get("path", row.get("target", "")))
            indexes[kind].setdefault(path, []).append(row)
    return indexes


def verify_map(root: Path = ROOT, path: Path | str = MAP, require_ready: bool = False,
               *, entry_keys: set[tuple[str, str, int]] | None = None) -> dict:
    data, exported = load_maps(root, path)
    indexes = export_indexes(exported)
    claims = selected_claims(data)
    rows, errors = [], []
    pending = {"identity": 0, "kernel": 0, "resources": 0, "runtime": 0}
    runtime_claims = set()
    for claim, role, index, entry in claim_entries(claims):
        if entry_keys is not None and (claim["id"], role, index) not in entry_keys:
            continue
        label = f"{claim['id']}.{role}[{index}]"
        result = {"entry": label, "identity": "pending"}
        try:
            kind = entry_kind(role, entry)
            result["kind"] = kind
            commit = entry.get("source_commit")
            if not isinstance(commit, str) or not HEX40.fullmatch(commit):
                raise ReleaseError("source_commit must be a complete 40-character Git revision")
            source = relative_path(entry.get("source_path"))
            public = entry.get("public")
            if public is None:
                pending["identity"] += 1
                if role == "resources":
                    pending["resources"] += 1
            else:
                if not isinstance(public, dict):
                    raise ReleaseError("public must be an object or null")
                public_path = relative_path(public.get("path"))
                index_kind = "artifacts" if kind == "artifact" else "modules"
                candidates = indexes[index_kind].get(public_path, [])
                if len(candidates) != 1:
                    raise ReleaseError(f"Expected one {index_kind} export row for {public_path}; found {len(candidates)}")
                row = candidates[0]
                if kind == "lean":
                    selected_source = source_record(row, source, commit)
                    if selected_source is None:
                        raise ReleaseError(f"Source path differs from export row: {public_path}")
                    row = selected_source
                revisions = set(row.get("source_revisions", [])) | {row.get("source_revision")}
                if commit not in revisions:
                    raise ReleaseError(f"Source revision is absent from export row: {public_path}")
                if source != row.get("source_path", row.get("source")):
                    raise ReleaseError(f"Source path differs from export row: {public_path}")
                if not HEX64.fullmatch(str(entry.get("source_sha256", ""))):
                    raise ReleaseError("Mapped entry needs source_sha256")
                if entry["source_sha256"] != row.get("source_sha256"):
                    raise ReleaseError(f"Source hash differs from export row: {public_path}")
                if entry.get("source_origin") != row.get("source_origin"):
                    raise ReleaseError(f"Source origin differs from export row: {public_path}")
                digest = public.get("sha256")
                if not isinstance(digest, str) or not HEX64.fullmatch(digest):
                    raise ReleaseError(f"Mapped entry needs public.sha256: {public_path}")
                if digest != row.get("target_sha256"):
                    raise ReleaseError(f"Public hash differs from export row: {public_path}")
                file = repo_file(root, public_path)
                if not file.is_file() or sha(file.read_bytes()) != digest:
                    raise ReleaseError(f"Public bytes differ from recorded hash: {public_path}")
                if kind == "lean":
                    module = module_name(public.get("module"))
                    if module != row.get("target") or public_path != module_path(module):
                        raise ReleaseError(f"Public module/path differs from export row: {public_path}")
                    if public.get("variant") != row.get("variant"):
                        raise ReleaseError(f"Public variant differs from export row: {public_path}")
                    declarations = entry.get("declarations")
                    if not isinstance(declarations, list) or not declarations:
                        raise ReleaseError(f"Mapped proof entry has no declaration roots: {public_path}")
                    for declaration in declarations:
                        declaration_name(declaration)
                result.update(identity="verified", public_path=public_path)
            verification = entry.get("verification", {})
            if kind == "lean":
                kernel = verification.get("kernel", "pending") if isinstance(verification, dict) else "pending"
                result["recorded_kernel"] = kernel
                if kernel not in {"passed", "verified"}:
                    pending["kernel"] += 1
            elif role == "resources" and public is not None:
                status = verification.get("identity", "pending") if isinstance(verification, dict) else verification
                if status not in {"passed", "verified", "mapped"}:
                    pending["resources"] += 1
            if claim.get("scientific_verification") is not None or kind == "artifact" and role != "resources":
                runtime_claims.add(claim["id"])
        except (ReleaseError, ViewError, OSError, TypeError) as error:
            result.update(identity="failed", error=str(error))
            errors.append({"entry": label, "error": str(error)})
        rows.append(result)
    runtime = []
    for claim in claims:
        if claim["id"] not in runtime_claims:
            continue
        verification = claim.get("scientific_verification", {})
        if not isinstance(verification, dict):
            errors.append({"entry": claim["id"], "error": "scientific_verification must be an object"})
            verification = {}
        status = verification.get("status", "pending")
        contracts = claim.get("runtime_contracts", [])
        contract_pending = []
        for contract in contracts:
            recorded = contract.get("verification", "pending")
            contract_status = recorded.get("status", "pending") if isinstance(recorded, dict) else recorded
            if contract_status not in {"passed", "verified"}:
                contract_pending.append(contract.get("id"))
        runtime.append({"claim": claim["id"], "recorded_status": status,
                        "check_ids": verification.get("check_ids", []), "pending_contract_ids": contract_pending})
        if status not in {"passed", "verified"} or contract_pending:
            pending["runtime"] += 1
    requirement_met = not errors and not any(pending.values())
    return {"schema": "h0mework/first-release-identity-check@1", "ok": not errors and (not require_ready or requirement_met),
            "identity_ready": not errors and pending["identity"] == 0, "require_ready": require_ready,
            "ready_requirement_met": requirement_met, "publication_readiness": "not_assessed",
            "kernel_status_scope": "recorded map status; this identity check does not execute Lean",
            "scientific_status_scope": "recorded map status; this identity check does not run scientific programs",
            "claims": len(claims), "entry_scope": "all selected entries" if entry_keys is None else "explicit proof-package entries",
            "mapped": sum(row["identity"] == "verified" for row in rows),
            "pending": pending, "errors": errors, "entries": rows, "scientific_verification": runtime}


def packages(data: dict, ids: list[str] | None = None) -> list[dict]:
    values = data.get("proof_packages")
    if not isinstance(values, list) or not values:
        raise ReleaseError("No proof_packages registered; nothing was built or audited")
    selected, seen = [], set()
    for package in values:
        if not isinstance(package, dict) or not isinstance(package.get("id"), str) or not package["id"]:
            raise ReleaseError("Every proof package needs an id")
        if package["id"] in seen:
            raise ReleaseError(f"Duplicate proof package: {package['id']}")
        seen.add(package["id"])
        if ids and package["id"] not in ids:
            continue
        module_name(package.get("lean_target"))
        if not isinstance(package.get("source_commit"), str) or not HEX40.fullmatch(package["source_commit"]):
            raise ReleaseError(f"Package needs a complete source_commit: {package['id']}")
        commits = package.get("source_commits", [package.get("source_commit")])
        if not isinstance(commits, list) or not commits or any(not isinstance(c, str) or not HEX40.fullmatch(c) for c in commits):
            raise ReleaseError(f"Package needs exact source_commit(s): {package['id']}")
        selected.append(package)
    if ids and set(ids) - seen:
        raise ReleaseError(f"Unknown proof packages: {sorted(set(ids) - seen)}")
    return selected


def package_entries(claims: list[dict], package: dict) -> list[tuple[dict, str, int, dict]]:
    commits = package.get("source_commits", [package["source_commit"]])
    ids = package.get("claim_ids")
    if ids is not None and (not isinstance(ids, list) or set(ids) - {c['id'] for c in claims}):
        raise ReleaseError(f"Invalid claim_ids for package: {package['id']}")
    selected = [item for item in claim_entries(claims) if entry_kind(item[1], item[3]) == "lean"
                and item[0]["paper"] == package.get("paper")
                and (ids is None or item[0]["id"] in ids) and item[3].get("source_commit") in commits]
    paths = None
    if "source_paths" in package:
        values = package["source_paths"]
        if not isinstance(values, list) or not values:
            raise ReleaseError(f"Invalid source_paths for package: {package['id']}")
        for path in values:
            if relative_path(path) != path or PurePosixPath(path).suffix != ".lean":
                raise ReleaseError(f"Package source_paths must be exact relative Lean paths: {package['id']}")
        paths = set(values)
        if len(paths) != len(values):
            raise ReleaseError(f"Duplicate source_paths for package: {package['id']}")
        missing = paths - {item[3].get("source_path") for item in selected}
        if missing:
            raise ReleaseError(f"Package source_paths have no selected same-epoch proof entries: {package['id']}: {sorted(missing)}")
        # Original audit and certification prefixes can define the same names
        # in independent environments; selection preserves both claim entries.
        selected = [item for item in selected if item[3]["source_path"] in paths]
    if not selected:
        raise ReleaseError(f"Package has no selected mapped proof entries: {package['id']}")
    if any(item[3].get("public") is None for item in selected):
        raise ReleaseError(f"Package still has pending public proof entries: {package['id']}")
    if paths is not None:
        for _, _, _, entry in selected:
            public = entry["public"]
            if not isinstance(public, dict):
                raise ReleaseError(f"Selected package source public must be an object: {entry['source_path']}")
            module_name(public.get("module"))
            declarations = entry.get("declarations")
            if not isinstance(declarations, list) or not declarations:
                raise ReleaseError(f"Selected package source has no declaration roots: {entry['source_path']}")
            for declaration in declarations:
                declaration_name(declaration)
    return selected


def proof_audit_entries(package: dict, entries: list) -> list:
    """Add explicitly registered named kernel controls without making claims.

    Anonymous examples remain in the package's compiled import closure. Only
    named declarations can also be roots of the complete metadata audit.
    """
    controls = package.get("controls", [])
    if not isinstance(controls, list):
        raise ReleaseError(f"Package controls must be an array: {package['id']}")
    if not controls:
        return entries
    result = list(entries)
    commits = package.get("source_commits", [package["source_commit"]])
    for index, control in enumerate(controls):
        label = f"{package['id']}.controls[{index}]"
        if not isinstance(control, dict) or entry_kind("controls", control) != "lean":
            raise ReleaseError(f"Kernel control must be a Lean entry: {label}")
        commit = control.get("source_commit")
        if not isinstance(commit, str) or not HEX40.fullmatch(commit) or commit not in commits:
            raise ReleaseError(f"Kernel control has no same-epoch package binding: {label}")
        path = relative_path(control.get("source_path"))
        if PurePosixPath(path).suffix != ".lean":
            raise ReleaseError(f"Kernel control needs an exact original Lean path: {label}")
        public = control.get("public")
        if not isinstance(public, dict):
            raise ReleaseError(f"Kernel control has no public owner: {label}")
        module = module_name(public.get("module"))
        if relative_path(public.get("path")) != module_path(module):
            raise ReleaseError(f"Kernel control public module/path differs: {label}")
        if (not HEX64.fullmatch(str(control.get("source_sha256", "")))
                or not HEX64.fullmatch(str(public.get("sha256", "")))):
            raise ReleaseError(f"Kernel control needs original and public byte identities: {label}")
        declarations = control.get("declarations")
        if not isinstance(declarations, list):
            raise ReleaseError(f"Kernel control needs an explicit declaration array: {label}")
        for declaration in declarations:
            declaration_name(declaration)
        if declarations:
            result.append(({"id": package["id"], "paper": package.get("paper")}, "controls", index, control))
    return result


def package_inputs(root: Path, exported: dict, package: dict, entries, *, parse_cache=None) -> dict:
    proof_audit_entries(package, entries)
    index = export_indexes(exported)["modules"]
    parse_cache = {} if parse_cache is None else parse_cache
    targets = exported.get("paper_aggregators", {})
    pending, files, reached = [package["lean_target"]], {}, set()
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        path = module_path(module)
        file = repo_file(root, path)
        if not file.is_file():
            raise ReleaseError(f"Missing public module: {module}")
        raw = file.read_bytes()
        digest = sha(raw)
        rows = index.get(path, [])
        if rows:
            if len(rows) != 1 or rows[0].get("target") != module or rows[0].get("target_sha256") != digest:
                raise ReleaseError(f"Import closure bytes differ from export map: {module}")
        elif targets.get(module) != path and exported.get("aggregator") != path:
            raise ReleaseError(f"Import closure module is not registered: {module}")
        files[path] = digest
        try:
            # Packages share many imports; every read is still hashed above.
            if digest not in parse_cache:
                parse_cache[digest] = [token[2] for token in import_tokens(raw.decode("utf-8"))]
            imports = parse_cache[digest]
        except (ViewError, UnicodeError) as error:
            raise ReleaseError(f"Cannot parse imports in {module}: {error}") from error
        pending.extend(dep for dep in imports if dep.split(".")[0] not in EXTERNAL)
    for _, _, _, entry in entries:
        if entry["public"]["module"] not in reached:
            raise ReleaseError(f"Selected proof module is not consumed by {package['id']}: {entry['public']['module']}")
    for control in package.get("controls", []):
        public = control["public"]
        if public["module"] not in reached:
            raise ReleaseError(f"Original kernel control is not consumed by {package['id']}: {public['module']}")
        rows = index.get(public["path"], [])
        record = (source_record(rows[0], control["source_path"], control["source_commit"])
                  if len(rows) == 1 else None)
        if (record is None or not row_at(record, control["source_commit"])
                or control.get("source_sha256") != record.get("source_sha256")
                or control.get("source_origin") != record.get("source_origin")
                or public.get("sha256") != rows[0].get("target_sha256")
                or public.get("variant") != rows[0].get("variant")):
            raise ReleaseError(f"Original kernel control identity differs from export row: {public['path']}")
    return {"files": files, "digest": sha(json.dumps(files, sort_keys=True).encode()), "modules": len(reached)}


def verify_build_configuration(root: Path, accepted_digest: str, *, data: dict, scopes: dict) -> dict:
    """Preserve signed package acceptance across explicitly bound library additions.

    The receipt's original Lake file stays authoritative. A changed file is
    admitted only through its retained snapshot and equivalent module compiler
    settings and resource inputs in the actual accepted proof scopes.
    """
    current_raw = repo_file(root, "Lean/lakefile.toml").read_bytes()
    if sha(current_raw) == accepted_digest:
        return {"mode": "exact", "lakefile_sha256": accepted_digest}
    compatibility = read_json(repo_file(root, BUILD_COMPATIBILITY))
    if compatibility.get("schema") != "h0mework/build-configuration-compatibility@1":
        raise ReleaseError("Build configuration compatibility schema differs")
    candidates = [row for row in compatibility.get("baselines", [])
                  if row.get("accepted_lakefile_sha256") == accepted_digest]
    if len(candidates) != 1:
        raise ReleaseError("Changed Lake configuration has no unique accepted baseline")
    baseline = candidates[0]
    if (not HEX40.fullmatch(str(baseline.get("source_commit", "")))
            or baseline.get("source_path") != "Lean/lakefile.toml"):
        raise ReleaseError("Build configuration baseline has no exact source identity")
    snapshot = baseline.get("snapshot", {})
    old_raw = repo_file(root, snapshot.get("path", "")).read_bytes()
    if sha(old_raw) != accepted_digest or snapshot.get("sha256") != accepted_digest:
        raise ReleaseError("Build configuration snapshot differs from the signed Lake file")
    commit = baseline["source_commit"]
    resolved = subprocess.run(["git", "--no-optional-locks", "-C", str(root), "rev-parse", "--verify",
                               "--end-of-options", commit + "^{commit}"], capture_output=True)
    if resolved.returncode or resolved.stdout.decode().strip() != commit:
        raise ReleaseError("Build compatibility baseline " + commit
                           + " is unavailable; restore this public repository's fixed baseline with: "
                           + "git fetch --no-tags origin " + commit)

    def fixed_blob(path):
        relative_path(path)
        result = subprocess.run(["git", "--no-optional-locks", "-C", str(root), "show", commit + ":" + path],
                                capture_output=True)
        if result.returncode:
            raise ReleaseError("Build compatibility input is unavailable at fixed baseline " + commit + ": " + path
                               + "; restore it with: git fetch --no-tags origin " + commit)
        return result.stdout

    if sha(fixed_blob(baseline["source_path"])) != accepted_digest:
        raise ReleaseError("Fixed Git baseline Lake file differs from the signed receipt")
    old, current = tomllib.loads(old_raw.decode()), tomllib.loads(current_raw.decode())
    ignored = {"defaultTargets", "lean_lib", "input_file"}
    if ({key: value for key, value in old.items() if key not in ignored}
            != {key: value for key, value in current.items() if key not in ignored}):
        raise ReleaseError("Signed package compiler or dependency settings changed")

    def append_only(before, after, label):
        if not isinstance(before, list) or not isinstance(after, list) or after[:len(before)] != before:
            raise ReleaseError("Build configuration is not an append-only extension: " + label)

    append_only(old.get("defaultTargets", []), current.get("defaultTargets", []), "defaultTargets")

    def named(values, label):
        result = {}
        for value in values:
            name = value.get("name")
            if not isinstance(name, str) or name in result:
                raise ReleaseError("Build configuration has an invalid or duplicate " + label)
            result[name] = value
        return result

    old_libs = named(old.get("lean_lib", []), "library")
    current_libs = named(current.get("lean_lib", []), "library")
    append_only(list(old_libs), list(current_libs), "lean_lib")

    def matches(module, glob):
        # The explicit Lake globs have the same semantics as ci_plan.matches.
        if glob.endswith(".+"):
            return module.startswith(glob[:-1])
        if glob.endswith(".*"):
            return module == glob[:-2] or module.startswith(glob[:-1])
        return module == glob

    def owners(module, libraries):
        return [lib for lib in libraries.values()
                if any(matches(module, glob) for glob in lib.get("globs", []))]

    def library_settings(lib):
        return {key: value for key, value in lib.items() if key not in {"name", "globs"}}

    promotions = {}
    for name, before in old_libs.items():
        after = current_libs[name]
        if library_settings(before) != library_settings(after):
            raise ReleaseError("Signed library settings or resource needs changed: " + name)
        old_globs, new_globs = before.get("globs", []), after.get("globs", [])
        if any(not isinstance(globs, list) or any(not isinstance(glob, str) for glob in globs)
               for globs in (old_globs, new_globs)):
            raise ReleaseError("Invalid Lake library globs: " + name)
        removed = set(old_globs) - set(new_globs)
        for module in sorted(removed):
            # A new paper can make an exact dependency from a historical
            # non-default library part of CI under the same effective options.
            module_name(module)
            original = owners(module, old_libs)
            current_owners = owners(module, current_libs)
            if (name in current.get("defaultTargets", []) or original != [before]
                    or len(current_owners) != 1):
                raise ReleaseError("Signed library glob removed without a unique promotion: " + module)
            target = current_owners[0]
            if (target["name"] in old_libs or target["name"] not in current.get("defaultTargets", [])
                    or module not in target.get("globs", []) or library_settings(target) != library_settings(before)):
                raise ReleaseError("Promoted module library options or resource needs differ: " + module)
            promotions[module] = (name, target["name"])
        append_only([glob for glob in old_globs if glob not in removed], new_globs, name + ".globs")
    old_resources = named(old.get("input_file", []), "resource input")
    current_resources = named(current.get("input_file", []), "resource input")
    for name, before in old_resources.items():
        if current_resources.get(name) != before:
            raise ReleaseError("Signed resource input definition changed: " + name)

    exported, claims = read_json(repo_file(root, EXPORT_MAP)), selected_claims(data)
    package_by_id = {package["id"]: package for package in packages(data)}
    if not scopes or not set(scopes) <= set(package_by_id):
        raise ReleaseError("Build compatibility needs the actual accepted proof packages")
    module_names, parse_cache = set(), {}
    for name, expected in scopes.items():
        package = package_by_id[name]
        actual = package_inputs(root, exported, package, package_entries(claims, package), parse_cache=parse_cache)
        if (actual["digest"] != expected.get("digest", expected.get("source_scope_sha256"))
                or actual["modules"] != expected.get("modules")):
            raise ReleaseError("Build compatibility proof source scope changed: " + name)
        for path in actual["files"]:
            if not path.startswith("Lean/") or not path.endswith(".lean"):
                raise ReleaseError("Build compatibility scope contains a non-module path")
            module_names.add(module_name(path[5:-5].replace("/", ".")))

    needed = set()
    for module in sorted(module_names):
        original, current_owners = owners(module, old_libs), owners(module, current_libs)
        if len(original) != 1 or len(current_owners) != 1:
            raise ReleaseError("Signed module library owner changed or became ambiguous: " + module)
        owner_pair = original[0]["name"], current_owners[0]["name"]
        if owner_pair[0] != owner_pair[1] and promotions.get(module) != owner_pair:
            raise ReleaseError("Signed module library owner changed: " + module)
        needed.update(original[0].get("needs", []))
    resource_bindings = baseline.get("resources", {})
    for name in sorted(needed):
        if name not in old_resources or name not in resource_bindings:
            raise ReleaseError("Signed resource input has no retained byte identity: " + name)
        path = posixpath.normpath(posixpath.join("Lean", old_resources[name]["path"]))
        reference = resource_bindings[name]
        if (reference.get("path") != path or not HEX64.fullmatch(str(reference.get("sha256", "")))
                or sha(repo_file(root, path).read_bytes()) != reference["sha256"]):
            raise ReleaseError("Signed resource input bytes changed: " + name)
        if sha(fixed_blob(path)) != reference["sha256"]:
            raise ReleaseError("Resource input differs from its fixed Git preservation baseline: " + name)
    return {"mode": "nondefault-promotion-equivalent" if promotions else "append-only-equivalent",
            "accepted_lakefile_sha256": accepted_digest,
            "current_lakefile_sha256": sha(current_raw), "source_commit": baseline["source_commit"],
            "modules": len(module_names), "resources": len(needed)}


def new_output(root: Path, value: Path | str) -> Path:
    output = Path(value)
    if output.is_absolute():
        try:
            value = output.relative_to(root.resolve()).as_posix()
        except ValueError as error:
            raise ReleaseError("Output must be in this repository's ignored .local directory") from error
    output = repo_file(root, str(value))
    local = root.resolve() / ".local"
    if not output.resolve().is_relative_to(local) or output.resolve() == local:
        raise ReleaseError("Output must be a new task directory below .local")
    if output.exists() or output.is_symlink():
        raise ReleaseError("Output directory already exists; choose a new run directory")
    ignored = subprocess.run(["git", "check-ignore", "--quiet", "--", output.relative_to(root).as_posix()], cwd=root)
    if ignored.returncode != 0:
        raise ReleaseError("Output is not ignored by this repository")
    output.mkdir(parents=True, exist_ok=False)
    return output


def settings(root: Path) -> dict:
    config = tomllib.loads(repo_file(root, "Lean/lakefile.toml").read_text())
    arguments = config.get("moreLeanArgs", [])
    if "--trust=0" not in arguments:
        raise ReleaseError("Lake package is missing its required --trust=0 gate")
    libraries = [{"name": lib.get("name"), "moreLeanArgs": lib.get("moreLeanArgs", [])}
                 for lib in config.get("lean_lib", [])]
    if not any("-DwarningAsError=true" in lib["moreLeanArgs"] for lib in libraries):
        raise ReleaseError("Lake libraries are missing warningAsError=true")
    return {"toolchain_pin": repo_file(root, "Lean/lean-toolchain").read_text().strip(),
            "package_moreLeanArgs": arguments, "package_weakLeanArgs": config.get("weakLeanArgs", []),
            "libraries": libraries}


def build_environment() -> dict:
    environment = dict(os.environ)
    override = environment.get("LEAN_NUM_THREADS")
    if override is not None:
        if not re.fullmatch(r"[1-9][0-9]*", override):
            raise ReleaseError("LEAN_NUM_THREADS must be a positive integer")
        return environment
    cpus = os.cpu_count() or 1
    if hasattr(os, "sched_getaffinity"):
        try:
            cpus = min(cpus, len(os.sched_getaffinity(0)))
        except OSError:
            pass
    try:
        memory = os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE")
    except (AttributeError, OSError, ValueError):
        memory = 0
    for path in ("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory/memory.limit_in_bytes"):
        try:
            limit = int(Path(path).read_text().strip())
            if limit > 0:
                memory = min(memory, limit) if memory > 0 else limit
        except (OSError, ValueError):
            pass
    # Generated proof rows use several GiB each; reserve half of a 16-GiB slot.
    memory_slots = max(1, memory // (16 * 1024**3)) if memory > 0 else 2
    environment["LEAN_NUM_THREADS"] = str(max(1, min(cpus, memory_slots, 8)))
    return environment


def snapshot(root: Path, path: Path | str, scopes: dict) -> dict:
    names = {"claim_map": map_file(root, path), "export_map": repo_file(root, EXPORT_MAP),
             "lakefile": repo_file(root, "Lean/lakefile.toml"), "toolchain": repo_file(root, "Lean/lean-toolchain"),
             "manifest": repo_file(root, "Lean/lake-manifest.json")}
    return {"sha256": {key: sha(file.read_bytes()) for key, file in names.items()},
            "package_inputs": {key: scope["digest"] for key, scope in scopes.items()}}


def run_process(command: list[str], root: Path, log: Path, environment: dict) -> dict:
    started = datetime.now(timezone.utc).isoformat()
    begin = time.monotonic()
    try:
        with log.open("w", encoding="utf-8") as stream:
            process = subprocess.run(command, cwd=root / "Lean", env=environment, stdout=stream, stderr=subprocess.STDOUT)
        code, error = process.returncode, None
    except OSError as exc:
        code, error = None, str(exc)
        log.write_text(str(exc) + "\n")
    return {"command": command, "cwd": "Lean", "started_at": started,
            "finished_at": datetime.now(timezone.utc).isoformat(), "elapsed_seconds": round(time.monotonic() - begin, 3),
            "exit_code": code, "error": error, "log": log.relative_to(root).as_posix()}


def compiled_targets(root: Path, targets: list[str]) -> dict:
    result = {}
    for target in targets:
        file = root / "Lean/.lake/build/lib/lean" / (target.replace(".", "/") + ".olean")
        result[target] = sha(file.read_bytes()) if file.is_file() else None
    return result


LEAN_AUDIT = r'''import Lean

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open Lean Elab Command
private def releaseName (value : String) : Name :=
  (value.splitOn ".").foldl (fun name part =>
    match part.toNat? with
    | some number => Name.num name number
    | none => Name.str name part) .anonymous

private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.type.getUsedConstantsAsSet
  if let some value := info.value? true then refs := refs ++ value.getUsedConstantsAsSet
  match info with
  | .defnInfo val => for name in val.all do refs := refs.insert name
  | .thmInfo val => for name in val.all do refs := refs.insert name
  | .opaqueInfo val => for name in val.all do refs := refs.insert name
  | .inductInfo val =>
      for name in val.all ++ val.ctors do refs := refs.insert name
  | .ctorInfo val => refs := (refs.insert val.name).insert val.induct
  | .recInfo val =>
      for name in val.all do refs := refs.insert name
      for rule in val.rules do
        refs := refs.insert rule.ctor
        refs := refs ++ rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return refs

run_cmd do
  let env ← getEnv
  let roots : List (String × String) := __ROOTS__
  for (decl, owner) in roots do
    let name := releaseName decl
    unless (env.checked.get.find? name).isSome do throwError "MISSING_DECLARATION {name}"
    let some index := env.getModuleIdxFor? name | throwError "MISSING_DECLARATION_MODULE {name}"
    unless env.header.moduleNames[index]! == releaseName owner do
      throwError "WRONG_DECLARATION_MODULE {name} expected={owner} actual={env.header.moduleNames[index]!}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending := roots.toArray.map (fun item => releaseName item.1)
  let mut seen : NameHashSet := {}
  let mut axioms : NameSet := {}
  let mut edges := 0
  while let some name := pending.back? do
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name | throwError "UNCHECKED_CONSTANT {name}"
    if info.isUnsafe || info.isPartial then throwError "UNSAFE_PARTIAL {name}"
    -- Collect each complete type/value and metadata edge once.
    let refs := completeRefs info
    edges := edges + refs.size
    for dep in refs do
      unless seen.contains dep do pending := pending.push dep
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAPPROVED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "MISSING_CONSTANT_VALUE {name}"
    | _ => pure ()
  let report := Json.mkObj [
    ("token", toJson "__TOKEN__"), ("roots", toJson roots.length),
    ("constants", toJson seen.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
'''


def audit_source(package: dict, entries) -> tuple[str, dict]:
    roots = {}
    for claim, role, _, entry in proof_audit_entries(package, entries):
        module = entry["public"]["module"]
        for declaration in entry["declarations"]:
            name = declaration_name(declaration)
            if name in roots and roots[name] != module:
                raise ReleaseError(f"Package mixes different owners for {name}: {package['id']}")
            roots[name] = module
    if not roots:
        raise ReleaseError(f"No declaration roots to audit: {package['id']}")
    scope = {"package": package["id"], "source_commits": package.get("source_commits", [package['source_commit']]),
             "lean_target": package["lean_target"], "declarations": roots,
             "closure": "complete type/value, mutual declarations, inductives, constructors and recursor metadata",
             "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"]}
    token = sha(json.dumps(scope, sort_keys=True).encode())
    scope["token"] = token
    pairs = ",\n    ".join(f"({json.dumps(name, ensure_ascii=False)}, {json.dumps(module)})" for name, module in sorted(roots.items()))
    source = "import " + package["lean_target"] + "\n" + LEAN_AUDIT
    source = source.replace("__ROOTS__", "[" + pairs + "]").replace("__TOKEN__", token)
    return source, scope


def trust_report(log: str, scope: dict) -> dict:
    matches = re.findall(r"FIRST_RELEASE_TRUST (\{[^\n]+\})", log)
    reports = [json.loads(text) for text in matches]
    matching = [report for report in reports if report.get("token") == scope["token"]]
    if len(matching) != 1:
        raise ReleaseError("Lean did not emit exactly one audit result for this scope")
    report = matching[0]
    if (report.get("roots") != len(scope["declarations"]) or report.get("unsafe") != 0
            or report.get("partial") != 0 or report.get("full_metadata") is not True
            or not isinstance(report.get("constants"), int) or report["constants"] < report["roots"]
            or not isinstance(report.get("axioms"), list) or set(report["axioms"]) - set(scope["allowed_axioms"])):
        raise ReleaseError("Lean audit report does not satisfy the registered trust contract")
    return report


def run_trust_audit(index: int, package: dict, entries: list, root: Path,
                    directory: Path, configured: dict, environment: dict) -> dict:
    run = {"package": package["id"], "status": "failed", "exit_code": None}
    try:
        source, scope = audit_source(package, entries)
        file = directory / f"audit-{index:03d}.lean"
        file.write_text(source, encoding="utf-8")
        scope["source_sha256"] = sha(source.encode())
        scope["public_modules"] = sorted({item[3]['public']['module'] for item in proof_audit_entries(package, entries)})
        (directory / f"audit-{index:03d}-scope.json").write_text(json.dumps(scope, indent=2) + "\n")
        flags = configured["package_moreLeanArgs"] + configured["package_weakLeanArgs"]
        flags = list(dict.fromkeys(flags + ["--trust=0", "-DwarningAsError=true"]))
        relative = "../" + file.relative_to(root).as_posix()
        log = directory / f"audit-{index:03d}.log"
        run.update(run_process(["lake", "env", "lean", "--root=..", *flags, relative], root, log, environment))
        run["audit_scope"] = scope
        if run["exit_code"] == 0:
            run["audit"] = trust_report(log.read_text(), scope)
            run["status"] = "passed"
    except (ReleaseError, OSError, ValueError, TypeError) as error:
        run["error"] = str(error)
    return run


def execute(kind: str, root: Path, path: Path | str, output: Path | str, ids: list[str] | None = None) -> dict:
    data, exported = load_maps(root, path)
    selected = packages(data, ids)
    entries = {p["id"]: package_entries(selected_claims(data), p) for p in selected}
    keys = {(claim['id'], role, index) for package_entries_ in entries.values()
            for claim, role, index, _ in package_entries_}
    identity = verify_map(root, path, entry_keys=keys)
    if identity["errors"]:
        raise ReleaseError(f"Selected package identity check failed: {identity['errors']}")
    parse_cache = {}
    scopes = {p["id"]: package_inputs(root, exported, p, entries[p["id"]], parse_cache=parse_cache) for p in selected}
    configured = settings(root)
    before = snapshot(root, path, scopes)
    environment = build_environment()
    directory = new_output(root, output)
    targets = list(dict.fromkeys(p["lean_target"] for p in selected))
    result = {"schema": f"h0mework/first-release-{kind}@1", "kind": kind, "ok": False,
              "input_identity": before, "settings": configured,
              "identity_scope": {"packages": [p['id'] for p in selected], "proof_entries": len(keys)},
              "cache": {"kind": "existing_workspace_cache", "clean_clone": False,
                        "build_directory_preexisted": (root / "Lean/.lake/build").is_dir(),
                        "lean_num_threads": environment["LEAN_NUM_THREADS"],
                        "compiled_targets_before": compiled_targets(root, targets)},
              "packages": selected, "results": [], "publication_readiness": "not_assessed"}
    if kind == "build":
        result["results"].append(run_process(["lake", "build", *targets], root, directory / "build.log", environment))
    else:
        preflight = run_process(["lake", "--no-build", "build", *targets], root, directory / "preflight.log", environment)
        preflight["scope"] = "validate existing built targets against current source; no build permitted"
        result["preflight"] = preflight
        if preflight["exit_code"] == 0:
            jobs = min(len(selected), int(environment["LEAN_NUM_THREADS"]), 8)
            result["cache"]["trust_jobs"] = jobs
            # Each epoch has its own Lean environment and output; keep receipt order stable.
            def audit(item):
                index, package = item
                return run_trust_audit(index, package, entries[package["id"]], root,
                                       directory, configured, environment)
            with ThreadPoolExecutor(max_workers=jobs) as workers:
                result["results"] = list(workers.map(audit, enumerate(selected, 1)))
    try:
        after_scopes = {p["id"]: package_inputs(root, exported, p, entries[p["id"]], parse_cache=parse_cache) for p in selected}
        result["input_identity_after"] = snapshot(root, path, after_scopes)
        result["inputs_unchanged"] = before == result["input_identity_after"]
    except (ReleaseError, OSError) as error:
        result.update(inputs_unchanged=False, input_error=str(error))
    if kind == "build":
        result["ok"] = result["results"][0]["exit_code"] == 0 and result["inputs_unchanged"]
    else:
        result["ok"] = (result["preflight"]["exit_code"] == 0 and len(result["results"]) == len(selected)
                        and all(run["status"] == "passed" for run in result["results"]) and result["inputs_unchanged"])
    result["receipt"] = (directory / "result.json").relative_to(root).as_posix()
    result["compiled_targets_after"] = compiled_targets(root, targets)
    (directory / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


def main(argv=None, *, root: Path = ROOT) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    verify = commands.add_parser("verify-map", help="verify public identities; no Lean execution")
    verify.add_argument("--map", default=MAP)
    verify.add_argument("--require-ready", action="store_true", help="reject identity, resource, recorded kernel or scientific runtime pending entries")
    for name in ("build", "trust"):
        command = commands.add_parser(name)
        command.add_argument("--map", default=MAP)
        command.add_argument("--output", required=True, type=Path, help="new ignored .local run directory")
        command.add_argument("--package", action="append", help="explicit proof-package id; default: all registered packages")
    args = parser.parse_args(argv)
    try:
        if args.command == "verify-map":
            result = verify_map(root, args.map, args.require_ready)
        else:
            result = execute(args.command, root, args.map, args.output, args.package)
    except (ReleaseError, OSError, ValueError, TypeError, KeyError) as error:
        result = {"ok": False, "error": str(error), "publication_readiness": "not_assessed"}
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
