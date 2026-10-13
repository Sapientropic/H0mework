#!/usr/bin/env python3
"""Stage a revision-pinned whole-ledger selection without changing public owners.

This is the multi-epoch intake of the existing incremental export mechanism:
fixed Git bodies, recursive import-layout reuse, publication transformations,
and source_view's exact inverse. It does not apply the resulting export-map rows.

Input: h0mework/whole-ledger-selection@1, with selections containing a full
source_commit, original-path roots, and original-path artifacts. Output plan.json
contains assignments keyed by commit:path, full additions/artifacts rows,
reused owners, and explicit revision/alias updates. New public bytes are under
stage/<row.path>; exact effective inputs are under raw/<source_sha256>.

An optional h0mework/whole-ledger-providers@1 document contains providers with
source_commit, source_path, source_sha256, provider (relative to that document),
and source_origin. Providers must bind their bytes to a fixed Git source or an
exact receipt pointer; a working-tree file is never a historical-source fallback.
"""
from __future__ import annotations

import argparse
import collections
import copy
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import posixpath
import re
import subprocess
import sys

import publication as pub
import source_view as sv

ROOT = Path(__file__).resolve().parents[1]
SELECTION_SCHEMA = "h0mework/whole-ledger-selection@1"
PROVIDER_SCHEMA = "h0mework/whole-ledger-providers@1"
PLAN_SCHEMA = "h0mework/whole-ledger-export-plan@1"
REVISION = re.compile(r"[0-9a-f]{40}\Z")
DIGEST = re.compile(r"[0-9a-f]{64}\Z")
INHERITED_FIELDS = ("local_instance_names", "proof_body_rewrites", "build_adaptations", "suggestion_name_exclusions")
PRIVATE_PATH = re.compile(r'/(?:Users|home|home2)/[^/\s"\\]+/[^\s"\\:;]*|/var/folders/[^\s"\\:;]*')
UNDECLARED_PATH = re.compile(r'/(?:Users|home|home2|tmp|Volumes)/[^\s"\\:;]+|/var/folders/[^\s"\\:;]*')


class ExportError(ValueError):
    pass


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def write_json(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, sort_keys=True, indent=1) + "\n")
    temporary.replace(path)


def source_key(commit: str, path: str) -> str:
    if not isinstance(commit, str) or not REVISION.fullmatch(commit):
        raise ExportError("source_commit must be a full lower-case Git SHA")
    return commit + ":" + sv.source_path(path)


def component(value: str) -> str:
    # Same path-to-module spelling as the fixed-cap plan_incremental driver.
    value = "".join(part[:1].upper() + part[1:] for part in value.split("-"))
    value = re.sub("[^A-Za-z0-9_]", "_", value)
    return "N" + value if value[:1].isdigit() else value


def original_module(path: str) -> str:
    name = path[5:-5].replace("/", ".") if path.startswith("Lean/") else ""
    return name if sv.MODULE.fullmatch(name) else "file:" + path


def load_selection(path: Path) -> dict:
    value = json.loads(path.read_bytes())
    if not isinstance(value, dict) or value.get("schema") != SELECTION_SCHEMA:
        raise ExportError("Unsupported whole-ledger selection schema")
    selections = value.get("selections")
    if not isinstance(selections, list) or not selections:
        raise ExportError("selections must be a nonempty list")
    for selection in selections:
        if not isinstance(selection, dict):
            raise ExportError("Each selection must be an object")
        commit = selection.get("source_commit")
        for field in ("roots", "artifacts"):
            rows = selection.get(field, [])
            if not isinstance(rows, list):
                raise ExportError(field + " must be a list of original paths")
            for source in rows:
                source_key(commit, source)
                if field == "roots" and not source.endswith(".lean"):
                    raise ExportError("A production root must be a Lean source: " + source)
        if not selection.get("roots") and not selection.get("artifacts"):
            raise ExportError("An empty selection has no acceptance scope")
    return value


class FixedGit:
    """The migration GitSource batch reader, restricted to full commit inputs."""

    def __init__(self, repository: Path):
        self.repository = repository
        self.process = None
        self.trees = {}
        self.blobs = {}

    def git(self, *args: str) -> bytes:
        result = subprocess.run(["git", "-C", str(self.repository), *args],
                                capture_output=True, check=False)
        if result.returncode:
            raise ExportError("Fixed Git operation failed: " + args[0])
        return result.stdout

    def tree(self, commit: str):
        source_key(commit, "identity")
        if commit not in self.trees:
            resolved = self.git("rev-parse", "--verify", "--end-of-options", commit + "^{commit}").decode().strip()
            if resolved != commit:
                raise ExportError("Git did not resolve the declared exact commit")
            entries = {}
            for entry in self.git("ls-tree", "-rz", commit).split(b"\0"):
                if entry:
                    header, path = entry.split(b"\t", 1)
                    mode, kind, oid = header.split()
                    entries[path.decode()] = (mode, kind, oid.decode())
            self.trees[commit] = entries
        return self.trees[commit]

    def exists(self, commit: str, path: str) -> bool:
        source_key(commit, path)
        return path in self.tree(commit)

    def read(self, commit: str, path: str) -> bytes:
        key = source_key(commit, path)
        record = self.tree(commit).get(path)
        if record is None:
            raise ExportError("Missing fixed Git source: " + key)
        mode, kind, oid = record
        if mode not in (b"100644", b"100755") or kind != b"blob":
            raise ExportError("Fixed source must be a regular Git file: " + key)
        if oid not in self.blobs:
            if self.process is None:
                self.process = subprocess.Popen(
                    ["git", "-C", str(self.repository), "cat-file", "--batch"],
                    stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
            self.process.stdin.write((oid + "\n").encode())
            self.process.stdin.flush()
            header = self.process.stdout.readline()
            match = re.fullmatch(rb"([0-9a-f]{40}|[0-9a-f]{64}) blob ([0-9]+)\n", header)
            if match is None or match[1].decode() != oid:
                raise ExportError("Invalid fixed Git blob response: " + key)
            raw = self.process.stdout.read(int(match[2]))
            if len(raw) != int(match[2]) or self.process.stdout.read(1) != b"\n":
                raise ExportError("Truncated fixed Git source: " + key)
            self.blobs[oid] = raw
        return self.blobs[oid]

    def close(self):
        if self.process is not None:
            self.process.stdin.close()
            self.process.stdout.close()
            try:
                code = self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait()
                raise ExportError("Fixed Git reader did not close")
            self.process = None
            if code:
                raise ExportError("Fixed Git reader failed")


# Vendored unchanged from the audited migration tools/migrate.py. The exception
# class and masking helper are bound to the tracked source_view implementation.
MigrationError = ExportError
mask_comments_and_strings = sv.mask_comments_and_strings


def include_tokens(text: str) -> list[tuple[int, int, str]]:
    """Recognize only standalone include_str literals, never general Lean terms."""
    masked = mask_comments_and_strings(text)
    result = []
    for keyword in re.finditer(r"(?<![\w'.])(?:include_str|include_bin)(?![\w'])", masked):
        if keyword.group() == "include_bin":
            raise MigrationError("Resource relocation blocked: include_bin is unsupported")
        following = re.search(r"\S", masked[keyword.end():])
        begin = keyword.end() + following.start() if following else len(text)
        literal = re.compile(r'"([^"\\\r\n]*)"').match(text, begin)
        if literal is None:
            raise MigrationError("Resource relocation blocked: include_str needs an unescaped relative string literal")
        end = literal.end()
        line_end = text.find("\n", end)
        tail = masked[end:line_end if line_end >= 0 else len(text)].strip()
        if tail and tail[0] not in "),;]}":
            raise MigrationError("Resource relocation blocked: compound include_str path is unsupported")
        if not tail:
            # A path operator or a more-indented term on the next line is not
            # the literal-only form; never rewrite one fragment of that term.
            next_token = re.search(r"\S", masked[end:])
            if next_token:
                position = end + next_token.start()
                original_line = masked[masked.rfind("\n", 0, keyword.start()) + 1:keyword.start()]
                next_line = masked[masked.rfind("\n", 0, position) + 1:position]
                indentation = len(original_line) - len(original_line.lstrip())
                if masked[position] in "/+.$" or (len(next_line) > indentation and masked[position] not in "),;]}"):
                    raise MigrationError("Resource relocation blocked: continued include_str path is unsupported")
        result.append((literal.start(1), literal.end(1), literal.group(1)))
    return result


def resolve_resource(module_path: str, address: str) -> str:
    if (not isinstance(address, str) or not address or address.startswith("/")
            or any(char in address for char in ("\\", ":", "\0", "\n", "\r"))):
        raise MigrationError(f"Resource relocation blocked: unsafe relative address {address!r}")
    resolved = posixpath.normpath(posixpath.join(posixpath.dirname(module_path), address))
    if resolved == ".." or resolved.startswith("../"):
        raise MigrationError(f"Resource relocation blocked: address escapes source repository: {address}")
    return resolved


def runtime_declarations(raw: bytes):
    # The declared-runtime-paths intake used by the existing artifact planner.
    def public_runtime(value):
        def replace(match):
            original = match.group()
            parts = original.split("/")
            for project in ("Homework", "H0mework"):
                if project in parts:
                    return "/".join(parts[parts.index(project) + 1:]) or "."
            if original.endswith("/bin/lean"):
                return "lean"
            return "runtime/" + "/".join(parts[3:])
        return PRIVATE_PATH.sub(replace, value)
    result = []
    def visit(value, pointer):
        if isinstance(value, dict):
            for index, (key, item) in enumerate(value.items()):
                if PRIVATE_PATH.search(key):
                    result.append({"pointer": pointer, "key_index": index, "relative": public_runtime(key)})
                visit(item, pointer + "/" + key.replace("~", "~0").replace("/", "~1"))
        elif isinstance(value, list):
            for index, item in enumerate(value):
                visit(item, pointer + "/" + str(index))
        elif isinstance(value, str) and PRIVATE_PATH.search(value):
            result.append({"pointer": pointer, "relative": public_runtime(value)})
    visit(json.loads(raw), "")
    return result


def public_text_path(value: str) -> str:
    parts = value.split("/")
    for project in ("Homework", "H0mework"):
        if project in parts:
            return "/".join(parts[parts.index(project) + 1:]) or "."
    if value.endswith("/bin/lean"):
        return "lean"
    return "runtime/" + "/".join(parts[3:])


def adapt_observer(text: str, imports: dict, target: str):
    # Same registered observer adaptation as migration/migrate2.adapt_observer.
    if not re.search(r"\bgetModuleIdx(?:For)?\?", sv.mask_comments_and_strings(text)):
        return text, {}
    split = sv.audit_observer_start(text)
    if split is None:
        return text, {}
    tail = text[split:]
    masked = sv.mask_comments_and_strings(tail)
    if not re.search(r"\bgetModuleIdx(?:For)?\?", masked):
        return text, {}
    rules = [{"source_module": name, "target_module": owner} for name, owner in imports.items()
             if re.search(r"(?<!`)`" + re.escape(name) + r"(?![\w'.!?])", masked)]
    variables = re.findall(r'IO.getEnv "(BELL_(?:FIBER|DETECTOR|PULSE|ANCHORS)_PAID_NAMES)"', tail)
    if not rules and not variables:
        return text, {}
    fields = {}
    text = sv.rewrite_audit_module_names(text, rules)
    if "open Lean Elab Command in\nrun_cmd do" in text:
        text = sv.rewrite_audit_runtime(text, variables, True)
        fields["audit_full_closure"] = True
    if rules:
        fields["audit_module_rewrites"] = rules
    if variables:
        fields["audit_boundary_fallbacks"] = variables
    declaration = 'elab "#audit_moving_pole_gauss_return" : command => do'
    if declaration in text:
        rule = {"source_declaration": declaration, "target_name": target + ".auditCommand"}
        text = sv.name_audit_command(text, rule)
        fields["audit_command_name"] = rule
    return text, fields


class Planner:
    def __init__(self, root: Path, repository: Path, selection: dict, overrides=()):
        self.root, self.selection = root, selection
        self.git, self.h0_git = FixedGit(repository), FixedGit(root)
        self.export_bytes = (root / "tools/export-map.json").read_bytes()
        self.export = json.loads(self.export_bytes)
        if self.export.get("schema") != 2:
            raise ExportError("Whole-ledger intake requires export-map schema 2")
        self.targets = {row["target"]: row for row in self.export["modules"]}
        self.by_path = collections.defaultdict(list)
        for owner in self.export["modules"]:
            self.by_path[owner["source_path"]].append((owner, owner))
            for alias in owner.get("source_aliases", []):
                record = sv.alias_record(owner, alias)
                self.by_path[record["source_path"]].append((owner, record))
        mapping_path = root / ".local/migration/modules.json"
        self.mapping = json.loads(mapping_path.read_bytes()) if mapping_path.is_file() else {}
        self.providers, self.provider_metadata, self.raw, self.sources, self.edges = {}, {}, {}, {}, {}
        self.public_imports, self.public_layouts = {}, {}
        self.incoming = collections.defaultdict(set)
        self.existing_raw = {}
        self.resources = {}
        self.resource_keys = set()
        self.resource_includes = set()
        self.artifact_by_source = collections.defaultdict(list)
        for artifact in self.export["artifacts"]:
            self.artifact_by_source[artifact["source"]].append(artifact)
        try:
            self.load_providers(overrides)
        except Exception:
            self.close()
            raise

    def load_providers(self, overrides):
        documents = [(document.parent, json.loads(document.read_bytes())) for document in overrides]
        if self.selection.get("providers"):
            documents.append((self.root, self.selection["providers"]))
        for directory, value in documents:
            if isinstance(value, dict) and value.get("schema") in (PROVIDER_SCHEMA, "whole-ledger-original-certification-providers/v1"):
                value = value.get("providers")
            if not isinstance(value, list):
                raise ExportError("Unsupported whole-ledger provider schema")
            for row in value:
                key = source_key(row.get("source_commit"), row.get("source_path"))
                digest = row.get("source_sha256")
                if not isinstance(digest, str) or not DIGEST.fullmatch(digest):
                    raise ExportError("Provider requires source_sha256: " + key)
                raw = (directory / row["provider"]).read_bytes()
                if sha(raw) != digest:
                    raise ExportError("Provider bytes differ from their digest: " + key)
                if key in self.providers:
                    raise ExportError("Competing explicit providers: " + key)
                origin = row.get("source_origin")
                if origin is None:
                    if self.git.read(row["source_commit"], row["source_path"]) != raw:
                        raise ExportError("An undeclared provider origin must be the exact fixed Git body: " + key)
                    origin = {"kind": "fixed-git-original-material", "source_commit": row["source_commit"],
                              "source_path": row["source_path"]}
                self.providers[key] = (raw, copy.deepcopy(origin))
                self.provider_metadata[key] = copy.deepcopy(row)
        for key, (raw, origin) in self.providers.items():
            self.verify_origin(origin, raw, key.split(":", 1)[0])

    def close(self):
        self.git.close()
        self.h0_git.close()

    def existing_body(self, owner):
        target = owner["target"]
        if target not in self.existing_raw:
            before = sv.ROOT
            try:
                sv.ROOT = self.root
                self.existing_raw[target] = sv.module_views(owner, self.targets)
            finally:
                sv.ROOT = before
        return self.existing_raw[target][1]

    def verify_origin(self, origin, raw: bytes, epoch: str):
        if not isinstance(origin, dict) or not origin.get("kind"):
            raise ExportError("A retained provider needs a source_origin contract")
        commit, path = origin.get("source_commit"), origin.get("source_path", origin.get("original_path"))
        if commit and path:
            reader = self.h0_git if str(origin.get("source_repository", "")).rstrip("/").endswith("/H0mework.git") else self.git
            if reader.read(commit, path) != raw:
                raise ExportError("Provider differs from its fixed source_origin Git body: " + path)
            return
        if origin.get("ledger_path"):
            ledger = self.git.read(origin.get("ledger_commit", epoch), origin["ledger_path"])
            if sha(ledger) != origin.get("ledger_sha256"):
                raise ExportError("Retained source fixed ledger SHA differs: " + origin["ledger_path"])
            if origin.get("ledger_pointer") is not None:
                bound = json.loads(ledger)
                for token in origin["ledger_pointer"].lstrip("/").split("/") if origin["ledger_pointer"] else []:
                    token = token.replace("~1", "/").replace("~0", "~")
                    bound = bound[int(token)] if isinstance(bound, list) else bound[token]
                ledger = json.dumps(bound).encode()
            verdict_digest = origin.get("original_verdict_sha256", sha(raw))
            if (origin.get("original_source_sha256") != sha(raw)
                    or not isinstance(verdict_digest, str) or not DIGEST.fullmatch(verdict_digest)
                    or not re.search(rb"(?<![0-9a-f])" + verdict_digest.encode() + rb"(?![0-9a-f])", ledger)):
                raise ExportError("Fixed ledger does not bind the retained original SHA: " + origin["ledger_path"])
            if verdict_digest != sha(raw):
                matches = [(body, metadata) for body, metadata in self.providers.values()
                           if sha(body) == verdict_digest and metadata.get("original_artifact_name") == "verdict.json"]
                if len(matches) != 1:
                    raise ExportError("A linked certification artifact needs its exact retained original verdict")
                verdict, verdict_origin = matches[0]
                self.verify_origin(verdict_origin, verdict, epoch)
                values = {}
                def walk(value, path=""):
                    if isinstance(value, dict):
                        for name, child in value.items():
                            walk(child, path + "." + name if path else name)
                    elif isinstance(value, list):
                        for index, child in enumerate(value):
                            walk(child, path + "." + str(index))
                    else:
                        values.setdefault(path, []).append(value)
                walk(json.loads(verdict))
                bindings = origin.get("original_verdict_sha_bindings")
                if (not isinstance(bindings, list) or not bindings
                        or any(values.get(binding) != [sha(raw)] for binding in bindings)):
                    raise ExportError("Original verdict does not bind the linked artifact SHA: " + str(bindings))
            elif origin.get("original_artifact_name") == "verdict.json":
                document = json.loads(raw)
                for field, origin_field in (("checkpoint", "checkpoint"), ("fixed_head", "original_fixed_head")):
                    if origin_field in origin and document.get(field) != origin[origin_field]:
                        raise ExportError("Original verdict execution identity differs: " + field)
            return
        receipt_path = origin.get("receipt_path")
        digest = origin.get("receipt_sha256")
        pointer = origin.get("receipt_pointer")
        if not receipt_path or not digest or not isinstance(pointer, str):
            raise ExportError("Retained source lacks a fixed Git or receipt-pointer binding")
        receipt = self.git.read(origin.get("receipt_commit", epoch), receipt_path)
        if sha(receipt) != digest:
            raise ExportError("Retained source receipt SHA differs: " + receipt_path)
        bound = json.loads(receipt)
        for token in pointer.lstrip("/").split("/") if pointer else []:
            token = token.replace("~1", "/").replace("~0", "~")
            bound = bound[int(token)] if isinstance(bound, list) else bound[token]
        if sha(raw) not in json.dumps(bound):
            raise ExportError("Receipt pointer does not bind the retained source SHA: " + receipt_path + pointer)
        declared = origin.get("original_path")
        if declared and declared not in json.dumps(bound):
            raise ExportError("Receipt pointer does not bind the retained original path: " + receipt_path + pointer)

    def available(self, commit, path):
        key = source_key(commit, path)
        return (key in self.providers or self.git.exists(commit, path)
                or any(sv.row_at(record, commit) and record.get("source_origin")
                       for _, record in self.by_path[path]))

    def source(self, commit, path):
        key = source_key(commit, path)
        if key in self.providers:
            raw, origin = self.providers[key]
            original = self.git.read(commit, path) if self.git.exists(commit, path) else None
            if original is not None and origin.get("original_source_sha256", sha(original)) != sha(original):
                raise ExportError("Explicit supplement does not bind the selected original Git SHA: " + key)
        elif self.git.exists(commit, path):
            original = self.git.read(commit, path)
            digest = sha(original)
            supplements = [(owner, record) for owner, record in self.by_path[path]
                           if record.get("source_origin", {}).get("original_source_sha256") == digest
                           and record["source_sha256"] != digest]
            epoch_bound_git_supplement = False
            if not supplements:
                # Earlier signed Git supplements predate original_source_sha256.
                # Their exact admitted epoch/path is the binding; this fallback
                # cannot carry a repair to an unregistered later epoch.
                supplements = [(owner, record) for owner, record in self.by_path[path]
                               if sv.row_at(record, commit)
                               and record.get("source_origin", {}).get("kind") == "git-source-supplement"
                               and record.get("source_origin", {}).get("original_path", record.get("source_origin", {}).get("source_path")) == path
                               and record["source_sha256"] != digest]
                epoch_bound_git_supplement = bool(supplements)
            if supplements:
                contracts = {(record["source_sha256"], json.dumps(sv.semantic_origin(record.get("source_origin")), sort_keys=True))
                             for _, record in supplements}
                if len(contracts) != 1:
                    raise ExportError("Conflicting signed source supplements: " + key)
                owner, selected = min(supplements, key=lambda pair: (not sv.row_at(pair[1], commit), pair[0]["target"]))
                raw = self.existing_body(owner)
                origin = copy.deepcopy(selected["source_origin"])
                self.verify_origin(origin, raw, commit)
                if epoch_bound_git_supplement:
                    origin["original_source_sha256"] = digest
                    origin["original_source_commit"] = commit
                    origin["original_source_path"] = path
                    origin["supplement_binding"] = "same admitted source epoch/path; fixed supplement Git body verified"
                if origin.get("dependency_epoch") != commit:
                    origin["inherited_supplement_dependency_epoch"] = origin.get("dependency_epoch")
                    origin["dependency_epoch"] = commit
            else:
                raw, origin = original, None
        else:
            retained = [(owner, record) for owner, record in self.by_path[path]
                        if sv.row_at(record, commit) and record.get("source_origin")]
            if not retained:
                raise ExportError("Missing fixed Git source (no bound provider): " + key)
            identities = {(record["source_sha256"], json.dumps(sv.semantic_origin(record["source_origin"]), sort_keys=True))
                          for _, record in retained}
            if len(identities) != 1:
                raise ExportError("Ambiguous retained original source: " + key)
            owner, selected = retained[0]
            raw, origin, original = self.existing_body(owner), copy.deepcopy(selected["source_origin"]), None
            self.verify_origin(origin, raw, commit)
        return raw, origin, sha(original) if original is not None else None

    def resolve_import(self, commit, path, module):
        # Original module roots precede adjacent overlays, as in close_entry.
        global_path = "Lean/" + module.replace(".", "/") + ".lean"
        if self.available(commit, global_path):
            return source_key(commit, global_path)
        local = posixpath.normpath(posixpath.join(posixpath.dirname(path), module.replace(".", "/") + ".lean"))
        if self.available(commit, local):
            return source_key(commit, local)
        raise ExportError("Unresolved fixed import " + module + " in " + source_key(commit, path)
                          + "; missing " + global_path + " and " + local)

    def closure(self):
        todo = []
        for selection in self.selection["selections"]:
            commit = selection["source_commit"]
            self.git.tree(commit)
            todo.extend(source_key(commit, path) for path in selection.get("roots", []))
            self.resource_keys.update(source_key(commit, path) for path in selection.get("artifacts", []))
        while todo:
            key = todo.pop()
            if key in self.sources:
                continue
            commit, path = key.split(":", 1)
            raw, origin, original_digest = self.source(commit, path)
            self.raw[key] = raw
            tokens = sv.import_tokens(raw.decode("utf-8"))
            edges = []
            for _, _, name in tokens:
                child = None if name.split(".")[0] in sv.EXTERNAL else self.resolve_import(commit, path, name)
                edges.append((name, child))
                if child:
                    self.incoming[child].add(name)
                    todo.append(child)
            resources = []
            for _, _, address in include_tokens(raw.decode("utf-8")):
                resource = resolve_resource(path, address)
                resource_key = source_key(commit, resource)
                self.resource_keys.add(resource_key)
                self.resource_includes.add(resource_key)
                resources.append({"source_path": resource, "source_address": address, "source_key": resource_key})
            self.sources[key] = {"source_commit": commit, "source_path": path, "source_sha256": sha(raw),
                                 "original_git_sha256": original_digest, "resources": resources}
            if origin:
                self.sources[key]["source_origin"] = origin
            self.edges[key] = edges
        children = {key: {child for _, child in edges if child} for key, edges in self.edges.items()}
        parents = collections.defaultdict(list)
        for key, dependencies in children.items():
            for child in dependencies:
                parents[child].append(key)
        ready = collections.deque(sorted(key for key, dependencies in children.items() if not dependencies))
        order = []
        while ready:
            key = ready.popleft()
            order.append(key)
            for parent in sorted(parents[key]):
                children[parent].remove(key)
                if not children[parent]:
                    ready.append(parent)
        if len(order) != len(self.sources):
            raise ExportError("Fixed source import cycle: " + ", ".join(sorted(set(self.sources) - set(order))[:5]))
        return order

    def plan_artifacts(self):
        additions, reuse, bindings, outputs, updates = [], [], {}, {}, {}
        originals, groups = {}, {}
        taken = {row["path"].casefold() for row in self.export["artifacts"]}
        for key in sorted(self.resource_keys):
            commit, path = key.split(":", 1)
            if key in self.providers:
                raw, origin = self.providers[key]
            else:
                raw, origin = self.git.read(commit, path), None
            digest = sha(raw)
            originals[key] = raw
            self.resources[key] = {"source_path": path, "source_commit": commit, "source_sha256": digest}
            identity = (path, digest)
            candidates = [row for row in self.artifact_by_source[path] if row["source_sha256"] == digest
                          and (key not in self.resource_includes or not row.get("compression"))]
            if candidates:
                row = min(candidates, key=lambda value: (not sv.row_at(value, commit), value["path"]))
                pub.verify_artifact((self.root / row["path"]).read_bytes(), row, raw)
                bindings[key] = row["path"]
                reuse.append({"source_key": key, "source_sha256": digest, "public_path": row["path"],
                              "target_sha256": row["target_sha256"]})
                updates.setdefault(row["path"], set(row.get("source_revisions", [row["source_revision"]]))).add(commit)
                self.resources[key].update(target=row["path"], target_sha256=row["target_sha256"])
                continue
            if identity in groups:
                row = groups[identity]
                row["source_revisions"].append(commit)
                bindings[key] = row["path"]
                continue
            prefix = "scripts" if path.endswith(".py") else "evidence"
            target = prefix + "/whole-ledger/original/R" + commit[:8] + "/" + path
            if target.casefold() in taken or (self.root / target).exists():
                raise ExportError("New artifact target collision: " + target)
            taken.add(target.casefold())
            row = {"source": path, "source_revision": commit, "source_revisions": [commit],
                   "source_sha256": digest, "target_sha256": digest, "path": target, "target": target,
                   "role": "mechanism-source" if path.endswith((".py", ".lean")) else "evidence"}
            if origin:
                row["source_origin"] = copy.deepcopy(origin)
            additions.append(row)
            groups[identity] = row
            bindings[key], outputs[target] = target, raw
        # Publication is applied per epoch so a same-path receipt from another
        # epoch cannot rewrite this receipt's bound sibling digest.
        publication_summary = []
        for commit in sorted({row["source_revision"] for row in additions}):
            rows = [row for row in additions if row["source_revision"] == commit]
            declarations = {}
            for row in rows:
                if row["path"].endswith(".json"):
                    key = source_key(commit, row["source"])
                    metadata = self.provider_metadata.get(key, {})
                    declarations[(commit, row["source"])] = (metadata["runtime_paths"] if "runtime_paths" in metadata
                                                            else runtime_declarations(outputs[row["path"]]))
            summary = pub.publish_outputs(outputs, [], rows, None, declarations)
            publication_summary.append({"source_commit": commit, **summary})
            for row in rows:
                raw = outputs[row["path"]]
                if not row["path"].endswith((".json", ".gz", ".xz", ".zip", ".pdf", ".xlsx")):
                    text = raw.decode("utf-8")
                    metadata = self.provider_metadata.get(source_key(commit, row["source"]), {})
                    declared = metadata.get("runtime_paths")
                    if declared is not None or PRIVATE_PATH.search(text):
                        # Same fixed text-span publication contract as plan_artifacts.
                        rules = declared if declared is not None else [
                            {"begin": match.start(), "end": match.end(), "relative": public_text_path(match.group())}
                            for match in PRIVATE_PATH.finditer(text)]
                        kind = pub.TEXT_RUNTIME_KIND if declared is not None else pub.TEXT_KIND
                        raw = pub.text_runtime_paths(raw, rules, kind=kind)
                        outputs[row["path"]] = raw
                        row["publication"] = {"kind": kind, "runtime_paths": rules,
                                              "payload_sha256": sha(raw)}
                        row["target_sha256"] = sha(raw)
                    if UNDECLARED_PATH.search(raw.decode()):
                        raise ExportError("Text artifact needs explicit runtime_paths spans: " + source_key(commit, row["source"]))
                if row["path"].endswith(".json") and UNDECLARED_PATH.search(raw.decode()):
                    def find_path(value, pointer=""):
                        if isinstance(value, dict):
                            for name, child in value.items():
                                yield from find_path(child, pointer + "/" + name.replace("~", "~0").replace("/", "~1"))
                        elif isinstance(value, list):
                            for index, child in enumerate(value):
                                yield from find_path(child, pointer + "/" + str(index))
                        elif isinstance(value, str) and UNDECLARED_PATH.search(value):
                            yield pointer
                    pointers = list(find_path(json.loads(raw)))
                    raise ExportError("Artifact needs explicit runtime_paths at " + source_key(commit, row["source"]) + ": " + ", ".join(pointers))
                pub.verify_artifact(raw, row, originals[source_key(commit, row["source"])])
        by_target = {row["path"]: row for row in self.export["artifacts"] + additions}
        for key, target in bindings.items():
            row = by_target[target]
            self.resources[key].update(target=target, target_sha256=row["target_sha256"])
        for row in additions:
            previous = row["path"]
            raw = outputs[previous]
            included = any(bindings[key] == previous for key in self.resource_includes)
            if len(raw) > 1024 * 1024 and row["source"].endswith(".json") and not included:
                compressed = gzip.compress(raw, compresslevel=9, mtime=0)
                row.update(path=previous + ".gz", target=previous + ".gz", target_sha256=sha(compressed),
                           compression={"kind": "gzip", "uncompressed_bytes": len(raw), "uncompressed_sha256": sha(raw)})
                outputs.pop(previous)
                outputs[row["path"]] = compressed
                for key in bindings:
                    if bindings[key] == previous:
                        bindings[key] = row["path"]
                        self.resources[key].update(target=row["path"], target_sha256=row["target_sha256"])
                pub.verify_artifact(compressed, row, originals[source_key(row["source_revision"], row["source"])])
        return additions, reuse, bindings, outputs, updates, originals, publication_summary

    def public_layout(self, target):
        stack = [(target, False)]
        active = set()
        while stack:
            current, expanded = stack.pop()
            if current in self.public_layouts:
                continue
            row = self.targets[current]
            if not expanded:
                if current in active:
                    raise ExportError("Existing public import cycle: " + current)
                active.add(current)
                if current not in self.public_imports:
                    raw = (self.root / row["path"]).read_bytes()
                    if sha(raw) != row["target_sha256"]:
                        raise ExportError("Existing public source SHA differs: " + row["path"])
                    self.public_imports[current] = tuple(name for _, _, name in sv.import_tokens(raw.decode()))
                stack.append((current, True))
                stack.extend((name, False) for name in self.public_imports[current] if name in self.targets and name not in self.public_layouts)
            else:
                active.remove(current)
                self.public_layouts[current] = sv.layout_identity(
                    row["source_path"], row["source_sha256"], row.get("source_origin"),
                    [self.public_layouts[name] for name in self.public_imports[current] if name in self.targets])
        return self.public_layouts[target]

    def target_for(self, key):
        commit, path = key.split(":", 1)
        name = original_module(path)
        base = self.mapping.get(name)
        if not base:
            candidates = self.by_path[path]
            if candidates:
                target = min(candidates, key=lambda pair: pair[0]["target"])[0]["target"]
                base = re.sub(r"^H0mework\.Versions\.[^.]+\.", "H0mework.", target)
            else:
                base = "H0mework.ReleaseMaterials." + ".".join(component(part) for part in path.removeprefix("Lean/").removesuffix(".lean").split("/"))
        return "H0mework.Versions.R" + commit[:8] + "." + base.removeprefix("H0mework.")

    def private_target(self, name, key, assignments):
        path = self.sources[key]["source_path"]
        if name in (original_module(path), PurePosixPath(path).stem):
            return assignments[key]
        direct = {module: child for module, child in self.edges[key] if child}
        if name in direct:
            return assignments[direct[name]]
        reachable, todo = set(), [key]
        while todo:
            child = todo.pop()
            if child not in reachable:
                reachable.add(child)
                todo.extend(dependency for _, dependency in self.edges[child] if dependency)
        choices = {assignments[child] for child in reachable if original_module(self.sources[child]["source_path"]) == name}
        choices.update(assignments[child] for child in reachable if name in self.incoming[child])
        if len(choices) != 1:
            raise ExportError("Unresolved exact private owner " + name + " in " + key)
        return next(iter(choices))

    def render(self, key, assignments, artifacts):
        source = self.sources[key]
        raw = self.raw[key]
        target, path = assignments[key], source["source_path"]
        destination = "Lean/" + target.replace(".", "/") + ".lean"
        imports = {name: assignments[child] for name, child in self.edges[key] if child}
        inverse = {owner: name for name, owner in imports.items()}
        if len(inverse) != len(imports):
            raise ExportError("Non-invertible original import bindings: " + key)
        row = {"source": original_module(path), "source_path": path, "source_revision": source["source_commit"],
               "source_revisions": [source["source_commit"]], "source_sha256": source["source_sha256"],
               "target": target, "path": destination, "variant": "R" + source["source_commit"][:8], "import_map": inverse}
        if source.get("source_origin"):
            row["source_origin"] = copy.deepcopy(source["source_origin"])
        candidates = [owner for owner, record in self.by_path[path] if record["source_sha256"] == source["source_sha256"]
                      and sv.semantic_origin(record.get("source_origin")) == sv.semantic_origin(source.get("source_origin"))]
        for field in INHERITED_FIELDS:
            values = {json.dumps(prior[field], sort_keys=True) for prior in candidates if prior.get(field)}
            if len(values) > 1:
                raise ExportError("Conflicting inherited " + field + " in " + key)
            if values:
                row[field] = json.loads(next(iter(values)))
        work = sv.rewrite_proof_bodies(raw.decode(), row.get("proof_body_rewrites"))
        resource_rules, digest_rules = [], []
        for resource in source["resources"]:
            artifact = artifacts[resource["source_key"]]
            target_artifact = artifact["target"]
            address = posixpath.relpath(target_artifact, posixpath.dirname(destination))
            hits = [(begin, end) for begin, end, value in include_tokens(work) if value == resource["source_address"]]
            if len(hits) != 1:
                raise ExportError("Original include_str address is not unique: " + key)
            resource_rules.append({"source_address": resource["source_address"], "source_artifact": resource["source_path"],
                                   "target_address": address, "target_artifact": target_artifact,
                                   "data_sha256": artifact["source_sha256"]})
            old, new = artifact["source_sha256"], artifact["target_sha256"]
            if old != new and json.dumps(old) in work:
                if work.count(json.dumps(old)) != 1:
                    raise ExportError("Original resource digest is not unique: " + key)
                digest_rules.append({"source": old, "target": new})
        tokens = sv.import_tokens(work)
        text = sv.transform(work, tokens, imports).decode()
        # include_str spans shift when imports relocate, so apply their exact
        # original literal spans after import relocation, as migration does.
        for begin, end, address in sorted([(begin, end, rule["target_address"])
            for rule in resource_rules for begin, end, old in include_tokens(text)
            if old == rule["source_address"]], reverse=True):
            text = text[:begin] + address + text[end:]
        if resource_rules:
            row["resource_rewrites"] = resource_rules
        masked = sv.mask_comments_and_strings(text)
        names = set()
        for name in re.findall(r"(?<![\w.])_private\.([A-Za-z_][A-Za-z0-9_.']*)", masked):
            parts = name.split(".")
            numeric = next((index for index, part in enumerate(parts) if part.isdigit()), len(parts))
            owner = ".".join(parts[:numeric])
            if owner.split(".")[0] not in sv.EXTERNAL:
                names.add(owner)
        private_rules = [{"source_name": "_private." + name,
                          "target_name": "_private." + self.private_target(name, key, assignments)} for name in sorted(names)]
        text = sv.rewrite_private_names(text, private_rules)
        if private_rules:
            row["private_name_rewrites"] = private_rules
        string_names = {rule["source_owner"].removeprefix("_private.") for prior in candidates
                        for rule in prior.get("private_owner_string_rewrites", [])}
        masked_work = sv.mask_comments_and_strings(work)
        for match in re.finditer(r'\.startsWith\s+"_private\.([A-Za-z_][A-Za-z0-9_.\']*)"', work):
            if masked_work[match.start():match.start() + 11] == ".startsWith":
                string_names.add(match[1].rstrip("."))
        owner_rules = [{"source_owner": "_private." + name,
                        "target_owner": "_private." + self.private_target(name, key, assignments)} for name in sorted(string_names)]
        text = sv.rewrite_private_owner_strings(text, owner_rules)
        if owner_rules:
            row["private_owner_string_rewrites"] = owner_rules
        expression_sets = {json.dumps(prior["private_owner_expression_rewrites"], sort_keys=True)
                           for prior in candidates if prior.get("private_owner_expression_rewrites")}
        if len(expression_sets) > 1:
            raise ExportError("Conflicting private expression adaptations: " + key)
        if expression_sets:
            expressions = json.loads(next(iter(expression_sets)))
            for rule in expressions:
                for old_target, prior in sorted(self.targets.items(), key=lambda pair: -len(pair[0])):
                    child = source_key(source["source_commit"], prior["source_path"])
                    if child in assignments and self.sources[child]["source_sha256"] == prior["source_sha256"]:
                        rule["target_expression"] = rule["target_expression"].replace(old_target, assignments[child])
        else:
            expressions = []
        masked_expressions = sv.mask_comments_and_strings(text)
        for match in re.finditer(r"Lean\.mkPrivateNameCore `([A-Za-z_][A-Za-z0-9_.']*) `([A-Za-z_][A-Za-z0-9_.']*)", masked_expressions):
            before = text[match.start():match.end()]
            after = "Lean.mkPrivateNameCore `" + self.private_target(match[1], key, assignments) + " `" + match[2]
            prior = next((rule for rule in expressions if rule["source_expression"] == before), None)
            if prior is not None:
                prior["target_expression"] = after
            else:
                expressions.append({"source_expression": before, "target_expression": after, "count": 1})
        for match in sv.PRIVATE_SPLIT_OWNER.finditer(text):
            if masked_expressions[match.start()] != '(':
                continue
            before = match[0]
            after = before.replace('"_private.' + match[1] + '"',
                                   '"_private.' + self.private_target(match[1], key, assignments) + '"', 1)
            count = sum(1 for other in sv.PRIVATE_SPLIT_OWNER.finditer(text)
                        if other[0] == before and masked_expressions[other.start()] == '(')
            prior = next((rule for rule in expressions if rule["source_expression"] == before), None)
            if prior is not None:
                prior["target_expression"] = after
                prior["count"] = count
            else:
                expressions.append({"source_expression": before, "target_expression": after, "count": count})
        str_owners = sv.private_str_owner_literals(text)
        for _, _, before, owner in str_owners:
            after = sv.private_str_owner_expression(self.private_target(owner, key, assignments))
            count = sum(1 for _, _, expression, _ in str_owners if expression == before)
            prior = next((rule for rule in expressions if rule["source_expression"] == before), None)
            if prior is not None:
                prior.update(target_expression=after, count=count)
            else:
                expressions.append({"source_expression": before, "target_expression": after, "count": count})
        if expressions:
            row["private_owner_expression_rewrites"] = expressions
            text = sv.rewrite_private_owner_expressions(text, expressions)
        text, audit = adapt_observer(text, imports, target)
        row.update(audit)
        text = sv.name_local_instances(text, row.get("local_instance_names"))
        text = sv.suggestion_index_postlude(text, row.get("suggestion_name_exclusions"))
        view = sv.suggestion_index_postlude(
            sv.rewrite_proof_bodies(raw.decode(), row.get("proof_body_rewrites")),
            row.get("suggestion_name_exclusions")).encode()
        encoded = text.encode()
        for rule in digest_rules:
            old, new = json.dumps(rule["source"]).encode(), json.dumps(rule["target"]).encode()
            if encoded.count(old) != 1:
                raise ExportError("Resource digest relocation lost its exact literal: " + key)
            encoded, view = encoded.replace(old, new, 1), view.replace(old, new, 1)
        if digest_rules:
            row["resource_sha256_rewrites"] = digest_rules
        if sha(view) != row["source_sha256"]:
            row["view_sha256"] = sha(view)
        row["target_sha256"] = sha(encoded)
        pub.verify_file_size(len(encoded), destination)
        return row, encoded

    def build(self, selection_digest, *, artifacts_only=False):
        if artifacts_only:
            for selection in self.selection["selections"]:
                self.resource_keys.update(source_key(selection["source_commit"], path) for path in selection.get("artifacts", []))
            included = {rule["source_artifact"] for row in self.export["modules"] for rule in row.get("resource_rewrites", [])}
            self.resource_includes.update(key for key in self.resource_keys if key.split(":", 1)[1] in included)
            order = []
        else:
            order = self.closure()
        artifact_add, artifact_reuse, artifact_bindings, outputs, artifact_updates, originals, publication = self.plan_artifacts()
        assignments, signatures, layouts, rows, reuse, revision_updates, alias_updates = {}, {}, {}, [], [], {}, collections.defaultdict(list)
        signature_owners = {}
        taken = {target.casefold() for target in self.targets}
        new_by_target = {}
        for key in order:
            source = self.sources[key]
            expected = tuple(assignments[child] if child else name for name, child in self.edges[key])
            signature_record = {"source_path": source["source_path"], "source_sha256": source["source_sha256"],
                                "origin_contract": sv.semantic_origin(source.get("source_origin")),
                                "imports": [{"module": name, "signature": signatures[child] if child else "external:" + name}
                                            for name, child in self.edges[key]],
                                "resources": [{"source_address": resource["source_address"],
                                               "source_sha256": self.resources[resource["source_key"]]["source_sha256"]}
                                              for resource in source["resources"]]}
            signature = sha(json.dumps(signature_record, sort_keys=True, separators=(",", ":")).encode())
            signatures[key] = signature
            layouts[key] = sv.layout_identity(source["source_path"], source["source_sha256"], source.get("source_origin"),
                                             [layouts[child] for _, child in self.edges[key] if child])
            exact = []
            for owner, record in self.by_path[source["source_path"]]:
                if (record["source_sha256"] != source["source_sha256"]
                    or sv.semantic_origin(record.get("source_origin")) != signature_record["origin_contract"]):
                    continue
                if self.existing_body(owner) != self.raw[key]:
                    raise ExportError("Existing source byte identity differs: " + key)
                self.public_layout(owner["target"])
                actual = self.public_imports[owner["target"]]
                resources = [{"source_address": rule["source_address"], "source_sha256": rule["data_sha256"]}
                             for rule in owner.get("resource_rewrites", [])]
                if self.public_layouts[owner["target"]] == layouts[key] and resources == signature_record["resources"]:
                    exact.append((owner, record))
            if exact:
                owner, record = min(exact, key=lambda pair: (not sv.row_at(pair[1], source["source_commit"]), pair[0]["target"]))
                target = owner["target"]
                assignments[key] = target
                reuse.append({"source_key": key, "source_path": source["source_path"], "public_path": owner["path"], "target": target,
                              "source_sha256": source["source_sha256"], "target_sha256": owner["target_sha256"],
                              "signature_sha256": signature})
                if self.public_imports[target] != expected:
                    source["canonical_import_owner_equivalence"] = {
                        "requested_import_targets": list(expected), "actual_owner_import_targets": list(self.public_imports[target]),
                        "comparison": "source_view recursive full-source layout identity", "layout_sha256": layouts[key]}
                if not sv.row_at(record, source["source_commit"]):
                    if record is owner and record.get("source_origin") == source.get("source_origin"):
                        revision_updates.setdefault(target, set(owner["source_revisions"])).add(source["source_commit"])
                    else:
                        alias_updates[target].append(self.alias(key, signature, owner["source_path"]))
                signature_owners.setdefault(signature, target)
            elif signature in signature_owners:
                target = signature_owners[signature]
                assignments[key] = target
                row = new_by_target[target]
                if row.get("source_origin") == source.get("source_origin"):
                    row["source_revisions"].append(source["source_commit"])
                else:
                    row.setdefault("source_aliases", []).append(self.alias(key, signature, row["source_path"]))
            else:
                target = self.target_for(key)
                if target.casefold() in taken or (self.root / ("Lean/" + target.replace(".", "/") + ".lean")).exists():
                    raise ExportError("Immutable target collision (fresh explicit version required): " + key + " -> " + target)
                taken.add(target.casefold())
                assignments[key] = target
                row, encoded = self.render(key, assignments, self.resources)
                rows.append(row)
                new_by_target[target] = row
                outputs[row["path"]] = encoded
                signature_owners[signature] = target
            source.update(target=assignments[key], signature_sha256=signature, layout_sha256=layouts[key],
                          imports={name: assignments[child] for name, child in self.edges[key] if child},
                          dependencies=[child for _, child in self.edges[key] if child],
                          raw_provider="raw/" + source["source_sha256"])
        for row in rows + artifact_add:
            row["source_revisions"] = sorted(set(row["source_revisions"]))
        plan = {"schema": PLAN_SCHEMA, "status": "staged", "selection_sha256": selection_digest,
                "export_map_sha256": sha(self.export_bytes), "source_repository": self.export["source_repository"],
                "selections": self.selection["selections"], "assignments": assignments, "sources": self.sources,
                "order": order, "additions": rows, "reuse": reuse, "artifacts": artifact_add, "reuse_artifacts": artifact_reuse,
                "artifact_bindings": artifact_bindings, "source_revision_updates": [{"target": target, "source_revisions": sorted(refs)}
                                                                                      for target, refs in sorted(revision_updates.items())],
                "source_alias_updates": [{"target": target, "source_aliases": aliases} for target, aliases in sorted(alias_updates.items())],
                "artifact_revision_updates": [{"path": path, "source_revisions": sorted(refs)} for path, refs in sorted(artifact_updates.items())],
                "publication": publication, "existing_public_bytes_written": False,
                "layout_canonicalization": {"algorithm": "full fixed source body, ordered recursive imports, original resource SHA and semantic source_origin",
                                            "import_map_scope": "actual header imports only"},
                "summary": {"source_closure": len(order), "reused_identities": len(reuse), "added_owners": len(rows),
                            "resource_identities": len(artifact_bindings), "reused_artifacts": len(artifact_reuse), "added_artifacts": len(artifact_add)}}
        return plan, outputs, {**{sha(raw): raw for raw in self.raw.values()}, **{sha(raw): raw for raw in originals.values()}}

    def alias(self, key, signature, owner_path):
        source = self.sources[key]
        name = original_module(source["source_path"])
        if name.startswith("file:"):
            logical = sorted(self.incoming[key])
            name = logical[0] if len(logical) == 1 else PurePosixPath(source["source_path"]).stem
        if not sv.MODULE.fullmatch(name):
            raise ExportError("A shared source alias has no actual logical module name: " + key)
        alias = {"source_path": source["source_path"], "source_sha256": source["source_sha256"],
                 "source_revision": source["source_commit"], "source_revisions": [source["source_commit"]],
                 "original_module_name": name, "signature_sha256": signature,
                 "layout_provenance": {"canonical_source_path": owner_path,
                                       "comparison": "full original body, ordered recursive imports, original resource SHA and semantic source_origin"}}
        if source.get("source_origin"):
            alias["source_origin"] = copy.deepcopy(source["source_origin"])
        return alias


def verify_staged_layouts(planner, plan, stage_root):
    """Use source_view's shared-owner protocol on actual old and staged imports."""
    additions = {row["target"]: row for row in plan["additions"]}
    rows = {**planner.targets, **additions}
    imports = dict(planner.public_imports)
    identities = dict(planner.public_layouts)
    def identity(target):
        stack, active = [(target, False)], set()
        while stack:
            current, expanded = stack.pop()
            if current in identities:
                continue
            row = rows[current]
            if not expanded:
                if current in active:
                    raise ExportError("Combined staged import cycle: " + current)
                active.add(current)
                if current not in imports:
                    raw = ((stage_root if current in additions else planner.root) / row["path"]).read_bytes()
                    if sha(raw) != row["target_sha256"]:
                        raise ExportError("Shared owner bytes differ: " + row["path"])
                    imports[current] = tuple(name for _, _, name in sv.import_tokens(raw.decode()))
                stack.append((current, True))
                stack.extend((name, False) for name in imports[current] if name in rows and name not in identities)
            else:
                active.remove(current)
                identities[current] = sv.layout_identity(row["source_path"], row["source_sha256"], row.get("source_origin"),
                                                        [identities[name] for name in imports[current] if name in rows])
        return identities[target]
    new_owners = {}
    for target in additions:
        digest = identity(target)
        if digest in new_owners:
            raise ExportError("New owner repeats a staged layout: " + target + " -> " + new_owners[digest])
        new_owners[digest] = target
    paths = {row["source_path"] for row in additions.values()}
    for row in planner.targets.values():
        if row["source_path"] in paths and identity(row["target"]) in new_owners:
            raise ExportError("New owner repeats an existing layout: " + new_owners[identity(row["target"])] + " -> " + row["target"])
    return {"checked_import_targets": len(identities), "new_owners": len(additions), "shared_owner_collisions": 0,
            "protocol": "source_view.layout_identity on actual public and staged header imports"}


def reconcile_artifact_baseline(planner, plan, latest_bytes):
    """Independent artifact intake can follow unrelated source-map admission."""
    latest = json.loads(latest_bytes)
    if latest.get("schema") != 2 or latest.get("source_repository") != planner.export["source_repository"]:
        raise ExportError("Artifact baseline changed its schema or source repository")
    by_path = {row["path"]: row for row in latest["artifacts"]}
    previous = {row["path"]: row for row in planner.export["artifacts"]}
    identity_fields = ("source", "path", "source_sha256", "target_sha256", "publication", "compression", "source_origin")
    for reused in plan["reuse_artifacts"]:
        path = reused["public_path"]
        current, prior = by_path.get(path), previous[path]
        if current is None or any(current.get(field) != prior.get(field) for field in identity_fields):
            raise ExportError("Selected artifact changed during planning; rerun against the new map: " + path)
        pub.verify_artifact((planner.root / path).read_bytes(), current)
    for row in plan["artifacts"]:
        if (row["path"] in by_path or (planner.root / row["path"]).exists()
                or any(old["source"] == row["source"] and old["source_sha256"] == row["source_sha256"]
                       for old in latest["artifacts"])):
            raise ExportError("A selected artifact was admitted during staging; rerun to reuse its owner: " + row["source"])
    for update in plan["artifact_revision_updates"]:
        current = by_path[update["path"]]
        update["source_revisions"] = sorted(set(update["source_revisions"]) | set(current.get("source_revisions", [current["source_revision"]])))
    plan["baseline_reconciliation"] = {"initial_export_map_sha256": plan["export_map_sha256"],
                                       "selected_artifacts_rechecked": len(plan["reuse_artifacts"]),
                                       "new_artifact_paths_rechecked": len(plan["artifacts"]),
                                       "source_scope_consumed": False}
    plan["export_map_sha256"] = sha(latest_bytes)


def stage(root: Path, repository: Path, selection_path: Path, output: Path, overrides=(), *, artifacts_only=False):
    selection = load_selection(selection_path)
    output = output.resolve()
    if output == root.resolve() or root.resolve() in output.parents and not (root / ".local").resolve() in output.parents:
        raise ExportError("Stage output must be outside the repository or under its ignored .local")
    planner = Planner(root, repository, selection, overrides)
    try:
        plan, outputs, raws = planner.build(sha(selection_path.read_bytes()), artifacts_only=artifacts_only)
        stage_root = output / "stage"
        for path, raw in outputs.items():
            destination = stage_root / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(raw)
        for digest, raw in raws.items():
            destination = output / "raw" / digest
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(raw)
        before = sv.ROOT
        try:
            sv.ROOT = stage_root
            for row in plan["additions"]:
                _, original = sv.module_views(row, planner.targets)
                if original != raws[row["source_sha256"]]:
                    raise ExportError("Staged exact inverse differs: " + row["source_path"])
        finally:
            sv.ROOT = before
        plan["shared_owner_check"] = verify_staged_layouts(planner, plan, stage_root)
        for row in plan["reuse"]:
            if sha((root / row["public_path"]).read_bytes()) != row["target_sha256"]:
                raise ExportError("Existing public source changed during stage: " + row["public_path"])
        latest_map = (root / "tools/export-map.json").read_bytes()
        if latest_map != planner.export_bytes:
            if artifacts_only:
                reconcile_artifact_baseline(planner, plan, latest_map)
            else:
                raise ExportError("The export map changed during planning; rerun against the new map")
        plan["summary"]["exact_inverse_passed"] = len(plan["additions"])
        plan["summary"]["existing_public_owners_rechecked"] = len({row["target"] for row in plan["reuse"]})
        write_json(output / "plan.json", plan)
        return plan
    finally:
        planner.close()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-repository", type=Path, required=True)
    parser.add_argument("--selection", type=Path, default=Path("checks/whole-ledger-selection.json"))
    parser.add_argument("--output", type=Path, default=Path(".local/whole-ledger-work/export-stage"))
    parser.add_argument("--override-provider", "--providers", type=Path, action="append", default=[])
    parser.add_argument("--artifacts-only", action="store_true", help="Stage explicitly selected artifacts after the source owners have been admitted")
    args = parser.parse_args(argv)
    try:
        plan = stage(ROOT, args.source_repository, args.selection, args.output, args.override_provider, artifacts_only=args.artifacts_only)
    except (ExportError, sv.ViewError, pub.PublicationError, OSError, ValueError, KeyError) as error:
        print(json.dumps({"status": "failed", "error": str(error), "existing_public_bytes_written": False}, ensure_ascii=False))
        return 1
    print(json.dumps({"status": plan["status"], **plan["summary"]}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
