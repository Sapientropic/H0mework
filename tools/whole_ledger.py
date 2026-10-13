#!/usr/bin/env python3
"""Recover the whole-ledger selection and inspect its checked declaration types.

Proof compilation and complete metadata trust use the existing edition runner.
This entry checks the independently recoverable source layouts and resources;
it never looks up a private research checkout or regenerates scientific data.
"""
from __future__ import annotations

import argparse
import gzip
import json
from pathlib import Path
import re

import first_release as release
import source_view

MAP = "docs/whole-ledger-map.json"
SCHEMA = "h0mework/whole-ledger-map@1"


def document(root=release.ROOT):
    data = release.read_json(root / MAP)
    if data.get("schema") != SCHEMA:
        raise release.ReleaseError("Whole-ledger map schema differs")
    claims = release.selected_claims(data)
    expected = {f"WA{i}" for i in range(1, 41)}
    if {claim["id"] for claim in claims} != expected:
        raise release.ReleaseError("The selected map must account for WA1–WA40 exactly")
    return data


def validate_complete_type(row):
    if row.get("type_format") is None:
        if "⋯" in row["type"]:
            raise release.ReleaseError("Checked declaration type was abbreviated")
        return
    if row.get("type_format") != "lean-expr-dag@1" or row.get("kernel_equivalent") is not True:
        raise release.ReleaseError("Complete type has no checked kernel reconstruction")
    graph = json.loads(row["type"])
    nodes, root = graph.get("nodes"), graph.get("root")
    if (graph.get("schema") != "lean-expr-dag@1" or not isinstance(nodes, list)
            or type(root) is not int or not 0 <= root < len(nodes)):
        raise release.ReleaseError("Complete type DAG has no valid root")
    allowed = {"bvar", "sort", "const", "app", "lam", "forallE", "letE", "lit", "proj"}
    for index, node in enumerate(nodes):
        if not isinstance(node, dict):
            raise release.ReleaseError("Complete type DAG node differs")
        kinds = set(node) & allowed
        if len(kinds) != 1 or set(node) - allowed - {"levels"}:
            raise release.ReleaseError("Complete type DAG contains an unresolved or unknown node")
        kind = next(iter(kinds))
        value = node[kind]
        refs = []
        if kind == "app":
            if not isinstance(value, list) or len(value) != 2:
                raise release.ReleaseError("Complete type DAG application differs")
            refs = value
        elif kind in {"lam", "forallE", "letE", "proj"}:
            if not isinstance(value, dict):
                raise release.ReleaseError("Complete type DAG constructor differs")
            keys = ["struct"] if kind == "proj" else ["type", "body"]
            if kind == "letE":
                keys.append("value")
            if any(key not in value for key in keys):
                raise release.ReleaseError("Complete type DAG constructor is incomplete")
            refs = [value[key] for key in keys]
        if any(type(ref) is not int or not 0 <= ref < index for ref in refs):
            raise release.ReleaseError("Complete type DAG has a missing or forward reference")


def verify_recorded_types(data, scopes, *, root=release.ROOT):
    reference = data.get("acceptance", {}).get("declaration_types", {})
    file = release.repo_file(root, reference.get("path", ""))
    raw = file.read_bytes()
    if release.sha(raw) != reference.get("sha256"):
        raise release.ReleaseError("Recorded complete type artifact changed")
    if reference.get("compression") == "gzip":
        raw = gzip.decompress(raw)
    if release.sha(raw) != reference.get("payload_sha256"):
        raise release.ReleaseError("Recorded complete type payload changed")
    result = json.loads(raw)
    if result.get("status") != "passed" or result.get("inputs_unchanged") is not True:
        raise release.ReleaseError("Complete types have no stable actual acceptance")
    fixed_inputs = {"lakefile": "Lean/lakefile.toml", "toolchain": "Lean/lean-toolchain",
                    "manifest": "Lean/lake-manifest.json"}
    accepted_inputs = result.get("input_identity", {}).get("sha256", {})
    for name, path in fixed_inputs.items():
        if release.sha(release.repo_file(root, path).read_bytes()) != accepted_inputs.get(name):
            raise release.ReleaseError("Recorded complete type build input changed: " + name)
    for name, scope in scopes.items():
        if result.get("source_scopes", {}).get(name) != scope:
            raise release.ReleaseError("Recorded complete type source scope changed: " + name)
    rows = result["declarations"]
    for row in rows:
        validate_complete_type(row)
    def verify_entry(entry, package):
        for declaration in entry["declarations"]:
            reference = declaration.get("complete_type", {})
            index = reference.get("declaration_index")
            if type(index) is not int or index < 0 or index >= len(rows):
                raise release.ReleaseError("Selected declaration has no complete checked type")
            row = rows[index]
            if (row["package"] != package or row["module"] != entry["public"]["module"]
                    or row["qualified_name"] != release.declaration_name(declaration)
                    or release.sha(row["type"].encode()) != reference.get("type_sha256")):
                raise release.ReleaseError("Selected declaration complete type identity differs")
    for _, role, _, entry in release.claim_entries(release.selected_claims(data)):
        if release.entry_kind(role, entry) == "lean":
            verify_entry(entry, entry["verification"]["proof_package"])
    for package in release.packages(data) if "proof_packages" in data else []:
        for _, _, _, control in release.proof_audit_entries(package, []):
            verify_entry(control, package["id"])
    return len(rows)


def entry(output, *, root=release.ROOT, require_ready=False):
    data = document(root)
    original = release.SCHEMA
    try:
        release.SCHEMA = SCHEMA
        identity = release.verify_map(root, MAP, require_ready)
    finally:
        release.SCHEMA = original
    if not identity["ok"]:
        raise release.ReleaseError(f"Whole-ledger identity failed: {identity['errors']}; {identity['pending']}")
    exported = release.read_json(root / release.EXPORT_MAP)
    _, _, _, inverse = source_view.load_map()
    by_path = {row["path"]: row for row in exported["modules"]}
    recovered = set()
    scopes = {}
    parse_cache = {}
    selected = release.selected_claims(data)
    for package in release.packages(data):
        entries = release.package_entries(selected, package)
        scope = release.package_inputs(root, exported, package, entries, parse_cache=parse_cache)
        for name in scope["files"]:
            row = by_path.get(name)
            if row is None or name in recovered:
                continue
            public, exact = source_view.module_views(row, inverse)
            if release.sha(exact) != row["source_sha256"]:
                raise release.ReleaseError("Recovered complete source differs: " + name)
            recovered.add(name)
        expected_scope = package.get("accepted_source_scope_sha256")
        if require_ready and expected_scope != scope["digest"]:
            raise release.ReleaseError("Accepted package source scope changed: " + package["id"])
        scopes[package["id"]] = {"source_scope_sha256": scope["digest"], "modules": scope["modules"]}
        for control in package.get("controls", []):
            public = control["public"]
            row = by_path.get(public["path"])
            record = (source_view.source_record(row, control["source_path"], control["source_commit"])
                      if row is not None else None)
            if (row is None or public["path"] not in scope["files"]
                    or public["sha256"] != row["target_sha256"]
                    or public["module"] != row["target"]
                    or record is None or not source_view.row_at(record, control["source_commit"])
                    or control["source_sha256"] != record["source_sha256"]
                    or control.get("source_origin") != record.get("source_origin")):
                raise release.ReleaseError("Original kernel control is outside its package: " + public["path"])
            if require_ready and control.get("verification", {}).get("kernel") != "passed":
                raise release.ReleaseError("Original kernel control has no actual acceptance: " + public["path"])
    artifact_index = {row["path"]: row for row in exported["artifacts"]}
    resource_paths = {entry["public"]["path"] for _, role, _, entry in release.claim_entries(selected)
                      if role == "resources" and entry.get("public")}
    for path in sorted(resource_paths):
        source_view.artifact_views(artifact_index[path])
    type_count = verify_recorded_types(data, scopes, root=root) if require_ready else None
    directory = release.new_output(root, output)
    result = {"schema": "h0mework/whole-ledger-entry@1", "status": "passed",
              "claim_map_sha256": release.sha((root / MAP).read_bytes()),
              "claims": len(selected), "mapped_entries": identity["mapped"],
              "complete_proof_owners_recovered": len(recovered),
              "resources_verified": len(resource_paths), "packages": scopes,
              "private_source_reads": 0, "scientific_recalculation": False,
              "recorded_readiness_required": require_ready,
              "recorded_complete_types_verified": type_count}
    (directory / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


TYPE_DAG_CODE = r'''
-- Name, level, binder and literal encoding follows Lean.Idbg (Apache-2.0).
open Lean Elab Command Meta
namespace WholeLedgerTypeCodec

/-- Custom `Name` serialization that preserves the exact structure.
The standard `ToJson`/`FromJson Name` uses `toString`/`toName` which doesn't
round-trip for hygienic names (e.g., names containing `@`). -/
def nameToJson : Name → Json
  | .anonymous => Json.null
  | .str p s   => Json.mkObj [("str", Json.arr #[nameToJson p, toJson s])]
  | .num p n   => Json.mkObj [("num", Json.arr #[nameToJson p, n])]

/-- Inverse of `nameToJson`. -/
partial def nameFromJson? (j : Json) : Except String Name := do
  if j.isNull then return .anonymous
  if let some arr := (j.getObjVal? "str").toOption then
    let #[p, s] := (← fromJson? arr : Array Json) | .error "str expects 2 elements"
    return .str (← nameFromJson? p) (← fromJson? s)
  if let some arr := (j.getObjVal? "num").toOption then
    let #[p, n] := (← fromJson? arr : Array Json) | .error "num expects 2 elements"
    return .num (← nameFromJson? p) (← fromJson? n)
  .error s!"expected Name, got {j}"

/-- Serialize `BinderInfo` to JSON. -/
def binderInfoToJson : BinderInfo → Json
  | .default        => "default"
  | .implicit       => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit   => "instImplicit"

/-- Deserialize `BinderInfo` from JSON. -/
def binderInfoFromJson? : Json → Except String BinderInfo
  | .str "default"        => .ok .default
  | .str "implicit"       => .ok .implicit
  | .str "strictImplicit" => .ok .strictImplicit
  | .str "instImplicit"   => .ok .instImplicit
  | j => .error s!"expected BinderInfo, got {j}"

/-- Serialize `Literal` to JSON. -/
def literalToJson : Literal → Json
  | .natVal n => Json.mkObj [("natVal", n)]
  | .strVal s => Json.mkObj [("strVal", s)]

/-- Deserialize `Literal` from JSON. -/
def literalFromJson? (j : Json) : Except String Literal := do
  if let some n := (j.getObjVal? "natVal").toOption then
    return .natVal (← fromJson? n)
  if let some s := (j.getObjVal? "strVal").toOption then
    return .strVal (← fromJson? s)
  .error s!"expected Literal, got {j}"

/-- Serialize `Level` to JSON. -/
partial def levelToJson : Level → Json
  | .zero     => Json.mkObj [("zero", Json.null)]
  | .succ l   => Json.mkObj [("succ", levelToJson l)]
  | .max a b  => Json.mkObj [("max", Json.arr #[levelToJson a, levelToJson b])]
  | .imax a b => Json.mkObj [("imax", Json.arr #[levelToJson a, levelToJson b])]
  | .param n  => Json.mkObj [("param", nameToJson n)]
  | .mvar id  => Json.mkObj [("mvar", nameToJson id.name)]

/-- Deserialize `Level` from JSON. -/
partial def levelFromJson? (j : Json) : Except String Level := do
  if (j.getObjVal? "zero").toOption.isSome then
    return .zero
  if let some l := (j.getObjVal? "succ").toOption then
    return .succ (← levelFromJson? l)
  if let some arr := (j.getObjVal? "max").toOption then
    let #[a, b] := (← fromJson? arr : Array Json) | .error "max expects 2 elements"
    return .max (← levelFromJson? a) (← levelFromJson? b)
  if let some arr := (j.getObjVal? "imax").toOption then
    let #[a, b] := (← fromJson? arr : Array Json) | .error "imax expects 2 elements"
    return .imax (← levelFromJson? a) (← levelFromJson? b)
  if let some n := (j.getObjVal? "param").toOption then
    return .param (← nameFromJson? n)
  if let some n := (j.getObjVal? "mvar").toOption then
    return .mvar ⟨← nameFromJson? n⟩
  .error s!"expected Level, got {j}"


end WholeLedgerTypeCodec
open Lean Elab Command Meta
private structure WholeLedgerDag where
  nodes : Array Json := #[]
  seen : ExprStructMap Nat := {}
private partial def wholeLedgerDagEncode (e : Expr) : StateM WholeLedgerDag Nat := do
  if let some i := (← get).seen.get? ⟨e⟩ then return i
  if let .mdata _ child := e then
    let i ← wholeLedgerDagEncode child
    modify fun state => { state with seen := state.seen.insert ⟨e⟩ i }
    return i
  let node ← match e with
    | .bvar i => pure <| Json.mkObj [("bvar", toJson i)]
    | .fvar id => pure <| Json.mkObj [("fvar", WholeLedgerTypeCodec.nameToJson id.name)]
    | .mvar id => pure <| Json.mkObj [("mvar", WholeLedgerTypeCodec.nameToJson id.name)]
    | .sort level => pure <| Json.mkObj [("sort", WholeLedgerTypeCodec.levelToJson level)]
    | .const name levels => pure <| Json.mkObj [("const", WholeLedgerTypeCodec.nameToJson name), ("levels", Json.arr (levels.toArray.map WholeLedgerTypeCodec.levelToJson))]
    | .app fn arg => do
        let fn ← wholeLedgerDagEncode fn
        let arg ← wholeLedgerDagEncode arg
        pure <| Json.mkObj [("app", toJson #[fn, arg])]
    | .lam name type body bi | .forallE name type body bi => do
        let type ← wholeLedgerDagEncode type
        let body ← wholeLedgerDagEncode body
        let tag := if e.isLambda then "lam" else "forallE"
        pure <| Json.mkObj [(tag, Json.mkObj [("name", WholeLedgerTypeCodec.nameToJson name), ("type", toJson type), ("body", toJson body), ("bi", WholeLedgerTypeCodec.binderInfoToJson bi)])]
    | .letE name type value body nondep => do
        let type ← wholeLedgerDagEncode type
        let value ← wholeLedgerDagEncode value
        let body ← wholeLedgerDagEncode body
        pure <| Json.mkObj [("letE", Json.mkObj [("name", WholeLedgerTypeCodec.nameToJson name), ("type", toJson type), ("value", toJson value), ("body", toJson body), ("nondep", toJson nondep)])]
    | .lit literal => pure <| Json.mkObj [("lit", WholeLedgerTypeCodec.literalToJson literal)]
    | .proj typeName index value => do
        let value ← wholeLedgerDagEncode value
        pure <| Json.mkObj [("proj", Json.mkObj [("typeName", WholeLedgerTypeCodec.nameToJson typeName), ("idx", toJson index), ("struct", toJson value)])]
    | .mdata _ _ => unreachable!
  let i := (← get).nodes.size
  modify fun state => { nodes := state.nodes.push node, seen := state.seen.insert ⟨e⟩ i }
  return i
private def wholeLedgerDagRef (prior : Array Expr) (j : Json) : Except String Expr := do
  let i : Nat ← fromJson? j
  match prior[i]? with
  | some e => return e
  | none => throw "Type DAG references a missing or forward node"
private def wholeLedgerDagNode (prior : Array Expr) (j : Json) : Except String Expr := do
  if let some i := (j.getObjVal? "bvar").toOption then return .bvar (← fromJson? i)
  if (j.getObjVal? "fvar").toOption.isSome || (j.getObjVal? "mvar").toOption.isSome then
    throw "Checked declaration type contains an unresolved variable"
  if let some level := (j.getObjVal? "sort").toOption then return .sort (← WholeLedgerTypeCodec.levelFromJson? level)
  if (j.getObjVal? "const").toOption.isSome then
    let name ← WholeLedgerTypeCodec.nameFromJson? (← j.getObjVal? "const")
    let levels : Array Json ← fromJson? (← j.getObjVal? "levels")
    return .const name (← levels.toList.mapM WholeLedgerTypeCodec.levelFromJson?)
  if let some arr := (j.getObjVal? "app").toOption then
    let #[fn,arg] := (← fromJson? arr : Array Json) | throw "Type DAG app needs two nodes"
    return .app (← wholeLedgerDagRef prior fn) (← wholeLedgerDagRef prior arg)
  for tag in ["lam", "forallE"] do
    if let some obj := (j.getObjVal? tag).toOption then
      let name ← WholeLedgerTypeCodec.nameFromJson? (← obj.getObjVal? "name")
      let type ← wholeLedgerDagRef prior (← obj.getObjVal? "type")
      let body ← wholeLedgerDagRef prior (← obj.getObjVal? "body")
      let bi ← WholeLedgerTypeCodec.binderInfoFromJson? (← obj.getObjVal? "bi")
      return if tag == "lam" then .lam name type body bi else .forallE name type body bi
  if let some obj := (j.getObjVal? "letE").toOption then
    return .letE (← WholeLedgerTypeCodec.nameFromJson? (← obj.getObjVal? "name"))
      (← wholeLedgerDagRef prior (← obj.getObjVal? "type"))
      (← wholeLedgerDagRef prior (← obj.getObjVal? "value"))
      (← wholeLedgerDagRef prior (← obj.getObjVal? "body"))
      (← fromJson? (← obj.getObjVal? "nondep"))
  if let some literal := (j.getObjVal? "lit").toOption then return .lit (← WholeLedgerTypeCodec.literalFromJson? literal)
  if let some obj := (j.getObjVal? "proj").toOption then
    return .proj (← WholeLedgerTypeCodec.nameFromJson? (← obj.getObjVal? "typeName"))
      (← fromJson? (← obj.getObjVal? "idx"))
      (← wholeLedgerDagRef prior (← obj.getObjVal? "struct"))
  throw "Unknown type DAG node"
private def wholeLedgerDagDecode (nodes : Array Json) (root : Nat) : Except String Expr := do
  let mut prior := #[]
  for node in nodes do prior := prior.push (← wholeLedgerDagNode prior node)
  wholeLedgerDagRef prior (toJson root)
private def wholeLedgerCompleteType (type : Expr) : MetaM String := do
  let (root, graph) := (wholeLedgerDagEncode type).run {}
  let serialized := Json.mkObj [("schema", toJson "lean-expr-dag@1"), ("nodes", Json.arr graph.nodes), ("root", toJson root)]
  let parsed ← match Json.parse serialized.compress with
    | .ok value => pure value
    | .error error => throwError "Type DAG JSON does not round trip: {error}"
  let nodes : Array Json ← match (parsed.getObjVal? "nodes" >>= fromJson?) with
    | .ok value => pure value
    | .error error => throwError "Type DAG nodes are invalid: {error}"
  let root : Nat ← match (parsed.getObjVal? "root" >>= fromJson?) with
    | .ok value => pure value
    | .error error => throwError "Type DAG root is invalid: {error}"
  let decoded ← match wholeLedgerDagDecode nodes root with
    | .ok value => pure value
    | .error error => throwError "Type DAG does not reconstruct: {error}"
  unless (← isDefEq type decoded) do throwError "Type DAG differs from the original declaration type"
  return serialized.compress
'''

TYPE_AUDIT = r'''
import Lean
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
''' + TYPE_DAG_CODE + r'''
private def wholeLedgerName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous
run_cmd do
  let env ← getEnv
  let owners : List String := __OWNERS__
  let wanted : List String := __WANTED__
  let moduleNames := env.header.moduleNames
  for value in wanted do
    let name := wholeLedgerName value
    let some info := env.checked.get.find? name |
      throwError "MISSING_WHOLE_LEDGER_DECLARATION {value}"
    let some index := env.getModuleIdxFor? name |
      throwError "MISSING_WHOLE_LEDGER_OWNER {value}"
    let owner := moduleNames[index]!.toString
    unless owners.contains owner do
      throwError "WRONG_WHOLE_LEDGER_OWNER {value} actual={owner}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let type ← liftTermElabM (wholeLedgerCompleteType info.type)
    let axioms ← liftTermElabM do collectAxioms name
    let row := Json.mkObj [
      ("qualified_name", toJson name.toString), ("module", toJson owner),
      ("kind", toJson kind), ("type", toJson type),
      ("type_format", toJson "lean-expr-dag@1"), ("kernel_equivalent", toJson true),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("axioms", toJson (axioms.toList.map Name.toString)),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial)]
    logInfo m!"WHOLE_LEDGER_DECLARATION {row.compress}"
'''


def types(output, ids=None, *, root=release.ROOT):
    data = release.read_json(root / MAP)
    if data.get("schema") != SCHEMA:
        raise release.ReleaseError("Whole-ledger map schema differs")
    configured = release.settings(root)
    environment = release.build_environment()
    flags = list(dict.fromkeys(configured["package_moreLeanArgs"] + configured["package_weakLeanArgs"]
                               + ["--trust=0", "-DwarningAsError=true"]))
    selected = release.selected_claims(data)
    rows, runs = [], []
    exported = release.read_json(root / release.EXPORT_MAP)
    packages = release.packages(data, ids)
    entries_by_package = {package["id"]: release.package_entries(selected, package) for package in packages}
    keys = {(claim['id'], role, index) for entries in entries_by_package.values()
            for claim, role, index, _ in entries}
    original = release.SCHEMA
    try:
        release.SCHEMA = SCHEMA
        identity = release.verify_map(root, MAP, entry_keys=keys)
    finally:
        release.SCHEMA = original
    if not identity["ok"]:
        raise release.ReleaseError("Declaration inspection identity failed: " + str(identity["errors"]))
    scopes = {package["id"]: release.package_inputs(root, exported, package, entries_by_package[package["id"]])
              for package in packages}
    before = release.snapshot(root, MAP, scopes)
    directory = release.new_output(root, output)
    for index, package in enumerate(packages, 1):
        entries = entries_by_package[package["id"]]
        scope = scopes[package["id"]]
        audit_entries = release.proof_audit_entries(package, entries)
        owners = sorted({entry["public"]["module"] for _, _, _, entry in audit_entries})
        wanted = sorted({release.declaration_name(declaration) for _, _, _, entry in audit_entries
                         for declaration in entry["declarations"]})
        source = "import " + package["lean_target"] + "\n" + TYPE_AUDIT
        source = source.replace("__OWNERS__", json.dumps(owners)).replace("__WANTED__", json.dumps(wanted))
        file = directory / f"types-{index:03d}.lean"
        file.write_text(source)
        log = directory / f"types-{index:03d}.log"
        run = release.run_process(["lake", "env", "lean", "--root=..", *flags,
                                   "../" + file.relative_to(root).as_posix()], root, log, environment)
        run["package"] = package["id"]
        runs.append(run)
        if run["exit_code"] != 0:
            break
        parsed = [json.loads(match) for match in re.findall(r"WHOLE_LEDGER_DECLARATION (\{[^\n]+\})", log.read_text())]
        if not parsed or not set(wanted) <= {row["qualified_name"] for row in parsed}:
            raise release.ReleaseError("Checked declaration inventory is incomplete: " + package["id"])
        for row in parsed:
            validate_complete_type(row)
        rows.extend({"package": package["id"], **row} for row in parsed)
        after = release.package_inputs(root, exported, package, entries)
        if after["digest"] != scope["digest"]:
            raise release.ReleaseError("Source changed during declaration inspection: " + package["id"])
    after_scopes = {package["id"]: release.package_inputs(root, exported, package, entries_by_package[package["id"]])
                    for package in packages}
    after = release.snapshot(root, MAP, after_scopes)
    result = {"schema": "h0mework/whole-ledger-declarations@1",
              "status": "passed" if len(runs) == len(packages)
                        and all(run["exit_code"] == 0 for run in runs) and before == after else "failed",
              "toolchain": configured["toolchain_pin"], "runs": runs, "declarations": rows,
              "source_scopes": {name: {"source_scope_sha256": scope["digest"], "modules": scope["modules"]}
                                for name, scope in scopes.items()},
              "input_identity": before, "input_identity_after": after, "inputs_unchanged": before == after,
              "inspection_program_sha256": release.sha((root / "tools/whole_ledger.py").read_bytes()),
              "type_scope": "complete shared Lean Expr DAG; exact names, universes, binders, literals, projections and proof terms; nonlogical annotations stripped; independently reconstructed and checked definitionally equal in Lean"}
    (directory / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for command in ("entry", "types"):
        child = commands.add_parser(command)
        child.add_argument("--output", required=True)
        if command == "entry":
            child.add_argument("--require-ready", action="store_true")
        else:
            child.add_argument("--package", action="append")
    args = parser.parse_args(argv)
    try:
        result = (entry(args.output, require_ready=args.require_ready) if args.command == "entry"
                  else types(args.output, args.package))
    except (OSError, ValueError, KeyError, release.ReleaseError, source_view.ViewError) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, ensure_ascii=False))
        return 1
    print(json.dumps({key: value for key, value in result.items() if key not in {"declarations", "runs"}},
                     ensure_ascii=False, indent=2))
    return 0 if result["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
