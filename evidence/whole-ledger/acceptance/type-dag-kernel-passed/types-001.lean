import H0mework.Papers.WholeLedgerAccountingRb67aa48c

import Lean
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

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
  let decoded ← match wholeLedgerDagDecode nodes root with
    | .ok value => pure value
    | .error error => throwError "Type DAG does not reconstruct: {error}"
  unless (← isDefEq type decoded) do throwError "Type DAG differs from the original declaration type"
  return serialized.compress

private def wholeLedgerName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous
run_cmd do
  let env ← getEnv
  let owners : List String := ["H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Compiler", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"]
  let wanted : List String := ["SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.AdmissionAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.ActiveAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.InactiveAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.Ledger", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.Occurrence", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.Readout", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.U7", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.World", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_answer", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_next", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_query", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.actual_next", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.actual_state", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.answerFace", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.authority", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.baseRoot", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.calculus", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.classify", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.compilation", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.compilationLaw", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.compilationRoot", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.compiled", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.consumer", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.consumerLaw", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.consumerRoot", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.endpointCount", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.endpointInput", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.endpointState", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.endpoint_source_state", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.entry", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.entryAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.entryAuthority", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.exactOccurrence", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.input", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.original", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.originalMaterialFace", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.original_material", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.packet", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.queryLaw", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.readout", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residualEnvironment", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residualFirstStep", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residualMaterial", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residualRegistered", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residualTarget", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_action", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.root", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.runtime", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.state", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.visit", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.actual_current", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.admission", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.authority", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.endpoint", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.endpointAuthority", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.endpointEntry", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.entry", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.initialEntry", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.initialRow", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.root", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.runtime", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.visit", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.RemainderAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.RowAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.compiler", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.coverage", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.image", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.image_math_row_found", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.ledgerRoot", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.patch", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.patchCertificate", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.patch_fold", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.remainder", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.remainderSource", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.restructuringLaw", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.rowSource", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.rows", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.wholeCertificate"]
  for name in wanted do
    unless (env.checked.get.find? (wholeLedgerName name)).isSome do
      throwError "MISSING_WHOLE_LEDGER_DECLARATION {name}"
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[index]!.toString
    unless owners.contains owner do continue
    unless wanted.contains name.toString do continue
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
