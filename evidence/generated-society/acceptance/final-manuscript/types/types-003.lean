import H0mework.Papers.GeneratedSocietyInterfaces

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
  let root : Nat ← match (parsed.getObjVal? "root" >>= fromJson?) with
    | .ok value => pure value
    | .error error => throwError "Type DAG root is invalid: {error}"
  let decoded ← match wholeLedgerDagDecode nodes root with
    | .ok value => pure value
    | .error error => throwError "Type DAG does not reconstruct: {error}"
  unless (← isDefEq type decoded) do throwError "Type DAG differs from the original declaration type"
  return serialized.compress

private def wholeLedgerName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous
run_cmd do
  let env ← getEnv
  let owners : List String := ["H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Consumers.Registered", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Root.Contract", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.Law", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Execution", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Iteration", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Copy", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Continuation", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Method", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.LedgerCertificate", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.RawCertificate", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance"]
  let wanted : List String := ["SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Consumers.the_characterization_keeps_the_entire_previous_capital_contract", "SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Consumers.the_original_registered_root_consumes_the_minimal_support_and_escape_characterization", "SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Root.MinimalSupportAndEscapeAt", "SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Root.the_original_root_characterizes_minimal_support_and_every_legal_escape", "SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.the_existing_no_capital_contract_iff_its_minimal_permission_support", "SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.uniformly_closed_also_has_the_same_no_capital_contract", "SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Code", "SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Code.afterDelivery", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Attempt", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Iteration.after", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Iteration.every_finite_actual_redress_history_keeps_every_original_native_row", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Iteration.financialSlot", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Iteration.native", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Iteration.next", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Iteration.original", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Iteration.originalRun", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression.a_real_override_keeps_the_original_liability_trigger", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression.every_real_old_grant_causes_redress_after_arbitrary_actual_inputs", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression.exhausted_capture_emits_a_real_exit_refusal_and_repair", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression.overridden", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression.overrideWord", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression.publicResidualDispatchCapturedFacade", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression.publicResidualDispatchOverrideFacade", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression.publicResidualDispatchQuietFacade", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression.quiet_liabilities_pay_an_actual_public_review", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Result", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Result.native", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Result.packet", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.actual_word_and_saved_cut", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.after", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.all_original_native_rows_reach_the_actual_response", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.attempt", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.dispatch_word_is_in_the_whole_root_source", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.every_live_original_slot_forces_the_actual_response", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.every_shortage_generates_an_actual_repair", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.finance", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.intent", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.intent_is_eligible", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.native", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.needsResponse", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.original", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.paid_exit_executes_retirement_in_the_dispatch", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.produce", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.rootActual", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.the_original_root_actually_executes_the_dispatch", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.the_paid_exit_is_the_same_root_actual_next", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.the_same_actual_root_consumes_dispatch_original_rows_and_next", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.trace", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.whole_termination_is_the_only_terminal_branch", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.word", "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.settled_iff_whole_termination_receipts", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.AuditPayment", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Frame", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.PaidMethod", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.PaidMethod.actual_labor_payment", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.PaidMethod.plan", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.PaidMethod.plan_is_parameterized_original", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.Certificate", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.Result", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.actual_ledger_certificate_is_generated", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.certify", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.completion", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.cost_is_registered", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.credit_is_actual_sum", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.cut_is_registered", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.debit_is_actual_sum", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.newborn_is_registered", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.ordered_balance", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.ordered_flow", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.run", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger.task_is_registered", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw.Certificate", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw.Result", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw.actual_raw_certificate_is_generated", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw.certify", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw.completion", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw.cost_is_registered", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw.cut_is_registered", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw.newborn_is_registered", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw.run", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw.task_is_registered", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.AtVisit", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.Face", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.Projection", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.activated", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.activated_state", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.atVisit", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.facade", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.original_root_is_preserved", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.previousFacade", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.previousRoot", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.process", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.projectionLaw", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.root", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime.stateAt", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.AtVisit", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.Certificate", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.Face", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.Projection", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.activated", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.activated_state", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.actual_complete_payload", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.actual_native_boundaries_include_refusal_release_and_renewal", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.atVisit", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.certificate", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.facade", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.original_root_is_preserved", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.previousFacade", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.previousRoot", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.process", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.productionSource", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.projectionLaw", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.root", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime.stateAt", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Ready", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Response", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Response.word", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.actual_dividend_preserves_every_old_executable_continuation", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.actual_final_current_is_the_same_carrier_plus_one_labor", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.advance", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.compile", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.compile_origin", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.every_legal_word_keeps_the_same_extra_labor", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.extra_labor_keeps_every_legal_request", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.frameAt", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.machine_round", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.method_is_kept", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.paid_step_transports_the_same_extra_labor", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.respond", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.seedWord", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.withLabor", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.wordAt", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.copy_preserves_every_financial_position", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.resource_generated_copy_pays_child_services", "SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.resources_generate_legal_copy", "SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance.activated", "SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance.both_replays_accept_the_same_original_trace", "SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance.every_new_source_birth_has_its_own_native_history", "SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance.ledgerCertificate", "SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance.next_copy_review_preserves_the_real_resource_deficit", "SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance.publicArtifactZeroFacade", "SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance.rawCertificate"]
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
