import H0mework.Papers.WholeLedgerAccountingRc19e94a5

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
  let owners : List String := ["H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel", "H0mework.Realization.Operations.Execution.Debt.Source", "H0mework.Realization.Operations.Execution.Relations", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Authority", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Compiler", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Image", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Projection", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Scope", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Completion", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Noetherian"]
  let wanted : List String := ["SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointOldEvolution", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointOldEvolution_transferred", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_debt_sameDebt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_debt_strict", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_destination_debt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_destination_debt_evolution", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_destination_old", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_destination_old_evolution", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_origin_debt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_origin_old", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_origin_old_evolution", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.CompleteImageAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.CompleteImageAt.target_emitted", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.IdentityScope", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.MathReadout", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Program", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.RawIncidenceAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.RawRowAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.authoritativeRoot", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.authoritySource", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.compile_emitted", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.coverage", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ledgerCompiler", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ledgerRoot", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ledgerSource", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.livingRoot", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.mathReadout", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.mathRowEvolution", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.mathSource", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.mathTargetEntry", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.oldEntry_injective", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.oldFold_destination_injective", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.oldFold_origin_injective", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.originalOccurrence", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.original_projection_outcome", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.patch", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.patch_destination_injective", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.patch_origin_injective", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.projectionLaw", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.read?", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.restructuringCertification", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.restructuringLaw", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.restructuringSource", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.rowEvolution", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.rowSource", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.rows", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.rows_size", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.sourceRow", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.targetRow", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.completed", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.completed_next_state", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.completed_source_value", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.completionRuntime", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.completion_budget", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathContinuation", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathCurrent", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathCurrent_budget", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathOrigin", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathPaidContinuation_wellFounded", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathPayment", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathStep", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.runtimeBudget", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.runtimeBudget_advance", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.runtimeBudget_tick", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.Advance", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.Settlement", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.State", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.advance", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.completed_value", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.generate", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.initial", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.law", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.actual_node", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.boundary", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.budget", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.budget_eq", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.canonicalSuccessor", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.canonical_next", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.current_original", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.current_pair_read", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.debtCurrent", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.debtStep", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.history", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.macro_next_actual", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.occurrence", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.originalOccurrence", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.paidContinuation", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.paidContinuation_wellFounded", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.payment", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalActive", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalEnvironment", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPair", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPair_eq", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPayload", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalProjection", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physical_inverse", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physical_outcome", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physical_pair_inverse", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.pinned_pair", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.postBirthProcess", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.postBirthProcess_actual", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.receipt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.residual_inventory", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.residual_read", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.residual_zero_iff", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.trace_accounting", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.zero_budget_residual", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Phase", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.birth_successor", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.bornResumption", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.firstTick", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initialQuery", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initialQuery_unique", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initial_next", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initial_next_living_law", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initial_resolution", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initial_resolution_kind", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.inquiryProcess", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.inquiryRuntime", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.math_successor", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.nextQueryAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.nextQuery_unique", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.presentationAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.presentationAt_erase_injective", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.stateAt_afterBirth_node", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.firstSuccessor", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.generated", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.initialBornRow", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.initialOldRow", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.program", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceAuthority", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceEntry", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceEvent", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceRoot", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceSuccessor", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceVisit", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.targetAt", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.targetInitialVisit", "SaturationMonoid.SourceOperationExecution.Step.relationWords", "SaturationMonoid.SourceOperationExecution.Step.relation_boundary", "SaturationMonoid.SourceOperationExecution.Trace.relationWords", "SaturationMonoid.SourceOperationExecution.Trace.relationWords_append", "SaturationMonoid.SourceOperationExecution.Trace.relation_boundary", "SaturationMonoid.SourceOperationExecution.Trace.relation_cochain", "SaturationMonoid.SourceOperationExecution.Trace.relation_inventory", "SaturationMonoid.SourceOperationExecution.Trace.relation_old", "SaturationMonoid.SourceOperationExecution.Trace.updated_residual", "SaturationMonoid.SourceOperationExecution.Trace.updated_zero_iff"]
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
