import H0mework.Papers.GeneratedSocietyRegeneration

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
  let owners : List String := ["H0mework.Realization.Audit.DebtFirstWrite", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection", "H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootDebtAdmissionActualActionKernel", "H0mework.Versions.R2.Foundation.Source.SequentialAction", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.M14WholeProgramRegression", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"]
  let wanted : List String := ["SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.PeriodicSameOccurrenceRegenerationAt", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.PeriodicSameOccurrenceRegenerationCertificate", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.RepairRenewalAt", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.SameOccurrenceCanonicalRegenerationAt", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.SameOccurrenceCanonicalRegenerationCertificate", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.SameOccurrenceRegenerationCertificate", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.periodicSameOccurrenceRegenerationAt", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.periodicSameOccurrenceRegeneration_certificate", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.periodicSameOccurrenceRegeneration_nextIsNextStep", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.sameOccurrenceCanonicalRegeneration", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.sameOccurrenceCanonicalRegeneration_certificate", "SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.sameOccurrenceCanonicalRegeneration_directConsumer", "SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.CanonicalSocietyAt", "SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.canonicalSociety", "SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.canonicalSociety_periodicSameOccurrenceRegeneration", "SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.canonicalSociety_rootLawComplete_and_u8Available", "SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.canonicalSociety_sameOccurrenceRegeneration", "SaturationMonoid.ProcessGame.Society.Renewal.RootRestrictedRenewalPayloadAt", "SaturationMonoid.ProcessGame.Society.Renewal.RootRestrictedRenewalPayloadAt.generate", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.RootAnswerAndNextFactorizes", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.componentOutcome_eq_activePayload", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.generate", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.inactive_noInstalledRenewal", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.localFace", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.localFace_sourceSeed", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.operationalAuthority", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.payload", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.rootAnswerAndNext_factorizes", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.rootResponsibilityConsumer", "SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.temporalSelectedRow", "SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalProjection", "SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalProjectionLaw", "SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalProjectionLaw.distinctRootOccurrences_generate_distinctSourceSeeds", "SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalProjectionLaw.ofRootShell", "SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalProjectionLaw.toProjectionLaw", "SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalRecognitionAt", "SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalRecognitionAt.componentOutcome_heq_rootOutcome", "SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalRecognitionAt.rootProjection", "SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalRootShellAt", "SaturationMonoid.ProcessGame.Society.Renewal.inheritedByRenewal", "SaturationMonoid.ProcessGame.Society.Renewal.noInstalledComponent_noSourceInstalledRenewal", "SaturationMonoid.ProcessGame.Society.Renewal.renewalComponent", "SaturationMonoid.ProcessGame.Society.Renewal.withRenewalProjection", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.actualNext", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.answer", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.finitePrefix", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.generate", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.independentConsumerReceipt", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.next_erases_to_generated", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.resolution", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.revisionKind", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.revolutionaryTick?", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.tick", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalRevisionKind", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryResolutionAt", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.cofaceFactorizationAndFirstWrite", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.firstWrite", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.firstWriteConsumes", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.firstWriteRealization", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.initialFactorization", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.initialFactorization_unique", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.minimalCoface", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.newRowAnswerAndNext", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.oldRowAnswerAndNext", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.resumption", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.revisedNext", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.rootEntry_eq", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.rooted", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.twoRowAnswerAndNext", "SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.twoRows_share_generatedNext", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.ExactFailureSameRowConditionalU8At", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.LawfulPresentationNoWriteAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedActionWholeLedgerNextAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedActionWholeLedgerNextAt.branch", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedActionWholeLedgerNextAt.dispositionExact", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedActionWholeLedgerNextAt.rooted", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedActionWholeLedgerNextAt.worldWriting", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedDebtAdmissionWholeLedgerNextAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedSequentialActionWholeLedgerNextAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceGeneratedObserverConsumerLegislationAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceGeneratedObserverConsumerLegislationAt.installedCompilationFace", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceGeneratedObserverConsumerLegislationAt.submission", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.InstalledActionAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.LawfulPresentationBranchAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.RejectedBranchAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.SameOccurrenceU8At", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.WorldWritingBranchAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.action_u8_disjoint", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.exhaustive_fourClasses", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.installedCompilationFace", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.nonrooted_worldWritingBranch_isEmpty", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.outputMismatch_isEmpty", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.presentation_worldWritingBranch_isEmpty", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.rejection_worldWritingBranch_isEmpty", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.rooted_exhaustive", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.worldWritingBranch_iff_action_or_u8", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.worldWritingBranch_implies_rooted", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerLegislationProgramAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerLegislationProgramAt.generate", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerLegislationProgramAt.generatedSubmission", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerSameOccurrenceLegislationAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverLegislationQuery", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeRootLawCompleteAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeU8AvailableAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.TypedRejectionVisibleResidualAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.compileSourceNativeObserverConsumerLegislationAt", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.compiledObserverConsumerLegislation_hasNoFifthClass", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.emptyLocalLedger_sameOccurrenceLegislation_isEmpty", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.rich_exhaustive_fourClasses", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceNativeObserverLegislationQuery", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceNativeRootLawComplete", "SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceNativeU8Available", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtAdmissionFirstWrite.generate", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.SourceNativeDebtAdmissionActualActionTargetAt.targetAnswerAndNext_next_eq", "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.SourceNativeSequentialActualActionTargetAt.initialOpenLedger_injective"]
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
