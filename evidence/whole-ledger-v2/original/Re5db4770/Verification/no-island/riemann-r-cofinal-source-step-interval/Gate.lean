import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptStepJointBlock
import «002-gate.source»
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1

run_cmd Lean.modifyEnv fun env =>
 Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CofinalSourceStepIntervalCertificate"

namespace CofinalSourceStepIntervalCertificate
open Lean

private def prefixName : String :=
 "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial."

private structure Binder where
 name : Name
 domain : Expr
 info : BinderInfo
 deriving Inhabited

private def telescope (type : Expr) : Array Binder × Expr := Id.run do
 let mut binders : Array Binder := #[]
 let mut body := type
 while let .forallE name domain next info := body do
  binders := binders.push {name := name, domain := domain, info := info}
  body := next
 return (binders,body)

private def require (ok : Bool) (why : String) : IO Unit :=
 unless ok do throw (IO.userError why)

private def lookup (env : Environment) (name : String) : IO ConstantInfo :=
 match env.find? name.toName with
 | some ci => pure ci
 | none => throw (IO.userError s!"MISSING_CANONICAL_BINDING {name}")

private def instantiate (ci : ConstantInfo) (arguments : Std.HashMap Name Expr)
    (universes : Std.HashMap Name Level) (suffix : Array String) :
    IO (Expr × Expr × Array String) := do
 let levels ← ci.levelParams.mapM fun n =>
  match universes[n]? with
  | some level => pure level
  | none => throw (IO.userError s!"UNMAPPED_CANONICAL_UNIVERSE {ci.name}: {n}")
 let mut value := Expr.const ci.name levels
 let mut target := ci.type.instantiateLevelParams ci.levelParams levels
 let mut binders : Array String := #[]
 while let .forallE name _ body _ := target do
  let some argument := arguments[name]? | break
  value := .app value argument
  target := body.instantiate1 argument
  binders := binders.push name.toString
 require (binders == #["observation","nontrivial","half","depth","ordinal",
  "Parent","Index","Whole","Next","HistoryEnd","History","update","cutoff","method"])
  s!"CANONICAL_GENERIC_BINDER_DRIFT {ci.name}: {binders}"
 let (remaining,_) := telescope target
 require (remaining.map (·.name.toString) == suffix)
  s!"CANONICAL_INDEX_BINDER_DRIFT {ci.name}: {remaining.map (·.name.toString)}"
 return (target,value,binders ++ suffix)

private def write (path : String) (json : Json) : IO Unit :=
 IO.FS.writeFile path (json.pretty ++ "\n")

-- Reuse the raw canonical application from CP505. One literal method is applied to
-- every conclusion, then the conjunction is checked by the kernel without Meta.
private def sameCanonicalMethod (env : Environment) (report current : String) : IO Unit := do
 require (env.header.trustLevel == 0) "CANONICAL_CONTEXT_TRUST_NONZERO"
 let canonical ← lookup env (prefixName ++ "BornRSourcePrice.actual_source_price_method")
 let receipt ← lookup env (prefixName ++ "BornRSourcePrice.SourcePriceMethodReceipt")
 let (binders,result) := telescope canonical.type
 let binderNames := binders.map (·.name.toString)
 require (binderNames == #["observation","nontrivial","half","depth","ordinal","update","N"])
   s!"CANONICAL_BINDER_DRIFT {binderNames}"
 let .const receiptName receiptLevels := result.getAppFn
  | throw (IO.userError "CANONICAL_RESULT_NOT_NOMINAL")
 require (receiptName == receipt.name) "WRONG_NOMINAL_PRICE_RECEIPT"
 let receiptArgs := result.getAppArgs
 let (receiptBinders,_) := telescope receipt.type
 require (receiptArgs.size == receiptBinders.size && receiptArgs.size == 13 &&
          receiptLevels.length == receipt.levelParams.length && receiptLevels.length == 6)
  "CANONICAL_RECEIPT_ARITY_DRIFT"
 let mut arguments : Std.HashMap Name Expr := {}
 for i in [:receiptBinders.size] do
  arguments := arguments.insert receiptBinders[i]!.name receiptArgs[i]!
 let canonicalArgs := (Array.range binders.size).map fun i => Expr.bvar (binders.size-1-i)
 for i in [:binders.size] do
  let name := binders[i]!.name
  arguments := arguments.insert name canonicalArgs[i]!
  if name == `N then arguments := arguments.insert `cutoff canonicalArgs[i]!
 let method := mkAppN (.const canonical.name (canonical.levelParams.map Level.param)) canonicalArgs
 arguments := arguments.insert `method method
 let mut universes : Std.HashMap Name Level := {}
 for (name,level) in receipt.levelParams.zip receiptLevels do
  universes := universes.insert name level
 let f := prefixName ++ "BornRNativeGammaInstall.PhysicalGammaBoundaryFeedback."
 let claims : Array (String × Array String) := #[
   (prefixName ++ "CofinalSourceStepIntervalCertificate.original_source_step_interval_at_literal_joint",
    #["requestIndex","stepIndex"]),
   (f ++ "actual_physical_gamma_boundary_feedback", #[])]
 let applications ← claims.mapM fun (name,suffix) => do
  let ci ← lookup env name
  instantiate ci arguments universes suffix
 let mut target := applications.back!.1
 let mut value := applications.back!.2.1
 for (prop,proof,_) in applications.pop.reverse do
  value := mkAppN (.const ``And.intro []) #[prop,target,proof,value]
  target := mkAppN (.const ``And []) #[prop,target]
 for binder in binders.reverse do
  value := .lam binder.name binder.domain value binder.info
  target := .forallE binder.name binder.domain target binder.info
 let name := `CofinalSourceStepIntervalCertificate.direct_same_canonical_method
 require ((env.find? name).isNone) "CANONICAL_CONTROL_ALREADY_INSTALLED"
 let declaration : Declaration := .thmDecl {
  name := name, levelParams := canonical.levelParams, type := target, value := value, all := [name] }
 let started ← IO.monoMsNow
 write current <| Json.mkObj [("phase",toJson "kernel-start"),("CI",toJson name.toString),
  ("monotonic_ms",toJson started)]
 IO.eprintln "CP531_CANONICAL_KERNEL_START"
 match env.toKernelEnv.addDeclCore 0 0 declaration (cancelTk? := none) with
 | .error error =>
  write current <| Json.mkObj [("phase",toJson "kernel-error"),("CI",toJson name.toString),
   ("elapsed_ms",toJson ((← IO.monoMsNow)-started))]
  throw (IO.userError (← error.toMessageData {} |>.toString))
 | .ok checked =>
  let elapsed := (← IO.monoMsNow)-started
  let some actual := checked.find? name | throw (IO.userError "CANONICAL_CHECKED_CI_MISSING")
  require (actual.type == target && actual.value? (allowOpaque := true) == some value &&
    actual.levelParams == canonical.levelParams) "CANONICAL_CI_CHANGED"
  write current <| Json.mkObj [("phase",toJson "kernel-done"),("CI",toJson name.toString),
   ("elapsed_ms",toJson elapsed)]
  write report <| Json.mkObj [("schema",toJson "cp531-canonical-shared-method-application/v1"),
   ("accepted",toJson true),("CI",toJson name.toString),("canonical",toJson canonical.name.toString),
   ("conjoined_claims",toJson (claims.map (·.1))),("canonical_binders",toJson binderNames),
   ("receipt_argument_binders",toJson (receiptBinders.map (·.name.toString))),
   ("receipt_universe_params",toJson (receipt.levelParams.map Name.toString)),
   ("canonical_universe_params",toJson (canonical.levelParams.map Name.toString)),
   ("application_binders",toJson (applications.map (·.2.2))),
   ("same_literal_method_expr_hash",toJson ((hash method).toNat)),
   ("type_expr_hash",toJson ((hash target).toNat)),("value_expr_hash",toJson ((hash value).toNat)),
   ("value_dependencies",toJson (value.getUsedConstants.map Name.toString)),
   ("canonical_kernel_ms",toJson elapsed),("Meta_calls",toJson (0:Nat)),
   ("new_proof_premises",toJson (0:Nat)),("kernel_add_decl_calls",toJson (1:Nat))]
  IO.eprintln s!"CP531_CANONICAL_KERNEL_PASS {elapsed}ms"

end CofinalSourceStepIntervalCertificate


noncomputable section
universe u uParent uIndex uWhole uNext uHistoryEnd uHistory

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.CofinalSourceStepIntervalCertificate

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
open BornRNativeGammaInstall.PhysicalGammaNextReceiptStepJointBlock
open private selectedActualInput PositionIn.position PositionIn.word PositionIn.lower
  PositionIn.upper PositionIn.actual from «002-gate.source»

private theorem relation_requests_length {S : Type u} {V X : S → Type u}
    [∀ t, AddCommGroup (V t)] {s : S} (start : Nat) (word : Formal ℤ V X s) :
    (SourceInventoryExecutionFeed.requestsFrom start [.relation word]).length =
      (Coefficients.sourceItems word).length := by
  simp only [SourceInventoryExecutionFeed.requestsFrom, SourceInventoryExecutionFeed.eventItems,
    List.append_nil, List.length_map]

private theorem remove_selected_support_ne {Event : Type u} (own : List Event) (support : Nat)
    (present : support < own.length) :
    own.take support ++ own.drop (support+1) ≠ own := by
  have missing : (own.take support ++ own.drop (support+1)).length =
      support + (own.length - (support+1)) := by
    simp only [List.length_append, List.length_take, Nat.min_eq_left present.le, List.length_drop]
  intro forged
  have same := congrArg List.length forged
  omega

private theorem shifted_joint_offset_ne {actual offset : Nat} (same : actual = offset) :
    actual ≠ offset + 1 := by
  omega

local instance gateStepGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value A.W grade t) :=
  Cfa.groups A.W grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : BornRSourcePrice.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
  (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff)

local notation "factory" => A.fixedRFactory observation nontrivial half
local notation "initial" => H.receiver observation nontrivial half depth ordinal
local notation "programme" => H.methodProgramme observation nontrivial half depth ordinal
local notation "site" => Cfa.packetAt factory initial programme rfl
local notation "current" => site (update+2)
local notation "born" => BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualBirth
  observation nontrivial half depth ordinal method
local notation "requests" => Batch.requests factory current born
local notation "selected" => Cfa.selected factory current
set_option quotPrecheck false in
local notation "base" => (Cfa.nativePacket factory current).2.2.1
local notation "decoder" => Cfa.stockDecodedEnvironment selected base

set_option quotPrecheck false in
local notation "receiptStep" requestIndex =>
  Fin (P.words (F.receipt decoder ((requests).get requestIndex))).length

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
private def atPaidStep (requestIndex : Fin (requests).length) (stepIndex : receiptStep requestIndex) :=
  let input := selectedActualInput observation nontrivial half depth ordinal method requestIndex stepIndex
  actualSourceStepJointBlock observation nontrivial half depth ordinal method
    (PositionIn.position input) (PositionIn.word input) (PositionIn.lower input)
    (PositionIn.upper input) (PositionIn.actual input)

run_cmd IO.eprintln "CP531_CONTROL + original_source_step_interval_at_literal_joint"
set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
theorem original_source_step_interval_at_literal_joint
    (requestIndex : Fin (requests).length) (stepIndex : receiptStep requestIndex) :
    let result := atPaidStep observation nontrivial half depth ordinal method requestIndex stepIndex
    let source := result.1
    let choice := Batch.stepInterval factory current born source.origin.sourceIndex
    let address := result.2.1
    let block := result.2.2.1
    let jointPosition := result.2.2.2.1
    let completion := result.2.2.2.2.2.1
    let model := result.2.2.2.2.2.2
    let action := actual_step_relation_source observation nontrivial half depth ordinal method source.origin.sourceIndex
    let own := ((requests).drop choice.first).take choice.count
    let support := source.origin.supportIndex.val
    (type_of% (choice.requests_eq)) ∧ (type_of% address) ∧
    (type_of% (block.trace_eq)) ∧ (type_of% jointPosition) ∧ (type_of% action) ∧
    (type_of% completion) ∧ (type_of% model) ∧
    own.take support ++ own.drop (support+1) ≠ own ∧
    (type_of% (shifted_joint_offset_ne jointPosition)) := by
  let result := atPaidStep observation nontrivial half depth ordinal method requestIndex stepIndex
  let source := result.1
  let choice := Batch.stepInterval factory current born source.origin.sourceIndex
  let own := ((requests).drop choice.first).take choice.count
  let support := source.origin.supportIndex.val
  have fullLength : own.length = choice.count :=
    (congrArg List.length choice.requests_eq).trans ((relation_requests_length _ _).trans choice.count_eq.symm)
  have present : support < own.length :=
    Nat.lt_of_lt_of_le source.origin.supportIndex.isLt (fullLength.trans choice.count_eq).symm.le
  exact ⟨choice.requests_eq, result.2.1, result.2.2.1.trace_eq, result.2.2.2.1,
    actual_step_relation_source observation nontrivial half depth ordinal method source.origin.sourceIndex,
    result.2.2.2.2.2.1, result.2.2.2.2.2.2, remove_selected_support_ne own support present,
    shifted_joint_offset_ne result.2.2.2.1⟩

end CountedPaInitial.CofinalSourceStepIntervalCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

open Lean Elab Command in
run_cmd do
 let some report ← liftIO <| IO.getEnv "CP531_CANONICAL_REPORT"
  | throwError "set CP531_CANONICAL_REPORT for the same canonical method check"
 let some current ← liftIO <| IO.getEnv "CP531_CANONICAL_CURRENT"
  | throwError "set CP531_CANONICAL_CURRENT for the canonical kernel marker"
 let env ← getEnv
 liftIO <| CofinalSourceStepIntervalCertificate.sameCanonicalMethod env report current
