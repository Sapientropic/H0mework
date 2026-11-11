import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptStepJointWhole
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1

run_cmd Lean.modifyEnv fun env =>
 Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CofinalCompleteGroupedWriteCertificate"

namespace CofinalCompleteGroupedWriteCertificate
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
   (prefixName ++ "CofinalCompleteGroupedWriteCertificate.original_complete_grouped_trace_and_joint", #[]),
   (prefixName ++ "CofinalCompleteGroupedWriteCertificate.actual_nonempty_group_rejects_omission_and_duplication",
    #["requestIndex"]),
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
 let name := `CofinalCompleteGroupedWriteCertificate.direct_same_canonical_method
 require ((env.find? name).isNone) "CANONICAL_CONTROL_ALREADY_INSTALLED"
 let declaration : Declaration := .thmDecl {
  name := name, levelParams := canonical.levelParams, type := target, value := value, all := [name] }
 let started ← IO.monoMsNow
 write current <| Json.mkObj [("phase",toJson "kernel-start"),("CI",toJson name.toString),
  ("monotonic_ms",toJson started)]
 IO.eprintln "CP532_CANONICAL_KERNEL_START"
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
  write report <| Json.mkObj [("schema",toJson "cp532-canonical-shared-method-application/v1"),
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
  IO.eprintln s!"CP532_CANONICAL_KERNEL_PASS {elapsed}ms"

end CofinalCompleteGroupedWriteCertificate


noncomputable section
universe u uParent uIndex uWhole uNext uHistoryEnd uHistory

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.CofinalCompleteGroupedWriteCertificate

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
open BornRNativeGammaInstall.PhysicalGammaNextReceiptStepJointWhole
open private jointHistoryAt from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Transport

namespace B
export ActualCofinalSourceAction.SourceReceiptOccurrence.Batch
  (requests nextBlock groupedRequestLists grouped_requests grouped_executed_trace grouped_request_boundary
   sourceRequestAt stepInterval)
end B
namespace Feed
export SourceInventoryExecutionFeed (Request Event receipt requestsFrom eventItems)
export SourceInventoryExecutionFeed.ReceiptOccurrence (executedTrace requestWord)
end Feed
namespace P
export SourceOperationPaidRelations (exposure words)
end P
namespace J
export BornRNativeGammaInstall.PhysicalGammaNextReceiptStepJointBlock (actualStepJointCochain actualStepJointPosition)
export BornRNativeGammaInstall.PhysicalGammaBoundaryFeedback (nextJointBoundary)
export CofinalRelationGeneratedComplex (completion_kills_generated_differential)
end J
namespace Stock
export ActualCofinalSourceAction (bornStock)
end Stock

private theorem group_trace_split {Entry Event : Type u} (groups : List Entry)
    (index : Fin groups.length) (execute : Entry → List Event) :
    (groups.map execute).flatten =
      (((groups.take index.val).map execute).flatten ++ execute (groups.get index)) ++
        ((groups.drop (index.val+1)).map execute).flatten := by
  have split : groups = groups.take index.val ++ groups.get index :: groups.drop (index.val+1) :=
    (List.take_append_drop index.val groups).symm.trans
      (congrArg (groups.take index.val ++ ·) (List.drop_eq_getElem_cons index.isLt))
  exact (congrArg (fun entries : List Entry => (entries.map execute).flatten) split).trans
    (by simp only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons, List.append_assoc])

private theorem slice_at_exact_group {Event : Type u} (stock before own after : List Event)
    (offset : Nat) (beforeLength : before.length = offset)
    (split : stock = before ++ own ++ after) :
    (stock.drop offset).take own.length = own := by
  rw [← beforeLength, split, List.append_assoc, List.drop_left, List.take_left]

private theorem exact_split_rejects_drop_duplicate {Event : Type u}
    (before own after stock : List Event) (split : stock = before ++ own ++ after)
    (present : 0 < own.length) :
    stock ≠ before ++ after ∧ stock ≠ before ++ own ++ own ++ after := by
  have full := congrArg List.length split
  simp only [List.length_append] at full
  constructor
  · intro dropped
    have lengths := congrArg List.length dropped
    simp only [List.length_append] at lengths
    omega
  · intro repeated
    have lengths := congrArg List.length repeated
    simp only [List.length_append] at lengths
    omega

private theorem relation_requests_length {S : Type u} {V X : S → Type u}
    [∀ t, AddCommGroup (V t)] {s : S} (start : Nat) (word : Formal ℤ V X s) :
    (Feed.requestsFrom start [.relation word]).length = (Coefficients.sourceItems word).length := by
  simp only [Feed.requestsFrom, Feed.eventItems, List.append_nil, List.length_map]

private theorem executed_nonempty {S : Type u} {V X : S → Type u}
    [∀ t, AddCommGroup (V t)] {s : S} (decoder : Env V X)
    (items : List (Feed.Request (V := V) (X := X) (s := s))) (present : 0 < items.length) :
    0 < (Feed.executedTrace decoder items).length := by
  cases items with
  | nil => exact False.elim (Nat.not_lt_zero 0 present)
  | cons request tail =>
    change 0 < ((P.exposure (Feed.receipt decoder request)).trace ++ Feed.executedTrace decoder tail).length
    change 0 < ((PresentedRelationEventAt.generator request.expression :: _) ++ _).length
    simp only [List.length_append, List.length_cons]
    omega

local instance gateWholeGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value A.W grade t) := Cfa.groups A.W grade

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
local notation "initial" => BornRSourceMethodHistory.receiver observation nontrivial half depth ordinal
local notation "programme" => BornRSourceMethodHistory.methodProgramme observation nontrivial half depth ordinal
local notation "site" => Cfa.packetAt factory initial programme rfl
local notation "current" => site (update+2)
local notation "nextSite" => site ((update+2)+1)
local notation "born" => BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualBirth
  observation nontrivial half depth ordinal method
set_option quotPrecheck false in
local notation "decoder" =>
  Cfa.stockDecodedEnvironment (Cfa.selected factory current) (Cfa.nativePacket factory current).2.2.1
local notation "batch" => B.requests factory current born
local notation "groups" => B.groupedRequestLists factory current born
local notation "execute" => Feed.executedTrace decoder
local notation "stepCochain" => J.actualStepJointCochain observation nontrivial half depth ordinal method
local notation "written" => Stock.bornStock factory current
local notation "wholeBlock" => B.nextBlock factory current born

run_cmd IO.eprintln "CP532_CONTROL + original_complete_grouped_trace_and_joint"
set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
theorem original_complete_grouped_trace_and_joint :
    let completion := J.completion_kills_generated_differential (jointHistoryAt nextSite) ((List.ofFn stepCochain).sum)
    (groups).flatten = batch ∧
    (((groups).map execute).flatten = execute batch) ∧
    (((groups).map (fun group => (group.map (Feed.requestWord decoder)).sum)).sum =
      ((batch).map (Feed.requestWord decoder)).sum) ∧
    (List.ofFn stepCochain).sum = J.nextJointBoundary observation nontrivial half depth ordinal method ∧
    (type_of% completion) :=
  ⟨B.grouped_requests factory current born, B.grouped_executed_trace factory current born,
    B.grouped_request_boundary factory current born,
    actual_grouped_joint_boundary observation nontrivial half depth ordinal method,
    J.completion_kills_generated_differential (jointHistoryAt nextSite) ((List.ofFn stepCochain).sum)⟩

set_option cleanup.letToHave false in
private def groupIndex (index : Fin (P.words (born).paid).length) : Fin (groups).length :=
  ⟨index.val, by simpa only [B.groupedRequestLists, List.length_ofFn] using index.isLt⟩

run_cmd IO.eprintln "CP532_CONTROL - actual_nonempty_group_rejects_omission_and_duplication"
set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
theorem actual_nonempty_group_rejects_omission_and_duplication (requestIndex : Fin (batch).length) :
    let origin := B.sourceRequestAt factory current born requestIndex
    let index := groupIndex observation nontrivial half depth ordinal method origin.sourceIndex
    let own := execute ((groups).get index)
    let front := (((groups).take index.val).map execute).flatten
    let before := (wholeBlock).before ++ front
    let after := (((groups).drop (index.val+1)).map execute).flatten ++ (wholeBlock).after
    let atJoint := J.actualStepJointPosition observation nontrivial half depth ordinal method origin.sourceIndex
    0 < own.length ∧ (written).trace = before ++ own ++ after ∧
    ((written).trace.drop ((wholeBlock).before.length + front.length)).take own.length = own ∧
    (written).trace ≠ before ++ after ∧ (written).trace ≠ before ++ own ++ own ++ after ∧
    (type_of% atJoint) := by
  let origin := B.sourceRequestAt factory current born requestIndex
  let index := groupIndex observation nontrivial half depth ordinal method origin.sourceIndex
  let choice := B.stepInterval factory current born origin.sourceIndex
  let own := execute ((groups).get index)
  let front := (((groups).take index.val).map execute).flatten
  let back := (((groups).drop (index.val+1)).map execute).flatten
  let before := (wholeBlock).before ++ front
  let after := back ++ (wholeBlock).after
  have picked : (groups).get index = ((batch).drop choice.first).take choice.count := by
    simp only [B.groupedRequestLists, List.get_eq_getElem, List.getElem_ofFn, index, groupIndex, choice]
  have ownCount : ((groups).get index).length = choice.count :=
    (congrArg List.length (picked.trans choice.requests_eq)).trans
      ((relation_requests_length _ _).trans choice.count_eq.symm)
  have present : 0 < own.length := executed_nonempty decoder _ <|
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le _) origin.supportIndex.isLt)
      (ownCount.trans choice.count_eq).symm.le
  have split : execute batch = (front ++ own) ++ back :=
    (B.grouped_executed_trace factory current born).symm.trans (group_trace_split groups index execute)
  have stockSplit : (written).trace = before ++ own ++ after :=
    (wholeBlock).trace_eq.trans
      ((congrArg (fun events => (wholeBlock).before ++ events ++ (wholeBlock).after) split).trans
        (by simp only [before, after, List.append_assoc]))
  have slice : ((written).trace.drop ((wholeBlock).before.length + front.length)).take own.length = own :=
    slice_at_exact_group _ before own after _ List.length_append stockSplit
  have rejects := exact_split_rejects_drop_duplicate before own after _ stockSplit present
  exact ⟨present,stockSplit,slice,rejects.1,rejects.2,
    J.actualStepJointPosition observation nontrivial half depth ordinal method origin.sourceIndex⟩

end CountedPaInitial.CofinalCompleteGroupedWriteCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

open Lean Elab Command in
run_cmd do
 let report ← liftIO <| IO.getEnv "CP532_CANONICAL_REPORT"
 let current ← liftIO <| IO.getEnv "CP532_CANONICAL_CURRENT"
 let env ← getEnv
 liftIO do
  match report, current with
  | some report, some current =>
   CofinalCompleteGroupedWriteCertificate.sameCanonicalMethod env report current
  | none, none =>
   IO.FS.withTempDir fun dir =>
    CofinalCompleteGroupedWriteCertificate.sameCanonicalMethod env
     (dir / "canonical-application.json").toString (dir / "kernel-progress.json").toString
  | _, _ => throw (IO.userError "set both CP532_CANONICAL_REPORT and CP532_CANONICAL_CURRENT")
