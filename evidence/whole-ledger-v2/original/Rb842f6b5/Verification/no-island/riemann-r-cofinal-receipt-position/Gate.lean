import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptPositionFibre
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1

run_cmd Lean.modifyEnv fun env =>
 Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CofinalReceiptPositionCertificate"

namespace CofinalReceiptPositionCertificate
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
   (prefixName ++ "CofinalReceiptPositionCertificate.original_paid_step_at_literal_next",
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
 let name := `CofinalReceiptPositionCertificate.direct_same_canonical_method
 require ((env.find? name).isNone) "CANONICAL_CONTROL_ALREADY_INSTALLED"
 let declaration : Declaration := .thmDecl {
  name := name, levelParams := canonical.levelParams, type := target, value := value, all := [name] }
 let started ← IO.monoMsNow
 write current <| Json.mkObj [("phase",toJson "kernel-start"),("CI",toJson name.toString),
  ("monotonic_ms",toJson started)]
 IO.eprintln "CP529_CANONICAL_KERNEL_START"
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
  write report <| Json.mkObj [("schema",toJson "cp529-canonical-shared-method-application/v1"),
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
  IO.eprintln s!"CP529_CANONICAL_KERNEL_PASS {elapsed}ms"

end CofinalReceiptPositionCertificate


noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalReceiptPositionCertificate

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open CofinalHistorySettlement

namespace F
export SourceInventoryExecutionFeed (Request receipt requestsFrom)
export SourceInventoryExecutionFeed.ReceiptOccurrence (ExecutedAtStep executedTrace readExecutedStep)
end F
namespace P
export SourceOperationPaidRelations (words stepOccurrence)
end P

private abbrev Values : Unit → Type := fun _ => ℤ
private abbrev Vars : Unit → Type := fun _ => Unit
private abbrev Word := Formal ℤ Values Vars ()
private def decoder : Env Values Vars := fun _ _ => 2
private def raw : Expr Values Vars () := .var ()
private def requests : List (F.Request (V := Values) (X := Vars) (s := ())) :=
  F.requestsFrom 0 [.generator raw, .generator raw]
private def paid := execution decoder raw
private def relationWord : Word := (P.stepOccurrence paid ⟨0, by decide⟩).word

private theorem first_relation :
    (F.executedTrace decoder requests)[1]? = some (.relation relationWord) := rfl
private theorem second_relation :
    (F.executedTrace decoder requests)[3]? = some (.relation relationWord) := rfl
private theorem second_generator :
    (F.executedTrace decoder requests)[2]? = some (.generator raw) := rfl

private theorem request_layout (index : Fin requests.length) :
    (F.executedTrace decoder (requests.take index.val)).length = 2 * index.val ∧
    (P.words (F.receipt decoder (requests.get index))).length = 1 ∧
    (requests.get index).position = index.val := by
  have bound : index.val < 2 := index.isLt
  have choices : index.val = 0 ∨ index.val = 1 := by omega
  rcases choices with zero | one
  · have same : index = (⟨0, by decide⟩ : Fin requests.length) := Fin.ext zero
    rw [same]
    exact ⟨rfl, rfl, rfl⟩
  · have same : index = (⟨1, by decide⟩ : Fin requests.length) := Fin.ext one
    rw [same]
    exact ⟨rfl, rfl, rfl⟩

private theorem selected_address (position : Nat) (found : F.ExecutedAtStep decoder requests position relationWord) :
    position = 2 * found.requestIndex.val + 1 := by
  have layout := request_layout found.requestIndex
  have inside : found.selected.index.val < 1 :=
    Nat.lt_of_lt_of_le found.selected.index.isLt layout.2.1.le
  have localAddress := found.selected.position_eq
  have globalAddress : position = 2 * found.requestIndex.val + found.localIndex :=
    found.offset_eq.trans (congrArg (· + found.localIndex) layout.1)
  omega

run_cmd IO.eprintln "CP529_CONTROL - equal_paid_words_keep_distinct_requests"
theorem equal_paid_words_keep_distinct_requests :
    let first := F.readExecutedStep decoder requests 1 relationWord first_relation
    let second := F.readExecutedStep decoder requests 3 relationWord second_relation
    first.requestIndex.val = 0 ∧ second.requestIndex.val = 1 ∧
    (requests.get first.requestIndex).position ≠ (requests.get second.requestIndex).position := by
  let first := F.readExecutedStep decoder requests 1 relationWord first_relation
  let second := F.readExecutedStep decoder requests 3 relationWord second_relation
  have firstIndex : first.requestIndex.val = 0 := by
    have address := selected_address 1 first
    omega
  have secondIndex : second.requestIndex.val = 1 := by
    have address := selected_address 3 second
    omega
  refine ⟨firstIndex, secondIndex, ?_⟩
  rw [(request_layout first.requestIndex).2.2, (request_layout second.requestIndex).2.2,
      firstIndex, secondIndex]
  exact Nat.zero_ne_one

run_cmd IO.eprintln "CP529_CONTROL - generator_slot_is_not_paid_relation"
theorem generator_slot_is_not_paid_relation (word : Word) :
    (F.executedTrace decoder requests)[2]? ≠ some (.relation word) := by
  intro forged
  have clash := Option.some.inj (second_generator.symm.trans forged)
  cases clash

end CofinalReceiptPositionCertificate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

noncomputable section
universe u uParent uIndex uWhole uNext uHistoryEnd uHistory

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.CofinalReceiptPositionCertificate

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
open ActualNativeRelationTransport (OccurrenceBlock)
open BornRNativeGammaInstall.PhysicalGammaNextReceiptPosition
open private executedTrace_append from
  SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block
open private executedTrace_single from
  SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block.Position
open private following_literal from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt
open private block_reindex from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptBlock

section Forward
variable {S : Type u} {V X W Y : S → Type u}
variable [∀ t, AddCommGroup (V t)] [∀ t, AddCommGroup (W t)] {s : S}

private theorem append_hit {Event : Type u} (front middle back : List Event)
    {offset : Nat} {event : Event} (read : middle[offset]? = some event) :
    (front ++ middle ++ back)[front.length + offset]? = some event := by
  have inside := (List.getElem?_eq_some_iff.mp read).elim (fun bound _ => bound)
  have lower : front.length ≤ front.length + offset := by omega
  have cancel : front.length + offset - front.length = offset := by omega
  rw [List.append_assoc, List.getElem?_append_right lower, cancel, List.getElem?_append_left inside]
  exact read

private structure PositionIn
    {stock : SourceInventoryExecutionFeed.Inventory (V := V) (X := X) (s := s)}
    {trace : List (F.Event (V := V) (X := X) (s := s))}
    (whole : OccurrenceBlock trace stock.trace) where
  position : Nat
  word : Formal ℤ V X s
  lower : whole.before.length ≤ position
  upper : position < whole.before.length + trace.length
  actual : stock.trace[position]? = some (.relation word)

set_option cleanup.letToHave false in
private def fromPaidStep (decoder : Env V X)
    (requests : List (F.Request (V := V) (X := X) (s := s)))
    {stock : SourceInventoryExecutionFeed.Inventory (V := V) (X := X) (s := s)}
    (whole : OccurrenceBlock (F.executedTrace decoder requests) stock.trace)
    (requestIndex : Fin requests.length)
    (stepIndex : Fin (P.words (F.receipt decoder (requests.get requestIndex))).length) :
    PositionIn (stock := stock) whole := by
  let paid := F.receipt decoder (requests.get requestIndex)
  let chosen := P.stepOccurrence paid stepIndex
  let chunk := (SourceOperationPaidRelations.exposure paid).trace
  let front := F.executedTrace decoder (requests.take requestIndex.val)
  let back := F.executedTrace decoder (requests.drop (requestIndex.val+1))
  have selected : chunk[chosen.before.length]? = some (.relation chosen.word) := by
    change (SourceOperationPaidRelations.exposure paid).trace[chosen.before.length]? = _
    rw [chosen.trace_eq, List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero]
  have requests_split : requests = requests.take requestIndex.val ++ [requests.get requestIndex] ++
      requests.drop (requestIndex.val+1) := by
    rw [List.append_assoc]
    exact (List.take_append_drop requestIndex.val requests).symm.trans
      (congrArg (requests.take requestIndex.val ++ ·) (List.drop_eq_getElem_cons requestIndex.isLt))
  have full : F.executedTrace decoder requests = front ++ chunk ++ back :=
    (congrArg (F.executedTrace decoder) requests_split).trans (by
      simp only [executedTrace_append, executedTrace_single, front, chunk, back, paid])
  let offset := front.length + chosen.before.length
  have inBatch : (F.executedTrace decoder requests)[offset]? = some (.relation chosen.word) :=
    (congrArg (fun events : List (F.Event (V := V) (X := X) (s := s)) => events[offset]?) full).trans
      (append_hit front chunk back selected)
  have inside := (List.getElem?_eq_some_iff.mp inBatch).elim (fun bound _ => bound)
  let position := whole.before.length + offset
  refine ⟨position, chosen.word, ?_, Nat.add_lt_add_left inside _, ?_⟩
  · dsimp only [position]
    omega
  · exact (congrArg (fun events : List (F.Event (V := V) (X := X) (s := s)) => events[position]?)
      whole.trace_eq).trans (append_hit whole.before _ whole.after inBatch)

local instance levelGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value W grade t) := Cfa.groups W grade

set_option cleanup.letToHave false in
private def literalPaidStep (native : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (target : Cfa.AdmissionPacket (W := W) (X := Y) (s := s))
    (language : X = Y) (same : Cfa.packetTransport language native = target)
    (stock : R.InventoryAt native) (installed : native.2.1.1.inventory = some stock)
    (decoder : Env (Cfa.Value W native.1) X)
    (requests : List (F.Request (V := Cfa.Value W native.1) (X := X) (s := s)))
    (whole : OccurrenceBlock (F.executedTrace decoder requests) stock.trace)
    (requestIndex : Fin requests.length)
    (stepIndex : Fin (P.words (F.receipt decoder (requests.get requestIndex))).length) :
    let literal := block_reindex native target language same stock installed (F.executedTrace decoder requests) whole
    PositionIn (stock := literal.1) literal.2.2.1 := by
  cases language
  cases same
  exact fromPaidStep decoder requests whole requestIndex stepIndex

end Forward

local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance actualGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value A.W grade t) := Cfa.groups A.W grade

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
local notation "nextSite" => site ((update+2)+1)
local notation "native" => Cfa.sourceBorn factory current
set_option quotPrecheck false in
local notation "language" => (current).2.2.2.down
local notation "recognition" => following_literal observation nontrivial half depth ordinal (update := update)
local notation "born" => N.actualBirth observation nontrivial half depth ordinal method
local notation "requests" => B.requests factory current born
local notation "selected" => Cfa.selected factory current
set_option quotPrecheck false in
local notation "base" => (Cfa.nativePacket factory current).2.2.1
local notation "decoder" => Cfa.stockDecodedEnvironment selected base
local notation "literal" => B.actualBlock observation nontrivial half depth ordinal method

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
private def selectedActualInput (requestIndex : Fin (requests).length)
    (stepIndex : Fin (P.words (F.receipt decoder ((requests).get requestIndex))).length) :=
  literalPaidStep native nextSite language recognition
    (Cfa.bornStock factory current) (Cfa.born_inventory factory current)
    decoder requests (B.nextBlock factory current born) requestIndex stepIndex

run_cmd IO.eprintln "CP529_CONTROL + original_paid_step_at_literal_next"
set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
theorem original_paid_step_at_literal_next (requestIndex : Fin (requests).length)
    (stepIndex : Fin (P.words (F.receipt decoder ((requests).get requestIndex))).length) :
    let input := selectedActualInput observation nontrivial half depth ordinal method requestIndex stepIndex
    let found := actualPosition observation nontrivial half depth ordinal method
      input.position input.word input.lower input.upper input.actual
    let consumed := actual_position_consumption observation nontrivial half depth ordinal method
      input.position input.word input.lower input.upper input.actual
    (type_of% (found.request_source)) ∧ (type_of% (found.paid_source)) ∧
    (type_of% (found.cut.trace_eq)) ∧ found.installedRelation.inventory = (literal).1 ∧
    found.installedRelation.val = input.word ∧
    (found.execution.step found.index).before.length = input.position ∧ (type_of% consumed) := by
  let input := selectedActualInput observation nontrivial half depth ordinal method requestIndex stepIndex
  let found := actualPosition observation nontrivial half depth ordinal method
    input.position input.word input.lower input.upper input.actual
  let consumed := actual_position_consumption observation nontrivial half depth ordinal method
    input.position input.word input.lower input.upper input.actual
  exact ⟨found.request_source, found.paid_source, found.cut.trace_eq, rfl, rfl,
    found.position_eq, consumed⟩

end CountedPaInitial.CofinalReceiptPositionCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

open Lean Elab Command in
run_cmd do
 let some report ← liftIO <| IO.getEnv "CP529_CANONICAL_REPORT"
  | throwError "set CP529_CANONICAL_REPORT for the same canonical method check"
 let some current ← liftIO <| IO.getEnv "CP529_CANONICAL_CURRENT"
  | throwError "set CP529_CANONICAL_CURRENT for the canonical kernel marker"
 let env ← getEnv
 liftIO <| CofinalReceiptPositionCertificate.sameCanonicalMethod env report current
