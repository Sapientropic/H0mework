import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptBlock
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1

run_cmd Lean.modifyEnv fun env =>
 Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CofinalReceiptBlockCertificate"

namespace CofinalReceiptBlockCertificate
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
 let b := prefixName ++ "BornRNativeGammaInstall.PhysicalGammaNextReceiptBlock."
 let claims : Array (String × Array String) := #[
   (prefixName ++ "CofinalReceiptBlockCertificate.literal_block_facts", #[]),
   (b ++ "actual_batch_boundary", #[]),
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
 let name := `CofinalReceiptBlockCertificate.direct_same_canonical_method
 require ((env.find? name).isNone) "CANONICAL_CONTROL_ALREADY_INSTALLED"
 let declaration : Declaration := .thmDecl {
  name := name, levelParams := canonical.levelParams, type := target, value := value, all := [name] }
 let started ← IO.monoMsNow
 write current <| Json.mkObj [("phase",toJson "kernel-start"),("CI",toJson name.toString),
  ("monotonic_ms",toJson started)]
 IO.eprintln "CP521_CANONICAL_KERNEL_START"
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
  write report <| Json.mkObj [("schema",toJson "cp521-canonical-shared-method-application/v1"),
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
  IO.eprintln s!"CP521_CANONICAL_KERNEL_PASS {elapsed}ms"

end CofinalReceiptBlockCertificate


noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalReceiptBlockCertificate

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement
open ActualNativeRelationTransport (OccurrenceBlock)

namespace Feed
export SourceInventoryExecutionFeed (Inventory Request requests requestsFrom receipt receipt_cost written)
export SourceInventoryExecutionFeed.ReceiptOccurrence (writtenBlock executedTrace requestWord)
end Feed
namespace P
export SourceOperationPaidRelations (events events_trace exposure words paid_boundary stepOccurrence stepOccurrence_before_length)
end P
namespace W
export SourceInventoryExecutionFeed.WordReceipt (sourceRequest source_request_member)
end W

private abbrev ToyValue : Unit → Type := fun _ => ℤ
private abbrev ToyVar : Unit → Type := fun _ => Unit
private abbrev ToyExpr := Expr ToyValue ToyVar ()
private abbrev ToyWord := Formal ℤ ToyValue ToyVar ()
private abbrev ToyRequest := Feed.Request (V := ToyValue) (X := ToyVar) (s := ())

private def toyEnv : Env ToyValue ToyVar := fun _ _ => 2
private def toyStart : ToyExpr := .add (.var ()) (.const 1)
private def toyMiddle : ToyExpr := .add (.const 2) (.const 1)
private def toyEnd : ToyExpr := .const 3
private def toyPaid := execution toyEnv toyStart
private def toyStock := P.exposure toyPaid
private def toyEvents := (P.words toyPaid).map PresentedRelationEventAt.relation

private def toySourceBlock : OccurrenceBlock toyEvents toyStock.trace :=
  ⟨[.generator toyStart], [], by
    change .generator toyStart :: RootedAccountedUnfolding.traceBranches (P.events toyPaid) =
      [.generator toyStart] ++ toyEvents ++ []
    simpa only [toyEvents, List.append_nil, List.singleton_append] using
      congrArg (List.cons (.generator toyStart)) (P.events_trace toyPaid)⟩

private def toyRequests := Feed.requestsFrom toySourceBlock.before.length toyEvents
private def toyWritten := Feed.writtenBlock toyEnv toyStock toyEvents toySourceBlock
private def toyRoot : ToyRequest := ⟨0, .generator toyStart, toyStart, 1⟩
private theorem toyRequestSplit : Feed.requests toyStock = toyRoot :: toyRequests := by
  change Feed.requestsFrom 0
    (.generator toyStart :: RootedAccountedUnfolding.traceBranches (P.events toyPaid)) = _
  exact congrArg (fun events => Feed.requestsFrom 0 (.generator toyStart :: events))
    (P.events_trace toyPaid)

private def toyFirstIndex : Fin (P.words toyPaid).length := ⟨0, by decide⟩
private def toySecondIndex : Fin (P.words toyPaid).length := ⟨1, by decide⟩
private def toyFirst := P.stepOccurrence toyPaid toyFirstIndex
private def toySecond := P.stepOccurrence toyPaid toySecondIndex
private def toyNegative : ToyRequest := W.sourceRequest toyFirst (toyMiddle, -1)
private def toyPositive : ToyRequest := W.sourceRequest toySecond (toyMiddle, 1)

private theorem toyMiddle_ne_start : toyMiddle ≠ toyStart := by
  intro same
  change ((.add (.const 2) (.const 1)) : ToyExpr) = .add (.var ()) (.const 1) at same
  have impossible := (Expr.add.inj same).1
  cases impossible

private theorem toyMiddle_ne_end : toyMiddle ≠ toyEnd := by
  intro same
  change ((.add (.const 2) (.const 1)) : ToyExpr) = .const 3 at same
  cases same

private theorem toyNegative_coeff : toyFirst.word toyMiddle = -1 := by
  change ((Finsupp.single toyStart 1 - Finsupp.single toyMiddle 1) : ToyWord) toyMiddle = -1
  rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne toyMiddle_ne_start, Finsupp.single_eq_same, zero_sub]

private theorem toyPositive_coeff : toySecond.word toyMiddle = 1 := by
  change ((Finsupp.single toyMiddle 1 - Finsupp.single toyEnd 1) : ToyWord) toyMiddle = 1
  rw [Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne toyMiddle_ne_end, sub_zero]

private theorem toyNegative_position : toyNegative.position = 1 :=
  (P.stepOccurrence_before_length toyPaid toyFirstIndex).trans rfl

private theorem toyPositive_position : toyPositive.position = 2 :=
  (P.stepOccurrence_before_length toyPaid toySecondIndex).trans rfl

private theorem toySupportItem {word : ToyWord} (active : word toyMiddle ≠ 0) :
    (toyMiddle, word toyMiddle) ∈ Coefficients.sourceItems word := by
  change (toyMiddle, word toyMiddle) ∈ word.support.toList.map (fun expression => (expression, word expression))
  exact List.mem_map.mpr ⟨toyMiddle, Finset.mem_toList.mpr (Finsupp.mem_support_iff.mpr active), rfl⟩

private theorem toyInBlock {item : ToyRequest} (member : item ∈ Feed.requests toyStock)
    (later : item.position ≠ 0) : item ∈ toyRequests := by
  rw [toyRequestSplit] at member
  rcases List.mem_cons.mp member with front | inside
  · exact (later (congrArg (fun request : ToyRequest => request.position) front)).elim
  · exact inside

private theorem toyNegative_member : toyNegative ∈ toyRequests := by
  have nonzero : toyFirst.word toyMiddle ≠ 0 := by rw [toyNegative_coeff]; decide
  have item : (toyMiddle, -1) ∈ Coefficients.sourceItems toyFirst.word := by
    simpa only [toyNegative_coeff] using toySupportItem nonzero
  exact toyInBlock (W.source_request_member toyFirst _ item) (by rw [toyNegative_position]; decide)

private theorem toyPositive_member : toyPositive ∈ toyRequests := by
  have nonzero : toySecond.word toyMiddle ≠ 0 := by rw [toyPositive_coeff]; decide
  have item : (toyMiddle, 1) ∈ Coefficients.sourceItems toySecond.word := by
    simpa only [toyPositive_coeff] using toySupportItem nonzero
  exact toyInBlock (W.source_request_member toySecond _ item) (by rw [toyPositive_position]; decide)

run_cmd IO.eprintln "CP521_CONTROL + two_paid_steps_retain_opposite_requests"
theorem two_paid_steps_retain_opposite_requests :
    toyNegative ∈ toyRequests ∧ toyPositive ∈ toyRequests ∧
    toyNegative.position = 1 ∧ toyPositive.position = 2 ∧
    toyNegative.expression = toyPositive.expression ∧
    toyNegative.coefficient = -1 ∧ toyPositive.coefficient = 1 ∧
    (Feed.receipt toyEnv toyNegative).length = 1 ∧
    (Feed.receipt toyEnv toyPositive).length = 1 ∧
    Feed.requestWord toyEnv toyNegative + Feed.requestWord toyEnv toyPositive = 0 ∧
    (Feed.written toyEnv toyStock).trace =
      toyWritten.before ++ Feed.executedTrace toyEnv toyRequests ++ toyWritten.after := by
  refine ⟨toyNegative_member, toyPositive_member, toyNegative_position, toyPositive_position,
    rfl, rfl, rfl, (Feed.receipt_cost toyEnv toyNegative).trans rfl,
    (Feed.receipt_cost toyEnv toyPositive).trans rfl, ?_, toyWritten.trace_eq⟩
  let payment := (P.words (execution toyEnv toyMiddle)).sum
  change (-1 : ℤ) • payment + (1 : ℤ) • payment = 0
  simp

run_cmd IO.eprintln "CP521_CONTROL - early_sum_erases_both_middle_requests"
theorem early_sum_erases_both_middle_requests :
    ¬ ∃ item ∈ Feed.requestsFrom toySourceBlock.before.length [.relation (P.words toyPaid).sum],
      (item : ToyRequest).expression = toyMiddle := by
  have endpoint : (P.words toyPaid).sum =
      (Finsupp.single toyStart 1 - Finsupp.single toyEnd 1 : ToyWord) :=
    (P.paid_boundary toyPaid).trans (toyPaid.relation_boundary (R := ℤ))
  have canceled : (P.words toyPaid).sum toyMiddle = 0 := by
    rw [endpoint, Finsupp.sub_apply, Finsupp.single_eq_of_ne toyMiddle_ne_start,
      Finsupp.single_eq_of_ne toyMiddle_ne_end, sub_self]
  intro ⟨item, member, same⟩
  change item ∈ (Coefficients.sourceItems (P.words toyPaid).sum).map (fun entry =>
    (⟨toySourceBlock.before.length, .relation (P.words toyPaid).sum, entry.1, entry.2⟩ : ToyRequest)) ++ [] at member
  rw [List.append_nil] at member
  obtain ⟨entry, included, written⟩ := List.mem_map.mp member
  have entrySame : entry.1 = toyMiddle :=
    (congrArg (fun request : ToyRequest => request.expression) written).trans same
  unfold Coefficients.sourceItems at included
  obtain ⟨expression, supported, exactEntry⟩ := List.mem_map.mp included
  have exprSame : expression = toyMiddle := (congrArg Prod.fst exactEntry).trans entrySame
  exact (Finsupp.mem_support_iff.mp (Finset.mem_toList.mp supported)) (by rw [exprSame, canceled])

end CofinalReceiptBlockCertificate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.CofinalReceiptBlockCertificate
open CenteredGram.IntegralGraphJointAction
open BornRNativeGammaInstall.PhysicalGammaNextReceiptBlock

set_option cleanup.letToHave false in
theorem literal_block_facts
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : ℕ, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
    {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
    {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
    {update cutoff : Nat}
    (method : BornRSourcePrice.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
      (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
      observation nontrivial half depth ordinal update cutoff) :
    let block := actualBlock observation nontrivial half depth ordinal method
    (type_of% (block.2.2.property)) ∧ (type_of% (block.2.2.val.trace_eq)) :=
  let block := actualBlock observation nontrivial half depth ordinal method
  And.intro block.2.2.property block.2.2.val.trace_eq

end CountedPaInitial.CofinalReceiptBlockCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

open Lean Elab Command in
run_cmd do
 let some report ← liftIO <| IO.getEnv "CP521_CANONICAL_REPORT"
  | throwError "set CP521_CANONICAL_REPORT for the same canonical method check"
 let some current ← liftIO <| IO.getEnv "CP521_CANONICAL_CURRENT"
  | throwError "set CP521_CANONICAL_CURRENT for the canonical kernel marker"
 let env ← getEnv
 liftIO <| CofinalReceiptBlockCertificate.sameCanonicalMethod env report current
