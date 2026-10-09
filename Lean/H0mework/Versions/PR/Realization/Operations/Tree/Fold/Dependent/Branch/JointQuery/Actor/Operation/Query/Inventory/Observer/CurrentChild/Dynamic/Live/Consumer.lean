import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Reverse.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootLawDependentJointStateController CofinalHistorySettlement
namespace E.Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (query nextBorn next presentation actual_query actual_next actual_answer)
end E.Shared
namespace F4
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation (rawSource)
end F4
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (anchor : Nat)
variable (frame : Dynamic.Frame root visit recognition)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition) (CurrentChild.resultSlot root recognition))))
local instance : AddCommGroup (CurrentChild.Value root visit recognition (CurrentChild.resultSlot root recognition)) :=
 CurrentChild.instAddCommGroupValue root visit recognition (CurrentChild.resultSlot root recognition)
theorem source_material : (face root visit recognition U7 calculus anchor frame seed).rootRead=
    materialAt root visit recognition U7 calculus anchor (E.epoch frame) seed (E.Shared.actualOccurrence frame) := rfl
theorem source_query : (E.Shared.query frame (configuration root visit recognition U7 calculus anchor seed)).raw=
 rawAt root visit recognition U7 calculus anchor (E.epoch frame) seed (E.Shared.actualOccurrence frame) := rfl
theorem raw_value {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Dynamic.C.Occurrence frame (current:=current)) : type_of% (JointLow.source_value
 (originalRawAt root visit recognition frame seed supplied).environment
  (dynamicRawAt root visit recognition U7 calculus anchor frame supplied).environment
  (originalRawAt root visit recognition frame seed supplied).expression
  (dynamicRawAt root visit recognition U7 calculus anchor frame supplied).expression) := JointLow.source_value
 (originalRawAt root visit recognition frame seed supplied).environment
  (dynamicRawAt root visit recognition U7 calculus anchor frame supplied).environment
  (originalRawAt root visit recognition frame seed supplied).expression
  (dynamicRawAt root visit recognition U7 calculus anchor frame supplied).expression
theorem raw_fee {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Dynamic.C.Occurrence frame (current:=current)) :
 remaining (rawAt root visit recognition U7 calculus anchor frame seed supplied).expression =
 remaining (originalRawAt root visit recognition frame seed supplied).expression+
 remaining (dynamicRawAt root visit recognition U7 calculus anchor frame supplied).expression+1 := JointLow.source_charge _ _ _ _
theorem paid_value {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Dynamic.C.Occurrence frame (current:=current)) :
 (paidAt root visit recognition U7 calculus anchor frame seed supplied).2.2.1=
 (rawAt root visit recognition U7 calculus anchor frame seed supplied).expression.eval
  (rawAt root visit recognition U7 calculus anchor frame seed supplied).environment :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
theorem paid_fee {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Dynamic.C.Occurrence frame (current:=current)) :
 (paidAt root visit recognition U7 calculus anchor frame seed supplied).2.1.2.length=
 remaining (rawAt root visit recognition U7 calculus anchor frame seed supplied).expression :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem recover_dynamic {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Dynamic.C.Occurrence frame (current:=current)) :
 Sub.sub (α:=PairValue (CurrentChild.Value root visit recognition) (CurrentChild.resultSlot root recognition))
  (paidAt root visit recognition U7 calculus anchor frame seed supplied).2.2.1
  ((originalRawAt root visit recognition frame seed supplied).expression.eval
   (originalRawAt root visit recognition frame seed supplied).environment) =
 (dynamicRawAt root visit recognition U7 calculus anchor frame supplied).expression.eval
  (dynamicRawAt root visit recognition U7 calculus anchor frame supplied).environment := by
 rw [paid_value]
 dsimp only [rawAt]
 rw [raw_value]
 exact add_sub_cancel_left _ _
def recoveredValueAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Dynamic.C.Occurrence frame (current:=current)) :=
 Sub.sub (α:=PairValue (CurrentChild.Value root visit recognition) (CurrentChild.resultSlot root recognition))
  (paidAt root visit recognition U7 calculus anchor frame seed supplied).2.2.1
  ((originalRawAt root visit recognition frame seed supplied).expression.eval
   (originalRawAt root visit recognition frame seed supplied).environment)
theorem recover_current {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Dynamic.C.Occurrence frame (current:=current)) :
 (recoveredValueAt root visit recognition U7 calculus anchor frame seed supplied).1=
 (Dynamic.paidAt root visit recognition U7 calculus anchor frame supplied).2.2.1 := by
 have pairValue := congrArg Prod.fst (recover_dynamic root visit recognition U7 calculus anchor frame seed supplied)
 have lifted := eval_liftExpr (Dynamic.rawAt root visit recognition U7 calculus anchor frame supplied).expression
  (Dynamic.environmentAt root visit recognition frame supplied) (Dynamic.Action.incrementAt root visit recognition frame supplied)
 have firstValue := congrArg Prod.fst lifted
 have paidValue := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (E.Shared.base frame).root.toAuthoritativeRoot
  (fun {_current} occurrence => Dynamic.rawAt root visit recognition U7 calculus anchor frame occurrence) supplied
 exact pairValue.trans (firstValue.trans paidValue.symm)
theorem born_environment : (E.Shared.nextBorn frame (configuration root visit recognition U7 calculus anchor seed)).environment
    ((E.Shared.nextBorn frame (configuration root visit recognition U7 calculus anchor seed)).old.root.emitted
      (E.Shared.nextBorn frame (configuration root visit recognition U7 calculus anchor seed)).old.visit.current)=
    Dynamic.generatedEnvironmentAt root visit recognition (E.epoch frame) (E.Shared.actualOccurrence frame) := rfl
theorem born_scalar : (E.Shared.nextBorn frame (configuration root visit recognition U7 calculus anchor seed)).inventory=
    some (nextScalar root visit recognition U7 calculus anchor frame seed) := rfl
theorem born_pair : (E.Shared.nextBorn frame (configuration root visit recognition U7 calculus anchor seed)).pairInventory=
    some (nextPair root visit recognition U7 calculus anchor frame seed) := rfl
theorem accumulated_preserved (event) (present : event ∈ (accumulated root visit recognition U7 calculus anchor frame).trace) :
    event ∈ (nextScalar root visit recognition U7 calculus anchor frame seed).trace := by
  unfold nextScalar
  cases (R.programme seed).nextInventory frame with
  | none => exact present
  | some original => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem original_scalar_write (original) (hasOriginal : (R.programme seed).nextInventory frame=some original)
    (event) (present : event ∈ original.trace) : event ∈ (nextScalar root visit recognition U7 calculus anchor frame seed).trace := by
  unfold nextScalar
  rw [hasOriginal]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem action_preserved (event) (present : event ∈ (written root visit recognition U7 calculus anchor frame).trace) :
    event ∈ (nextScalar root visit recognition U7 calculus anchor frame seed).trace :=
  accumulated_preserved root visit recognition U7 calculus anchor frame seed event ((SourceHistoryCommon.parallel_right _ _ _).1 event present)
theorem scalar_preserved (prior) (hasPrior : frame.inventory=some prior) (event) (present : event ∈ prior.trace) :
    event ∈ (nextScalar root visit recognition U7 calculus anchor frame seed).trace := by
  apply accumulated_preserved root visit recognition U7 calculus anchor frame seed event
  unfold accumulated
  rw [hasPrior]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
theorem pair_written_preserved (event) (present : event ∈ (pairWritten root visit recognition U7 calculus anchor frame).trace) :
    event ∈ (nextPair root visit recognition U7 calculus anchor frame seed).trace := by
  unfold nextPair
  cases (R.programme seed).nextPairInventory frame with
  | none => exact present
  | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem old_pair_preserved (prior) (hasPrior : (R.programme seed).nextPairInventory frame=some prior)
    (event) (present : event ∈ prior.trace) : event ∈ (nextPair root visit recognition U7 calculus anchor frame seed).trace := by
  unfold nextPair
  rw [hasPrior]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem born_written (event) (present : event ∈ (written root visit recognition U7 calculus anchor frame).trace) :
 event ∈ (nextScalar root visit recognition U7 calculus anchor frame seed).trace :=
 action_preserved root visit recognition U7 calculus anchor frame seed event present
theorem new_paid_next (settled) (actual : frame.action=.inl settled) (event)
 (present : event ∈ (written root visit recognition U7 calculus anchor frame).trace) :
 (E.Shared.next frame (configuration root visit recognition U7 calculus anchor seed)).inventory=
 some (nextScalar root visit recognition U7 calculus anchor frame seed) ∧
 event ∈ (nextScalar root visit recognition U7 calculus anchor frame seed).trace := by
 constructor
 · unfold E.Shared.next
   rw [actual]
   rfl
 · exact action_preserved root visit recognition U7 calculus anchor frame seed event present
theorem prior_next (prior) (hasPrior : frame.inventory=some prior) (event) (present : event ∈ prior.trace) :
 ∃ written, (E.Shared.next frame (configuration root visit recognition U7 calculus anchor seed)).inventory=some written ∧
 event ∈ written.trace := by
 unfold E.Shared.next
 cases frame.action with
 | inr paid => exact ⟨prior,hasPrior,present⟩
 | inl settled => exact ⟨nextScalar root visit recognition U7 calculus anchor frame seed,rfl,
   scalar_preserved root visit recognition U7 calculus anchor frame seed prior hasPrior event present⟩
theorem math_environment {current : frame.V.Current}
    (occurrence : frame.old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    frame.mathNext.environment occurrence=frame.environment occurrence := rfl
variable (sourceStage : Nat)
theorem initial_source : initial root visit recognition U7 calculus anchor sourceStage=
 CurrentChild.Installation.initial root visit recognition U7 calculus anchor sourceStage := rfl
theorem actual_initial : (runtime root visit recognition U7 calculus anchor sourceStage).initialState.engine.node=
    .active (E.Shared.presentation (initial root visit recognition U7 calculus anchor sourceStage) (programme root visit recognition U7 calculus anchor sourceStage)) := rfl
theorem actual_input (stage : Nat) : type_of%
    (E.Shared.actual_query (initial root visit recognition U7 calculus anchor sourceStage) (programme root visit recognition U7 calculus anchor sourceStage) stage) :=
  E.Shared.actual_query _ _ stage
theorem actual_next (stage : Nat) : type_of%
    (E.Shared.actual_next (initial root visit recognition U7 calculus anchor sourceStage) (programme root visit recognition U7 calculus anchor sourceStage) stage) :=
  E.Shared.actual_next _ _ stage
theorem actual_answer (stage : Nat) : type_of%
    (E.Shared.actual_answer (initial root visit recognition U7 calculus anchor sourceStage) (programme root visit recognition U7 calculus anchor sourceStage) stage) :=
  E.Shared.actual_answer _ _ stage


abbrev rawSource := SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.rawSource
 (initial root visit recognition U7 calculus anchor sourceStage) (programme root visit recognition U7 calculus anchor sourceStage)
theorem inverse_whole (stage : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_write
 (runtime root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 ((runtime root visit recognition U7 calculus anchor sourceStage).stateAt stage)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_write _ _ _
theorem inverse_next (stage : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_next
 (runtime root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 ((runtime root visit recognition U7 calculus anchor sourceStage).stateAt stage)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_next _ _ _
theorem macro_payment (stage : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current
 (programme root visit recognition U7 calculus anchor sourceStage) (initial root visit recognition U7 calculus anchor sourceStage) stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current _ _ stage
theorem no_refill (stage : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill
 (programme root visit recognition U7 calculus anchor sourceStage) (frameAt root visit recognition U7 calculus anchor sourceStage stage)) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill _ _
theorem noetherian (stage : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded
 (programme root visit recognition U7 calculus anchor sourceStage) (frameAt root visit recognition U7 calculus anchor sourceStage stage)) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded _ _
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
