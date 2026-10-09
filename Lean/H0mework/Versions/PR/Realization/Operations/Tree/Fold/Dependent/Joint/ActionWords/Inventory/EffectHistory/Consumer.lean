import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)

variable (point : I.Carrier root recognition visit successor)
variable (word : List (I.Letter root recognition visit successor))
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count point word)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count point word =
    total root recognition visit successor transition alignment U7 calculus count point word :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (programme_value root recognition visit successor transition alignment U7 calculus count point word)
theorem first_step_paid (selected : I.Letter root recognition visit successor)
    (tail : List (I.Letter root recognition visit successor))
    (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr (Value root recognition visit successor) Var Slot.waves))
    (present : event ∈ (SourceOperationPaidRelations.exposure
      (singleResult root recognition visit successor transition alignment U7 calculus count selected point).2.1.2).trace) :
    event ∈ (completeInventory root recognition visit successor transition alignment U7 calculus count point (selected::tail)).trace := by
  apply (SourceHistoryCommon.parallel_right _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem history_member (walked tail : List (I.Letter root recognition visit successor))
    (selected : I.Letter root recognition visit successor)
    (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr (Value root recognition visit successor) Var Slot.waves))
    (present : event ∈ (SourceOperationPaidRelations.exposure
      (singleResult root recognition visit successor transition alignment U7 calculus count selected
        (SourceGeneratedActionWords.run (I.actions root recognition visit successor transition alignment U7 calculus count) walked point)).2.1.2).trace) :
    event ∈ (historyInventory root recognition visit successor transition alignment U7 calculus count (walked++selected::tail) point).trace := by
  induction walked generalizing point with
  | nil => exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
  | cons letter rest previous =>
    apply (SourceHistoryCommon.parallel_right _ _ _).1
    exact previous (I.actions root recognition visit successor transition alignment U7 calculus count letter point) present

theorem all_step_paid (walked tail : List (I.Letter root recognition visit successor))
    (selected : I.Letter root recognition visit successor)
    (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr (Value root recognition visit successor) Var Slot.waves))
    (present : event ∈ (SourceOperationPaidRelations.exposure
      (singleResult root recognition visit successor transition alignment U7 calculus count selected
        (SourceGeneratedActionWords.run (I.actions root recognition visit successor transition alignment U7 calculus count) walked point)).2.1.2).trace) :
    event ∈ (completeInventory root recognition visit successor transition alignment U7 calculus count point (walked++selected::tail)).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event
    (history_member root recognition visit successor transition alignment U7 calculus count point walked tail selected event present)

def materialFace : SourceNativeRootSemanticFaceAt
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point word) visit where
  projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (I.sourceRoot root recognition visit successor transition alignment U7 calculus count point word).source.base
    (component root recognition visit successor transition alignment U7 calculus count point word)).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem history_read : (materialFace root recognition visit successor transition alignment U7 calculus count point word).rootRead.2.1 =
    sourceHistory root recognition visit successor transition alignment U7 calculus count point word := rfl

theorem cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point word)).length=2*word.length+5 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (programme_budget root recognition visit successor transition alignment U7 calculus count word)

theorem frame_inventory : (frame root recognition visit successor transition alignment U7 calculus count point word).inventory=
    some (completeInventory root recognition visit successor transition alignment U7 calculus count point word) := rfl

namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
  (queryAt nextAt no_refill noetherian installed_born_inventory old_past_born full_scalar_inventory)
end Request

theorem query_next (stage : Nat) : type_of% (Request.queryAt
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word) stage) ∧
    type_of% (Request.nextAt
      (seed root recognition visit successor transition alignment U7 calculus count point word)
      (frame root recognition visit successor transition alignment U7 calculus count point word) stage) :=
  ⟨Request.queryAt _ _ stage,Request.nextAt _ _ stage⟩
theorem same_debt (stage : Nat) : type_of% (Request.no_refill
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word) stage) ∧
    type_of% (Request.noetherian
      (seed root recognition visit successor transition alignment U7 calculus count point word)
      (frame root recognition visit successor transition alignment U7 calculus count point word) stage) :=
  ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩
theorem all_inventory : type_of% (Request.full_scalar_inventory
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word)) :=
  Request.full_scalar_inventory _ _
theorem born_inventory : type_of% (Request.installed_born_inventory
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word)) :=
  Request.installed_born_inventory _ _
theorem inventory_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (Value root recognition visit successor) Var Slot.waves))
    (present : event ∈ (completeInventory root recognition visit successor transition alignment U7 calculus count point word).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.updatedSeed
      (seed root recognition visit successor transition alignment U7 calculus count point word)
      (frame root recognition visit successor transition alignment U7 calculus count point word)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (frame root recognition visit successor transition alignment U7 calculus count point word))).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem actual_environment {current : (frame root recognition visit successor transition alignment U7 calculus count point word).V.Current}
    (occurrence : (frame root recognition visit successor transition alignment U7 calculus count point word).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (frame root recognition visit successor transition alignment U7 calculus count point word).environment occurrence =
      environmentFrom root recognition visit successor
        (SourceGeneratedActionWords.run (I.actions root recognition visit successor transition alignment U7 calculus count) word point) :=
  congrArg (environmentFrom root recognition visit successor)
    (SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.acted_value root recognition visit successor transition alignment U7 calculus count point word)
theorem same_execution : HEq (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point word))
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
      (I.sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
      (originalReader root recognition visit successor transition alignment U7 calculus count point word)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _
    (raw root recognition visit successor transition alignment U7 calculus count point word)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
