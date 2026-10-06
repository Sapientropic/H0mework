import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
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

variable (selectedLetter : Letter root recognition visit successor)
variable (point : Carrier root recognition visit successor) (word : List (Letter root recognition visit successor))
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count selectedLetter point word).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count selectedLetter point word =
    effect root recognition visit successor transition alignment U7 calculus count selectedLetter
      (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (programme_value root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
theorem original_effect (index : Index root recognition visit successor) :
    normal root recognition visit successor transition alignment U7 calculus count selectedLetter point word index =
      EffectHistory.total root recognition visit successor transition alignment U7 calculus count
        (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point)
        [selectedLetter] (actor root recognition visit successor index) := by
  rw [normal_value,Inventory.normal_value,SourceGeneratedActionWords.run_source]
  exact effect_full root recognition visit successor transition alignment U7 calculus count selectedLetter index _
theorem cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count selectedLetter point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count selectedLetter point word)).length=7 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (programme_cost root recognition visit successor transition alignment U7 calculus count selectedLetter)
abbrev pairExposure := SourceOperationPaidRelations.exposure
  (pairResult root recognition visit successor transition alignment U7 calculus count selectedLetter point word).2.1.2

theorem pair_inventory : (frame root recognition visit successor transition alignment U7 calculus count selectedLetter point word).pairInventory=
    some (pairExposure root recognition visit successor transition alignment U7 calculus count selectedLetter point word) := rfl
theorem pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count)) Var Slot.measured))
    (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count selectedLetter point word).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (seed root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
      (frame root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (frame root recognition visit successor transition alignment U7 calculus count selectedLetter point word))).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem pair_same_execution : HEq (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count selectedLetter point word).toAuthoritativeRoot visit.current
    (pairReader root recognition visit successor transition alignment U7 calculus count selectedLetter point word))
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
      (pairReader root recognition visit successor transition alignment U7 calculus count selectedLetter point word)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _
    (pairRaw root recognition visit successor transition alignment U7 calculus count selectedLetter point word)

namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
  (queryAt nextAt no_refill noetherian installed_born_inventory old_past_born)
end Request
theorem query_next (stage : Nat) : type_of% (Request.queryAt
    (seed root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
    (frame root recognition visit successor transition alignment U7 calculus count selectedLetter point word) stage) ∧
    type_of% (Request.nextAt
      (seed root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
      (frame root recognition visit successor transition alignment U7 calculus count selectedLetter point word) stage) :=
  ⟨Request.queryAt _ _ stage,Request.nextAt _ _ stage⟩
theorem same_debt (stage : Nat) : type_of% (Request.no_refill
    (seed root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
    (frame root recognition visit successor transition alignment U7 calculus count selectedLetter point word) stage) ∧
    type_of% (Request.noetherian
      (seed root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
      (frame root recognition visit successor transition alignment U7 calculus count selectedLetter point word) stage) :=
  ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩
theorem born_inventory : type_of% (Request.installed_born_inventory
    (seed root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
    (frame root recognition visit successor transition alignment U7 calculus count selectedLetter point word)) :=
  Request.installed_born_inventory _ _
theorem all_inventory : type_of% (Request.old_past_born
    (seed root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
    (frame root recognition visit successor transition alignment U7 calculus count selectedLetter point word)) :=
  Request.old_past_born _ _
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
