import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Words.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Words
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

variable (point : Carrier root recognition visit successor)
variable (seedWord queryWord : List (Letter root recognition visit successor))
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count point seedWord queryWord =
    effect root recognition visit successor transition alignment U7 calculus count queryWord
      (Inventory.normal root recognition visit successor transition alignment U7 calculus count point seedWord) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (programme_equation root recognition visit successor transition alignment U7 calculus count queryWord
      (environment root recognition visit successor transition alignment U7 calculus count point seedWord))
theorem original_effect (index : Index root recognition visit successor) :
    normal root recognition visit successor transition alignment U7 calculus count point seedWord queryWord index =
      EffectHistory.total root recognition visit successor transition alignment U7 calculus count
        (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) seedWord point)
        queryWord (actor root recognition visit successor index) := by
  rw [normal_value,Inventory.normal_value,SourceGeneratedActionWords.run_source]
  exact congrArg (fun values : Space root recognition visit successor => values index)
    (effect_source root recognition visit successor transition alignment U7 calculus count queryWord _)
theorem cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)).length=2*queryWord.length+5 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (programme_budget root recognition visit successor transition alignment U7 calculus count queryWord)
abbrev pairExposure := SourceOperationPaidRelations.exposure
  (pairResult root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).2.1.2

theorem pair_inventory : (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).pairInventory=
    some (pairExposure root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) := rfl
theorem pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count)) Var Slot.measured))
    (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord))).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem pair_same_execution : HEq (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).toAuthoritativeRoot visit.current
    (pairReader root recognition visit successor transition alignment U7 calculus count point seedWord queryWord))
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
      (pairReader root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _
    (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)

namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
  (queryAt nextAt no_refill noetherian installed_born_inventory old_past_born)
end Request
theorem query_next (stage : Nat) : type_of% (Request.queryAt
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) stage) ∧
    type_of% (Request.nextAt
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) stage) :=
  ⟨Request.queryAt _ _ stage,Request.nextAt _ _ stage⟩
theorem same_debt (stage : Nat) : type_of% (Request.no_refill
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) stage) ∧
    type_of% (Request.noetherian
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) stage) :=
  ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩
theorem born_inventory : type_of% (Request.installed_born_inventory
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)) :=
  Request.installed_born_inventory _ _
theorem all_inventory : type_of% (Request.old_past_born
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)) :=
  Request.old_past_born _ _
def materialFace : SourceNativeRootSemanticFaceAt
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) visit where
  projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface root.source.base
    (component root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)).embed (.inl PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

theorem ordered_query_source : (materialFace root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).rootRead.2.2.2.1 =
    EffectHistory.material root recognition visit successor transition alignment U7 calculus count
      (Inventory.acted root recognition visit successor transition alignment U7 calculus count point seedWord).1 queryWord := rfl

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Words
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
