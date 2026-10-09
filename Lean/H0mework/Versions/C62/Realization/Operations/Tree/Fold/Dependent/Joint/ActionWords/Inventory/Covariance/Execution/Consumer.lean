import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.Execution.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.Execution
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution SourceGeneratedIntegralCoherentCompletion
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
variable (actor : Actor root recognition visit successor)


variable (point : Carrier root recognition visit successor) (word : List (Letter root recognition visit successor))
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count actor point word)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count actor point word =
    effect root recognition visit successor transition alignment U7 calculus count actor
      (selectedPoint root recognition visit successor transition alignment U7 calculus count actor point word) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count actor point word)).trans
      (programme_value root recognition visit successor transition alignment U7 calculus count actor point word)
theorem cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count actor point word)).length=5 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (programme_cost root recognition visit successor transition alignment U7 calculus count actor)
def materialFace : SourceNativeRootSemanticFaceAt
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word) visit where
  projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface root.source.base
    (component root recognition visit successor transition alignment U7 calculus count actor point word)).embed (.inl PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl
theorem source_read : (materialFace root recognition visit successor transition alignment U7 calculus count actor point word).rootRead.2.2.2.1 =
    selected root recognition visit successor transition alignment U7 calculus count actor := rfl

theorem branch_effect : SourceGeneratedCovarianceExecution.EffectPredicate
    (feature root recognition visit successor transition alignment U7 calculus count actor)
    (action root recognition visit successor transition alignment U7 calculus count actor)
    (selected root recognition visit successor transition alignment U7 calculus count actor)
    (normal root recognition visit successor transition alignment U7 calculus count actor point word) := by
  rw [normal_value]
  exact SourceGeneratedCovarianceExecution.source_effect_predicate _ _ _
    (current root recognition visit successor transition alignment U7 calculus count point word)

theorem actual_environment {current : (frame root recognition visit successor transition alignment U7 calculus count actor point word).V.Current}
    (occurrence : (frame root recognition visit successor transition alignment U7 calculus count actor point word).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (frame root recognition visit successor transition alignment U7 calculus count actor point word).environment occurrence =
      environmentAt root recognition visit successor transition alignment U7 calculus count
        ((action root recognition visit successor transition alignment U7 calculus count actor).integralTransition
          (selectedPoint root recognition visit successor transition alignment U7 calculus count actor point word)) := rfl
namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
  (queryAt nextAt no_refill noetherian installed_born_inventory old_past_born)
end Request
theorem query_next (stage : Nat) : type_of% (Request.queryAt
    (seed root recognition visit successor transition alignment U7 calculus count actor point word)
    (frame root recognition visit successor transition alignment U7 calculus count actor point word) stage) ∧
    type_of% (Request.nextAt
      (seed root recognition visit successor transition alignment U7 calculus count actor point word)
      (frame root recognition visit successor transition alignment U7 calculus count actor point word) stage) :=
  ⟨Request.queryAt _ _ stage,Request.nextAt _ _ stage⟩
theorem same_debt (stage : Nat) : type_of% (Request.no_refill
    (seed root recognition visit successor transition alignment U7 calculus count actor point word)
    (frame root recognition visit successor transition alignment U7 calculus count actor point word) stage) ∧
    type_of% (Request.noetherian
      (seed root recognition visit successor transition alignment U7 calculus count actor point word)
      (frame root recognition visit successor transition alignment U7 calculus count actor point word) stage) :=
  ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩
theorem born_inventory : type_of% (Request.installed_born_inventory
    (seed root recognition visit successor transition alignment U7 calculus count actor point word)
    (frame root recognition visit successor transition alignment U7 calculus count actor point word)) :=
  Request.installed_born_inventory _ _
theorem all_inventory : type_of% (Request.old_past_born
    (seed root recognition visit successor transition alignment U7 calculus count actor point word)
    (frame root recognition visit successor transition alignment U7 calculus count actor point word)) :=
  Request.old_past_born _ _
def parentFace : SourceNativeRootSemanticFaceAt
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word) visit where
  projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface root.source.base
    (component root recognition visit successor transition alignment U7 calculus count actor point word)).embed (.inr PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

theorem parent_source : (parentFace root recognition visit successor transition alignment U7 calculus count actor point word).rootRead =
    parentMaterial root recognition visit successor transition alignment U7 calculus count actor point word := rfl

theorem old_pair_inventory : (frame root recognition visit successor transition alignment U7 calculus count actor point word).pairInventory=
    some (pairExposure root recognition visit successor transition alignment U7 calculus count actor point word) := rfl

theorem old_pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count)) Var Slot.measured))
    (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count actor point word).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (seed root recognition visit successor transition alignment U7 calculus count actor point word)
      (frame root recognition visit successor transition alignment U7 calculus count actor point word)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (frame root recognition visit successor transition alignment U7 calculus count actor point word))).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.Execution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
