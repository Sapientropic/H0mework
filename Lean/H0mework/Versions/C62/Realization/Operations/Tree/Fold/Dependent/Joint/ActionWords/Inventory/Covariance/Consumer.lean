import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance
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
variable (actor : Actor root recognition visit successor)
variable (point : Carrier root recognition visit successor) (word : List (Letter root recognition visit successor))
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history)
end O
abbrev normal := O.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count actor point word)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count actor point word =
    effect root recognition visit successor transition alignment U7 calculus count actor
      (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word) :=
  (O.value_source _ _ _).trans (programme_value root recognition visit successor transition alignment U7 calculus count actor point word)

theorem original_effect : normal root recognition visit successor transition alignment U7 calculus count actor point word =
    evolution root recognition visit successor actor
      (originalFeature root recognition visit successor actor
        (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point)) -
    originalFeature root recognition visit successor actor
      (actions root recognition visit successor transition alignment U7 calculus count (letter root recognition visit successor actor)
        (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point)) := by
  rw [normal_value,Inventory.normal_value,SourceGeneratedActionWords.run_source]
  exact effect_source root recognition visit successor transition alignment U7 calculus count actor _

theorem cost : (O.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count actor point word)).length = 7 :=
  (O.paid_history _ _ _).trans (programme_cost root recognition visit successor transition alignment U7 calculus count actor)

theorem independent_zero_iff : normal root recognition visit successor transition alignment U7 calculus count actor point word = 0 ↔
    evolution root recognition visit successor actor
      (originalFeature root recognition visit successor actor
        (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point)) =
    originalFeature root recognition visit successor actor
      (actions root recognition visit successor transition alignment U7 calculus count (letter root recognition visit successor actor)
        (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point)) := by
  rw [original_effect]
  exact sub_eq_zero

theorem whole_next (stage : Nat) : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count actor point word) stage) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next _ _ _ stage

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

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
