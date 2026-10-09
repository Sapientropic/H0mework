import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory
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
variable (point : Carrier root recognition visit successor) (word : List (Letter root recognition visit successor))
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history)
end O
abbrev normal := O.value (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count point word)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count point word =
    SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) word
      (projection root recognition visit successor transition alignment U7 calculus count point) :=
  (O.value_source _ _ _).trans (programme_value root recognition visit successor transition alignment U7 calculus count point word)
theorem normal_read (following : List (Letter root recognition visit successor)) :
    readout root recognition visit successor transition alignment U7 calculus count following
      (normal root recognition visit successor transition alignment U7 calculus count point word) =
        read root recognition visit successor transition alignment U7 calculus count
          (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) (word++following) point) := by
  rw [normal_value,SourceGeneratedActionWords.run_source,SourceGeneratedActionWords.readout_source,SourceGeneratedActionWords.run_append]
  rfl

theorem original_model_read :
    originalRestriction root recognition visit successor transition alignment U7 calculus count
      (normal root recognition visit successor transition alignment U7 calculus count point word) =
        SourceGeneratedActionObservationHistory.projection
          (actions root recognition visit successor transition alignment U7 calculus count (.simultaneous : Letter root recognition visit successor))
          (read root recognition visit successor transition alignment U7 calculus count)
          (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point) := by
  rw [normal_value,SourceGeneratedActionWords.run_source]
  exact SourceGeneratedActionWords.originalRestriction_source _ _ _ _

theorem old_model_read :
    oldModelRestriction root recognition visit successor transition alignment U7 calculus count
      (normal root recognition visit successor transition alignment U7 calculus count point word) =
        ActionWords.projection root recognition visit successor transition alignment U7 calculus count
          (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point) := by
  rw [normal_value,SourceGeneratedActionWords.run_source]
  exact old_model_source root recognition visit successor transition alignment U7 calculus count _

theorem normal_source_measurement (following : List (Letter root recognition visit successor))
    (actor : SourceActor root recognition visit) :
    (readout root recognition visit successor transition alignment U7 calculus count following
      (normal root recognition visit successor transition alignment U7 calculus count point word)).2.1 actor =
        actor.val.2.measurement
          (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) (word++following) point).1 :=
  congrArg (fun value => value.2.1 actor)
    (normal_read root recognition visit successor transition alignment U7 calculus count point word following)

theorem normal_target_measurement (following : List (Letter root recognition visit successor))
    (actor : TargetActor root recognition visit successor) :
    (readout root recognition visit successor transition alignment U7 calculus count following
      (normal root recognition visit successor transition alignment U7 calculus count point word)).2.2 actor =
        actor.val.2.measurement
          (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) (word++following) point).2 :=
  congrArg (fun value => value.2.2 actor)
    (normal_read root recognition visit successor transition alignment U7 calculus count point word following)

theorem coarse_model_read :
    coarseRestriction root recognition visit successor transition alignment U7 calculus count
      (normal root recognition visit successor transition alignment U7 calculus count point word) =
        SourceGeneratedActionWords.projection (actions root recognition visit successor transition alignment U7 calculus count)
          (coarseRead root recognition visit successor transition alignment U7 calculus count) (.simultaneous : Letter root recognition visit successor)
          (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point) := by
  rw [normal_value,SourceGeneratedActionWords.run_source]
  exact coarse_source root recognition visit successor transition alignment U7 calculus count _

theorem cost : (O.trace (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point word)).length = word.length+2 :=
  (O.paid_history _ _ _).trans (programme_budget root recognition visit successor transition alignment U7 calculus count word)

namespace C
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (activated_query activated_answer activated_next)
end C
theorem query_answer_next (offset : Nat) :
    type_of% (C.activated_query (sourceRoot root recognition visit successor transition alignment U7 calculus count point word) visit U7 calculus
      (reader root recognition visit successor transition alignment U7 calculus count point word) offset) ∧
    type_of% (C.activated_answer (sourceRoot root recognition visit successor transition alignment U7 calculus count point word) visit U7 calculus
      (reader root recognition visit successor transition alignment U7 calculus count point word) offset) ∧
    type_of% (C.activated_next (sourceRoot root recognition visit successor transition alignment U7 calculus count point word) visit U7 calculus
      (reader root recognition visit successor transition alignment U7 calculus count point word) offset) :=
  ⟨C.activated_query _ _ _ _ _ offset,C.activated_answer _ _ _ _ _ offset,C.activated_next _ _ _ _ _ offset⟩
theorem whole_next (stage : Nat) : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point word) stage) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next _ _ _ stage

theorem source_seed : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Relations.boundary_in_inventory
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point word) (paid root recognition visit successor transition alignment U7 calculus count point word)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Relations.boundary_in_inventory _ _ _ _
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
