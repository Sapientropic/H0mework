import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory.Consumer
import H0mework.Realization.ObservationActions.WordsCompletionRestriction
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete
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


abbrev Whole := SourceGeneratedActionObservationHistory.completion
  (actions root recognition visit successor transition alignment U7 calculus count (.simultaneous : Letter root recognition visit successor))
  (SourceGeneratedActionWords.inventory (actions root recognition visit successor transition alignment U7 calculus count)
    (read root recognition visit successor transition alignment U7 calculus count))
abbrev sourceMap := SourceGeneratedActionObservationHistory.sourceMap
  (actions root recognition visit successor transition alignment U7 calculus count (.simultaneous : Letter root recognition visit successor))
  (SourceGeneratedActionWords.inventory (actions root recognition visit successor transition alignment U7 calculus count)
    (read root recognition visit successor transition alignment U7 calculus count))
abbrev equivalence := SourceGeneratedActionWords.completionEquiv
  (actions root recognition visit successor transition alignment U7 calculus count)
  (read root recognition visit successor transition alignment U7 calculus count) (.simultaneous : Letter root recognition visit successor)
abbrev completeAdvance := SourceGeneratedActionWords.completeAdvance
  (actions root recognition visit successor transition alignment U7 calculus count)
  (read root recognition visit successor transition alignment U7 calculus count) (.simultaneous : Letter root recognition visit successor)
abbrev completeRead := SourceGeneratedActionWords.completeRead
  (actions root recognition visit successor transition alignment U7 calculus count)
  (read root recognition visit successor transition alignment U7 calculus count) (.simultaneous : Letter root recognition visit successor)
variable (value : Whole root recognition visit successor transition alignment U7 calculus count)
variable (point : Carrier root recognition visit successor)
variable (word : List (Letter root recognition visit successor))
abbrev actedComplete := SourceGeneratedActionWords.run (completeAdvance root recognition visit successor transition alignment U7 calculus count) word value
abbrev model := (equivalence root recognition visit successor transition alignment U7 calculus count).symm value
abbrev actedModel := (equivalence root recognition visit successor transition alignment U7 calculus count).symm
  (actedComplete root recognition visit successor transition alignment U7 calculus count value word)
theorem model_action : actedModel root recognition visit successor transition alignment U7 calculus count value word =
    SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) word
      (model root recognition visit successor transition alignment U7 calculus count value) :=
  SourceGeneratedActionWords.complete_run_model _ _ _ _ _
theorem read_after (following : List (Letter root recognition visit successor)) :
    completeRead root recognition visit successor transition alignment U7 calculus count following
      (actedComplete root recognition visit successor transition alignment U7 calculus count value word) =
      completeRead root recognition visit successor transition alignment U7 calculus count (word++following) value := by
  obtain ⟨point,rfl⟩ := SourceGeneratedActionWords.full_source_surjective
    (actions root recognition visit successor transition alignment U7 calculus count)
    (read root recognition visit successor transition alignment U7 calculus count) (.simultaneous : Letter root recognition visit successor) value
  dsimp only [actedComplete,completeAdvance,completeRead]
  rw [SourceGeneratedActionWords.complete_run_source,SourceGeneratedActionWords.complete_read_source,SourceGeneratedActionWords.complete_read_source,SourceGeneratedActionWords.run_append]
  rfl
theorem complete_fibre (left right : Whole root recognition visit successor transition alignment U7 calculus count) :
    left=right ↔ ∀ following : List (Letter root recognition visit successor),
      completeRead root recognition visit successor transition alignment U7 calculus count following left =
        completeRead root recognition visit successor transition alignment U7 calculus count following right := by
  constructor
  · intro same; subst right; exact fun _ => rfl
  · intro same
    obtain ⟨first,rfl⟩ := SourceGeneratedActionWords.full_source_surjective
      (actions root recognition visit successor transition alignment U7 calculus count)
      (read root recognition visit successor transition alignment U7 calculus count) (.simultaneous : Letter root recognition visit successor) left
    obtain ⟨second,rfl⟩ := SourceGeneratedActionWords.full_source_surjective
      (actions root recognition visit successor transition alignment U7 calculus count)
      (read root recognition visit successor transition alignment U7 calculus count) (.simultaneous : Letter root recognition visit successor) right
    apply congrArg (equivalence root recognition visit successor transition alignment U7 calculus count)
      ((SourceGeneratedActionWords.projection_fibre _ _ _ _ _).mpr (fun following => by
        have equal := same following
        dsimp only [completeRead] at equal
        rw [SourceGeneratedActionWords.complete_read_source,SourceGeneratedActionWords.complete_read_source] at equal
        exact equal))
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
