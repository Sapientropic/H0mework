import H0mework.Fock.HistoryModel.CompletionConditional

/-! Passing through the complete carrier keeps the original entire source mixture, not just its image. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Complete

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalHistory

noncomputable section

theorem action_original_model (depth : Nat) (letter : Fock.Letter depth) (state : Current) :
    originalModel depth (action depth letter (point depth state)) = Fock.letterAction depth letter (Fock.point depth state) :=
  (congrArg (originalModel depth) (action_point depth letter state)).trans
    ((original_model_point depth (Fock.step depth letter state)).trans (Fock.action_point depth letter state).symm)

theorem next_mixture_original (depth : Nat) : nextMixture depth = Fock.nextMixture depth := by
  obtain ⟨newSupport, newEquation⟩ := Coarsening.mixture_is_conditional (Fock.sourceLaw depth)
    (point (depth + 1)) (action (depth + 1) (.inl ())) (nativeNext depth) (next_supported depth)
  obtain ⟨oldSupport, oldEquation⟩ := Coarsening.mixture_is_conditional (Fock.sourceLaw depth)
    (Fock.point (depth + 1)) (Fock.letterAction (depth + 1) (.inl ())) (Fock.nextValue depth) (Fock.next_supported depth)
  have sameFibre : {state : Current | action (depth + 1) (.inl ()) (point (depth + 1) state) = nativeNext depth} =
      {state : Current | Fock.letterAction (depth + 1) (.inl ()) (Fock.point (depth + 1) state) = Fock.nextValue depth} := by
    ext state
    constructor
    · intro same
      exact (action_original_model (depth + 1) (.inl ()) state).symm.trans
        ((congrArg (originalModel (depth + 1)) same).trans (next_original_model depth))
    · intro same
      apply (completionEquiv (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ())).symm.injective
      exact (action_original_model (depth + 1) (.inl ()) state).trans (same.trans (next_original_model depth).symm)
  change nextMixture depth = _ at newEquation
  change Fock.nextMixture depth = _ at oldEquation
  rw [newEquation, oldEquation]
  unfold conditional
  congr 1

theorem original_mixture_complete_next (depth : Nat) :
    let nextLaw := (SourceGeneratedRuntimeHistoryProbability.historyPMF depth).map
      (fun index : Fin (depth + 1) =>
        (((SourceGeneratedRuntimeHistoryProbability.history
          NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimeSeed depth).stageAt index).next.current.visit.current : Current))
    ∃ supported : nativeNext depth ∈ (observed nextLaw (point (depth + 1))).support,
      (Fock.nextMixture depth).map nativeStep = conditional nextLaw (point (depth + 1)) (nativeNext depth) supported := by
  have generated := native_conditional_push depth
  rw [next_mixture_original] at generated
  exact generated

end
end SourceGeneratedActionWords.Fock.Complete
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
