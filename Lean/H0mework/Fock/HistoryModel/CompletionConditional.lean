import H0mework.Fock.HistoryModel.CompletionSource

/-! The same original source weights condition completed letters and push to actual native next stages. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Complete

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedRuntimeHistoryProbability SourceConditionalHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem conditional_letter (depth : Nat) (letter : Fock.Letter (depth + 1)) (value : Carrier (depth + 1))
    (supported : value ∈ (observed (observed (Fock.sourceLaw depth) (point (depth + 1)))
      (action (depth + 1) letter)).support) :
    ∃ nextSupported : value ∈ (observed ((Fock.sourceLaw depth).map (Fock.step (depth + 1) letter)) (point (depth + 1))).support,
      (Coarsening.mixture (Fock.sourceLaw depth) (point (depth + 1)) (action (depth + 1) letter) value supported).map
        (Fock.step (depth + 1) letter) =
        conditional ((Fock.sourceLaw depth).map (Fock.step (depth + 1) letter)) (point (depth + 1)) value nextSupported :=
  Coarsening.mixture_pushforward (Fock.sourceLaw depth) (point (depth + 1))
    (Fock.step (depth + 1) letter) (point (depth + 1)) (action (depth + 1) letter)
    (fun state => (action_point (depth + 1) letter state).symm) value supported

theorem next_supported (depth : Nat) : nativeNext depth ∈
    (observed (observed (Fock.sourceLaw depth) (point (depth + 1))) (action (depth + 1) (.inl ()))).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨point (depth + 1) ((runtimeAt depth).current.visit.current : Current), ?_, rfl⟩
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨((runtimeAt depth).current.visit.current : Current), Fock.current_supported depth, rfl⟩

def nextMixture (depth : Nat) : PMF Current :=
  Coarsening.mixture (Fock.sourceLaw depth) (point (depth + 1)) (action (depth + 1) (.inl ()))
    (nativeNext depth) (next_supported depth)

theorem native_conditional_push (depth : Nat) :
    let nextLaw := (historyPMF depth).map
      (fun index : Fin (depth + 1) => (((history runtimeSeed depth).stageAt index).next.current.visit.current : Current))
    ∃ supported : nativeNext depth ∈ (observed nextLaw (point (depth + 1))).support,
      (nextMixture depth).map nativeStep = conditional nextLaw (point (depth + 1)) (nativeNext depth) supported := by
  have pushed := conditional_letter depth (.inl ()) (nativeNext depth) (next_supported depth)
  change (∃ supported : nativeNext depth ∈ (observed ((Fock.sourceLaw depth).map nativeStep) (point (depth + 1))).support,
    (nextMixture depth).map nativeStep =
      conditional ((Fock.sourceLaw depth).map nativeStep) (point (depth + 1)) (nativeNext depth) supported) at pushed
  rw [Fock.nativeLaw_next] at pushed
  exact pushed

end
end SourceGeneratedActionWords.Fock.Complete
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
