import H0mework.Fock.HistoryModel.WordRuntime
import H0mework.Probability.Source.ConditionalCoarseningAction

/-! Original UnitHistory weights condition every generated letter, and the native letter pushes to the owned next stages. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceConditionalHistory

noncomputable section

abbrev sourceLaw (depth : Nat) := SourceOwnedObservationHistory.statePMF nativeStep CanonicalUnitArithmeticRoot.initialCurrent depth

theorem sourceLaw_actual (depth : Nat) : sourceLaw depth = (historyPMF depth).map
    (fun index : Fin (depth + 1) => ((runtimeAt index.val).current.visit.current : Current)) := by
  exact congrArg (fun query : Fin (depth + 1) → Current => (historyPMF depth).map query)
    (funext fun index => (runtime_current_iterate index.val).symm)

theorem nativeLaw_next (depth : Nat) : (sourceLaw depth).map nativeStep = (historyPMF depth).map
    (fun index : Fin (depth + 1) => (((history runtimeSeed depth).stageAt index).next.current.visit.current : Current)) := by
  exact (congrArg (fun law : PMF Current => law.map nativeStep) (sourceLaw_actual depth)).trans
    (PMF.map_comp (fun index : Fin (depth + 1) => ((runtimeAt index.val).current.visit.current : Current))
      (historyPMF depth) nativeStep)

theorem conditional_letter (depth : Nat) (letter : Letter (depth + 1)) (value : WholeModel (depth + 1))
    (supported : value ∈ (observed (observed (sourceLaw depth) (point (depth + 1)))
      (letterAction (depth + 1) letter)).support) :
    ∃ nextSupported : value ∈ (observed ((sourceLaw depth).map (step (depth + 1) letter)) (point (depth + 1))).support,
      (Coarsening.mixture (sourceLaw depth) (point (depth + 1))
        (letterAction (depth + 1) letter) value supported).map (step (depth + 1) letter) =
        conditional ((sourceLaw depth).map (step (depth + 1) letter)) (point (depth + 1)) value nextSupported :=
  Coarsening.mixture_pushforward (sourceLaw depth) (point (depth + 1))
    (step (depth + 1) letter) (point (depth + 1)) (letterAction (depth + 1) letter)
    (fun state => (action_point (depth + 1) letter state).symm) value supported

theorem current_supported (depth : Nat) :
    ((runtimeAt depth).current.visit.current : Current) ∈ (sourceLaw depth).support := by
  rw [sourceLaw_actual]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨Fin.last depth, by simp [historyPMF], rfl⟩

theorem next_supported (depth : Nat) : nextValue depth ∈
    (observed (observed (sourceLaw depth) (point (depth + 1))) (letterAction (depth + 1) (.inl ()))).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨point (depth + 1) ((runtimeAt depth).current.visit.current : Current), ?_, rfl⟩
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨((runtimeAt depth).current.visit.current : Current), current_supported depth, rfl⟩

def nextMixture (depth : Nat) : PMF Current :=
  Coarsening.mixture (sourceLaw depth) (point (depth + 1))
    (letterAction (depth + 1) (.inl ())) (nextValue depth) (next_supported depth)

theorem native_conditional_consumed (depth : Nat) :
    let nextLaw := (historyPMF depth).map
      (fun index : Fin (depth + 1) => (((history runtimeSeed depth).stageAt index).next.current.visit.current : Current))
    (∃ supported : nextValue depth ∈ (observed nextLaw (point (depth + 1))).support,
      (nextMixture depth).map nativeStep = conditional nextLaw (point (depth + 1)) (nextValue depth) supported) ∧
      type_of% (native_word_information depth) := by
  have pushed := conditional_letter depth (.inl ()) (nextValue depth) (next_supported depth)
  change (∃ supported : nextValue depth ∈ (observed ((sourceLaw depth).map nativeStep) (point (depth + 1))).support,
    (nextMixture depth).map nativeStep =
      conditional ((sourceLaw depth).map nativeStep) (point (depth + 1)) (nextValue depth) supported) at pushed
  rw [nativeLaw_next] at pushed
  exact ⟨pushed, native_word_information depth⟩

end
end SourceGeneratedActionWords.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
