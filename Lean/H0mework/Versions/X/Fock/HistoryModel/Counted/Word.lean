import H0mework.Versions.X.Fock.SourceHistory.CountedMerge.Information
import H0mework.Versions.X.Fock.HistoryModel.ConditionalWords
import H0mework.Versions.X.Fock.HistoryModel.DynamicHilbertSeparation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedWordTransport

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

theorem native_actor_square (depth : Nat) (actor : Fin (depth + 1)) :
    SourceGeneratedActionWords.Fock.letterAction (depth + 1) (.inl ())
      (SourceGeneratedActionWords.Fock.point (depth + 1)
        ((runtimeAt actor.val).current.visit.current : Current)) =
      SourceGeneratedActionWords.Fock.point (depth + 1)
        ((((history runtimeSeed depth).stageAt actor).next).current.visit.current : Current) := by
  let source : Current := (runtimeAt actor.val).current.visit.current
  let target : Current := ((history runtimeSeed depth).stageAt actor).next.current.visit.current
  have actual : SourceGeneratedActionWords.Fock.step (depth + 1) (.inl ()) source = target := by
    change nativeStep source = target
    rfl
  exact (SourceGeneratedActionWords.Fock.action_point (depth + 1) (.inl ()) source).trans
    (congrArg (SourceGeneratedActionWords.Fock.point (depth + 1)) actual)

theorem native_word_law (depth : Nat) :
    ((SourceGeneratedActionWords.Fock.sourceLaw depth).map nativeStep).map
      (SourceGeneratedActionWords.Fock.point (depth + 1)) =
    (historyPMF depth).map (fun actor : Fin (depth + 1) =>
      SourceGeneratedActionWords.Fock.letterAction (depth + 1) (.inl ())
        (SourceGeneratedActionWords.Fock.point (depth + 1)
          ((runtimeAt actor.val).current.visit.current : Current))) := by
  let nextState : Fin (depth + 1) → Current := fun actor =>
    ((history runtimeSeed depth).stageAt actor).next.current.visit.current
  have law := congrArg (fun p : PMF Current => p.map (SourceGeneratedActionWords.Fock.point (depth + 1)))
    (SourceGeneratedActionWords.Fock.nativeLaw_next depth)
  have composed := PMF.map_comp nextState (historyPMF depth)
    (SourceGeneratedActionWords.Fock.point (depth + 1))
  have same : (fun actor : Fin (depth + 1) =>
      SourceGeneratedActionWords.Fock.point (depth + 1) (nextState actor)) =
      (fun actor : Fin (depth + 1) =>
        SourceGeneratedActionWords.Fock.letterAction (depth + 1) (.inl ())
          (SourceGeneratedActionWords.Fock.point (depth + 1)
            ((runtimeAt actor.val).current.visit.current : Current))) := by
    funext actor
    exact (native_actor_square depth actor).symm
  exact law.trans (composed.trans (congrArg (fun read : Fin (depth + 1) →
    SourceGeneratedActionWords.Fock.WholeModel (depth + 1) => (historyPMF depth).map read) same))

private theorem word_point_runtime_injective (depth : Nat) : Function.Injective
    (fun state : Nat => SourceGeneratedActionWords.Fock.point depth
      ((runtimeAt state).current.visit.current : Current)) := by
  intro left right same
  have mapped := congrArg
    (SourceGeneratedActionWords.completionEquiv
      (SourceGeneratedActionWords.Fock.actions depth)
      (SourceGeneratedActionWords.Fock.observer depth) (.inl ())) same
  have complete : SourceGeneratedActionWords.Fock.Complete.point depth
      ((runtimeAt left).current.visit.current : Current) =
      SourceGeneratedActionWords.Fock.Complete.point depth
        ((runtimeAt right).current.visit.current : Current) := by
    simpa only [SourceGeneratedActionWords.Fock.point, SourceGeneratedActionWords.Fock.Complete.point,
      SourceGeneratedActionWords.completion_equiv_source] using mapped
  exact SourceGeneratedActionWords.Fock.Dynamic.Hilbert.point_runtime_injective depth complete

theorem native_actor_g_factors (runtime : LivingRuntimeState process)
    (left right : Actors runtime)
    (same : SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1) (.inl ())
      (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
        ((runtimeAt left.val).current.visit.current : Current)) =
      SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1) (.inl ())
        (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
          ((runtimeAt right.val).current.visit.current : Current))) :
    nextRead runtime left = nextRead runtime right := by
  let depth := inventoryBound runtime
  have sameNext : SourceGeneratedActionWords.Fock.point (depth + 1)
      (((history runtimeSeed depth).stageAt left).next.current.visit.current : Current) =
      SourceGeneratedActionWords.Fock.point (depth + 1)
        (((history runtimeSeed depth).stageAt right).next.current.visit.current : Current) :=
    (native_actor_square depth left).symm.trans (same.trans (native_actor_square depth right))
  have runtimePoint (actor : Actors runtime) :
      SourceGeneratedActionWords.Fock.point (depth + 1)
        (((history runtimeSeed depth).stageAt actor).next.current.visit.current : Current) =
      SourceGeneratedActionWords.Fock.point (depth + 1)
        ((runtimeAt (actor.val + 1)).current.visit.current : Current) := rfl
  rw [runtimePoint left, runtimePoint right] at sameNext
  have indices := word_point_runtime_injective (depth + 1) sameNext
  have equal : left = right := Fin.ext (by omega)
  rw [equal]

theorem native_word_actor_posterior (runtime : LivingRuntimeState process)
    (actor : Actors runtime) :
    let read : Actors runtime → SourceGeneratedActionWords.Fock.WholeModel (inventoryBound runtime + 1) :=
      fun index => SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1) (.inl ())
        (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
          ((runtimeAt index.val).current.visit.current : Current))
    SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) read (read actor)
      (SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) read actor
        (SourceConditionalModel.positive runtime actor)) = PMF.pure actor := by
  dsimp only
  let read : Actors runtime → SourceGeneratedActionWords.Fock.WholeModel (inventoryBound runtime + 1) :=
    fun index => SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1) (.inl ())
      (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
        ((runtimeAt index.val).current.visit.current : Current))
  have faithful : Function.Injective read := by
    intro left right same
    exact SourceActualImageStep.nextRead_injective runtime (native_actor_g_factors runtime left right same)
  exact SourceWeightedRecovery.ObservationRefinement.conditional_injective
    (historyPMF (inventoryBound runtime)) read faithful actor (SourceConditionalModel.positive runtime actor)

theorem native_word_g_recovers (runtime : LivingRuntimeState process)
    (actor : Actors runtime) :
    let read : Actors runtime → SourceGeneratedActionWords.Fock.WholeModel (inventoryBound runtime + 1) :=
      fun index => SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1) (.inl ())
        (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
          ((runtimeAt index.val).current.visit.current : Current))
    (∑ candidate : Actors runtime,
      (((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) read (read actor)
        (SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) read actor
          (SourceConditionalModel.positive runtime actor))) candidate).toReal : ℂ) •
        nextRead runtime candidate) = nextRead runtime actor := by
  dsimp only
  rw [native_word_actor_posterior runtime actor]
  rw [Finset.sum_eq_single actor]
  · simp
  · intro candidate _ different
    rw [PMF.pure_apply, if_neg different]
    simp
  · intro missing
    exact (missing (Finset.mem_univ actor)).elim

theorem native_word_mass (runtime : LivingRuntimeState process) (actor : Actors runtime) :
    (((SourceGeneratedActionWords.Fock.sourceLaw (inventoryBound runtime)).map nativeStep).map
      (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)))
        (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1) (.inl ())
          (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
            ((runtimeAt actor.val).current.visit.current : Current))) =
      historyPMF (inventoryBound runtime) actor := by
  let read : Actors runtime → SourceGeneratedActionWords.Fock.WholeModel (inventoryBound runtime + 1) :=
    fun index => SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1) (.inl ())
      (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
        ((runtimeAt index.val).current.visit.current : Current))
  have faithful : Function.Injective read := by
    intro left right same
    exact SourceActualImageStep.nextRead_injective runtime (native_actor_g_factors runtime left right same)
  rw [native_word_law]
  rw [PMF.map_apply, tsum_eq_single actor]
  · exact if_pos rfl
  · intro candidate different
    exact if_neg (fun same => different (faithful same).symm)

theorem native_word_next_mixture_pure (depth : Nat) :
    (SourceGeneratedActionWords.Fock.nextMixture depth).map nativeStep =
      PMF.pure (((history runtimeSeed depth).stageAt (Fin.last depth)).next.current.visit.current : Current) := by
  let nextState : Fin (depth + 1) → Current := fun actor =>
    ((history runtimeSeed depth).stageAt actor).next.current.visit.current
  let read : Fin (depth + 1) → SourceGeneratedActionWords.Fock.WholeModel (depth + 1) :=
    fun actor => SourceGeneratedActionWords.Fock.letterAction (depth + 1) (.inl ())
      (SourceGeneratedActionWords.Fock.point (depth + 1)
        ((runtimeAt actor.val).current.visit.current : Current))
  let newest := Fin.last depth
  have square (actor : Fin (depth + 1)) :
      SourceGeneratedActionWords.Fock.point (depth + 1) (nextState actor) = read actor :=
    (native_actor_square depth actor).symm
  have supported : read newest ∈
      (SourceConditionalHistory.observed (historyPMF depth) read).support :=
    SourceWeightedRecovery.observed_supported (historyPMF depth) read newest (by simp [historyPMF])
  obtain ⟨nextSupported, pushed⟩ := SourceConditionalHistory.conditional_pushforward
    (historyPMF depth) read nextState (SourceGeneratedActionWords.Fock.point (depth + 1)) id
    square Function.injective_id (read newest) supported
  have faithful : Function.Injective read := by
    intro left right same
    have nextEqual : SourceGeneratedActionWords.Fock.point (depth + 1) (nextState left) =
        SourceGeneratedActionWords.Fock.point (depth + 1) (nextState right) :=
      (square left).trans (same.trans (square right).symm)
    have runtimePoint (actor : Fin (depth + 1)) :
        SourceGeneratedActionWords.Fock.point (depth + 1) (nextState actor) =
        SourceGeneratedActionWords.Fock.point (depth + 1)
          ((runtimeAt (actor.val + 1)).current.visit.current : Current) := rfl
    rw [runtimePoint left, runtimePoint right] at nextEqual
    have indices := word_point_runtime_injective (depth + 1) nextEqual
    exact Fin.ext (by omega)
  have posterior : SourceConditionalHistory.conditional (historyPMF depth) read (read newest) supported =
      PMF.pure newest :=
    SourceWeightedRecovery.ObservationRefinement.conditional_injective
      (historyPMF depth) read faithful newest (by simp [historyPMF])
  have target : read newest = SourceGeneratedActionWords.Fock.nextValue depth := by
    rw [← square]
    exact (SourceGeneratedActionWords.Fock.nextValue_is_source depth).symm
  rcases (SourceGeneratedActionWords.Fock.native_conditional_consumed depth).1 with ⟨wordSupported, consumed⟩
  rw [posterior, PMF.pure_map] at pushed
  simp only [target, id_eq] at pushed
  exact consumed.trans pushed.symm

end
end SourceCountedWordTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
