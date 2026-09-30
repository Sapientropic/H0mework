import H0mework.Fock.PrimeField.RecoveryResidual
import H0mework.Fock.SourceHistory.PrimeFieldRecoveryRegression

/-! The original actor task consumes prime-history recovery, retained residuals and the same source-written next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

theorem last_query_reads_birth (owner : GlobalParentOwner) (bound : Nat) :
    let current : CanonicalUnitArithmeticRoot.Current := (runtimeAt (completionDepth owner bound)).current.visit.current
    observe owner bound (Fin.last bound) (Fin.last (windowBound owner bound)) =
      sourceFieldAt current + SourceFactorizationAction.Fock.birth current := by
  rw [query_value]
  have position : bound + 1 + windowBound owner bound = completionDepth owner bound + 1 := by
    unfold completionDepth
    omega
  change rawField (bound + 1 + windowBound owner bound) = _
  rw [position]
  exact (SourceFactorizationAction.Fock.runtime_source_factorization (completionDepth owner bound)).2.1

theorem information_consumed (bound : Nat) :
    let owner := sourceOwner
    let depth := completionDepth owner bound
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    type_of% (argument_value owner (bound + 1)) ∧
      type_of% (selected_divides owner (bound + 1)) ∧
      type_of% (delay_positive owner (bound + 1)) ∧
      type_of% (sourceMap_injective owner) ∧
      (∀ left right : SourceOperationNative.Carrier process, type_of% (original_model_fibre owner left right)) ∧
      (∀ index actor : Fin (bound + 1), type_of% (coefficient_query owner bound index actor)) ∧
      (∀ index : Fin (bound + 1), type_of% (conditional_is_original owner bound index) ∧
        FiniteRecurrence.Native.conditional (process := process) rawField (windowBound owner bound) runtimeSeed bound index = PMF.pure index) ∧
      (∀ index candidate : Fin (bound + 1), observe owner bound candidate = observe owner bound index →
        HEq ((history runtimeSeed bound).stageAt candidate) ((history runtimeSeed bound).stageAt index)) ∧
      (∀ task : Fin (bound + 1) → ℂ,
        type_of% (raw_error_zero owner bound task) ∧
        (∀ index : Fin (bound + 1), type_of% (complete_transfer owner bound task index)) ∧
        type_of% (residuals_zero owner bound task) ∧ type_of% (original_actor_reconstructed owner bound task)) ∧
      (∀ task : Fin (bound + 1) → ℂ, ∀ decode,
        type_of% (Runtime.Actor.actor_error_decomposition (process := process) rawField runtimeSeed bound task decode)) ∧
      (∀ actor : Fin (bound + 1), ∀ time : Fin (windowBound owner bound + 1),
        type_of% (query_material_factorizes owner bound actor time)) ∧
      (∀ actor : Fin (depth + 1), type_of% (sample_factorizes runtimeSeed depth actor)) ∧
      observe owner bound (Fin.last bound) (Fin.last (windowBound owner bound)) = rawField stage.next.state ∧
      type_of% (last_query_reads_birth owner bound) ∧
      type_of% (SourceOperationNative.Observed.model_factorizes (process := process) rawField runtime) ∧
      (∀ containsGap : 2 ≤ bound, type_of% (no_current_only_clock bound containsGap)) ∧
      type_of% (SourceFactorizationAction.Fock.runtime_source_factorization depth) := by
  exact ⟨argument_value sourceOwner (bound + 1), selected_divides sourceOwner (bound + 1),
    delay_positive sourceOwner (bound + 1), sourceMap_injective sourceOwner, original_model_fibre sourceOwner,
    coefficient_query sourceOwner bound,
    (fun index => ⟨conditional_is_original sourceOwner bound index, conditional_pure sourceOwner bound index⟩),
    posterior_material sourceOwner bound,
    (fun task => ⟨raw_error_zero sourceOwner bound task, complete_transfer sourceOwner bound task,
      residuals_zero sourceOwner bound task, original_actor_reconstructed sourceOwner bound task⟩),
    Runtime.Actor.actor_error_decomposition (process := process) rawField runtimeSeed bound,
    query_material_factorizes sourceOwner bound, sample_factorizes runtimeSeed (completionDepth sourceOwner bound),
    last_query_is_next sourceOwner bound, last_query_reads_birth sourceOwner bound,
    SourceOperationNative.Observed.model_factorizes (process := process) rawField (runtimeAt (completionDepth sourceOwner bound)),
    no_current_only_clock bound,
    SourceFactorizationAction.Fock.runtime_source_factorization (completionDepth sourceOwner bound)⟩

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
