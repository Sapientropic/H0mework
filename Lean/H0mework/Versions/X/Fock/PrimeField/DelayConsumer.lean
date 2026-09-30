import H0mework.Versions.X.Fock.SourceHistory.PrimeObservationDelayRegression

/-! The original clock and ledger consume the full posterior, exact finite-query loss and continuing source update. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeObservationDelay

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open SourcePrimeHistoryRecovery
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

theorem original_decoder_loss (owner : GlobalParentOwner) (bound width : Nat)
    (decode : (Fin (width + 1) → IntegralOneParticle) → ℂ) :
    let runtime := startRuntime owner bound width
    let task := clockTask owner bound width
    SourceConditionalRecovery.decoderError (process := process) rawField runtime bound
      (SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField runtime bound
        (Runtime.Actor.actorTransfer (process := process) rawField runtime bound (taskValue (historyPMF bound) task)))
      (fun field => decode (FiniteRecurrence.Native.fieldRead (process := process) rawField width field)) =
      (bound : ℝ) * (bound + 2) / 12 +
        ‖(((firstState owner (bound + width) : ℝ) + bound / 2 : ℝ) : ℂ) - decode (atom owner bound width)‖ ^ 2 := by
  have retained := Runtime.Actor.actor_error_decomposition (process := process) rawField (startRuntime owner bound width) bound
    (clockTask owner bound width) (fun field => decode (FiniteRecurrence.Native.fieldRead (process := process) rawField width field))
  dsimp only at retained
  rw [(residuals_zero owner (startRuntime owner bound width) bound (clockTask owner bound width)).1,
    (residuals_zero owner (startRuntime owner bound width) bound (clockTask owner bound width)).2] at retained
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at retained
  exact retained.symm.trans (original_clock_error owner bound width decode)

theorem information_consumed (bound width : Nat) :
    let owner := sourceOwner
    let length := bound + width
    let depth := completionDepth owner bound width
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    type_of% (magnitude_value owner length) ∧
      (∀ offset, ∀ inside : offset ≤ length, type_of% (source_birth_zero owner length offset inside)) ∧
      (∀ offset, type_of% (source_multiplicity_increases owner length offset)) ∧
      (∀ actor : Fin (bound + 1), type_of% (posterior_is_full owner bound width actor)) ∧
      (∀ decode : (Fin (width + 1) → IntegralOneParticle) → ℂ,
        type_of% (original_clock_error owner bound width decode) ∧ type_of% (original_decoder_loss owner bound width decode)) ∧
      type_of% (minimum_clock_cost owner bound width) ∧
      type_of% (residuals_zero owner (startRuntime owner bound width) bound (clockTask owner bound width)) ∧
      type_of% (no_fixed_window_model width) ∧
      (∀ actor : Fin (bound + 1), type_of% (sample_factorizes (startRuntime owner bound width) bound actor)) ∧
      (∀ actor : Fin (bound + 1), ∀ time : Fin (width + 1), type_of% (query_material owner bound width actor time)) ∧
      (∀ actor : Fin (depth + 1), type_of% (sample_factorizes runtimeSeed depth actor)) ∧
      shortQuery owner bound width (Fin.last bound) (Fin.last width) = rawField stage.next.state ∧
      SourceFactorizationAction.Fock.birth (current owner length length) = 0 ∧
      type_of% (SourceOperationNative.Observed.model_factorizes (process := process) rawField runtime) ∧
      type_of% (SourceFactorizationAction.Fock.runtime_source_factorization depth) := by
  exact ⟨magnitude_value sourceOwner (bound + width),
    source_birth_zero sourceOwner (bound + width),
    source_multiplicity_increases sourceOwner (bound + width), posterior_is_full sourceOwner bound width,
    (fun decode => ⟨original_clock_error sourceOwner bound width decode, original_decoder_loss sourceOwner bound width decode⟩),
    minimum_clock_cost sourceOwner bound width, residuals_zero sourceOwner (startRuntime sourceOwner bound width) bound (clockTask sourceOwner bound width),
    no_fixed_window_model width, sample_factorizes (startRuntime sourceOwner bound width) bound,
    query_material sourceOwner bound width, sample_factorizes runtimeSeed (completionDepth sourceOwner bound width),
    (query_material sourceOwner bound width (Fin.last bound) (Fin.last width)).1,
    source_birth_zero sourceOwner (bound + width) (bound + width) (by rfl),
    SourceOperationNative.Observed.model_factorizes (process := process) rawField (runtimeAt (completionDepth sourceOwner bound width)),
    SourceFactorizationAction.Fock.runtime_source_factorization (completionDepth sourceOwner bound width)⟩

end
end SourcePrimeObservationDelay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
