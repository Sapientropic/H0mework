import H0mework.Fock.PrimeFieldJoint.ClockContinuity
import H0mework.Fock.SourceHistoryClock.PosteriorInstalled

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointClock

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAcquisitionMeasure
open SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint SourceGeneratedJointTime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def RecoveryAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    let bound := inventoryBound runtime
    let depth := SourceGeneratedAcquisitionJoint.depth runtime
    (∀ index : Fin (bound + 1), type_of% (signal_model bound index) ∧
      type_of% (next_clock_actual depth bound index) ∧ type_of% (original_clock_recovery depth bound index) ∧
      type_of% (actual_clock_error depth bound index) ∧
      type_of% (SourcePrimeClockSplitting.chart_restores_model runtimeSeed bound index) ∧
      type_of% (SourcePrimeClockSplitting.native_action_equation (runtimeAt index.val))) ∧
    type_of% (original_time_increment depth bound) ∧ type_of% (original_clock_error_norm depth bound) ∧
    type_of% (original_adjusted_recovery depth bound) ∧
    type_of% (SourceGeneratedRecordFrame.original_temporal_residual_zero depth bound (currentClock depth bound)) ∧
    type_of% (SourceWeightedRecovery.Runtime.Actor.History.Clock.runtime_posterior_factorizes bound 0 (signal bound)) ∧
    (∀ value : FieldSpace depth bound, type_of% (clock_word_transfer depth bound value)) ∧
    (∀ value : NextSpace depth bound, type_of% (clock_word_pullback depth bound value)) ∧
    (∀ sourceWord : Nat →₀ ℤ, type_of% (native_realization round sourceWord) ∧
      type_of% (source_round_after round (SourceClockComplex.ofNative sourceWord)) ∧
      type_of% (SourcePrimeClockSplitting.source_reconstruction sourceWord) ∧
      type_of% (coversAt_factorizes (sourceRound round (SourceClockComplex.ofNative sourceWord)) .particleWave) ∧
      type_of% (coversAt_factorizes (sourceRound round (SourceClockComplex.ofNative sourceWord)).tick.next .particleWave)) ∧
    (∀ left right : Nat →₀ ℤ, type_of% (SourceClockModel.projection_fibre_iff left right)) ∧
    type_of% (scaled_density_clock runtime) ∧ type_of% (actual_scaled_joint_tendsto round) ∧
    (∀ reader : SourceMassCompletion.Joint → ℂ, ∀ continuous : ContinuousAt reader 0,
      type_of% (no_continuous_clock_recovery round reader continuous)) ∧
    type_of% (SourceGeneratedJointTime.sourceGeneratedJointTimeRecovery round) ∧
    type_of% (runtime_eq runtime) ∧ type_of% (coversAt_factorizes runtime .particleWave) ∧
    type_of% (coversAt_factorizes (next runtime) .particleWave)

theorem sourceGeneratedJointClockRecovery (round : Nat) : RecoveryAt round := by
  dsimp only [RecoveryAt]
  exact ⟨(fun index => ⟨signal_model _ index, next_clock_actual _ _ index, original_clock_recovery _ _ index,
      actual_clock_error _ _ index, SourcePrimeClockSplitting.chart_restores_model _ _ index,
      SourcePrimeClockSplitting.native_action_equation _⟩),
    original_time_increment _ _, original_clock_error_norm _ _, original_adjusted_recovery _ _,
    SourceGeneratedRecordFrame.original_temporal_residual_zero _ _ _,
    SourceWeightedRecovery.Runtime.Actor.History.Clock.runtime_posterior_factorizes _ _ _,
    clock_word_transfer _ _, clock_word_pullback _ _,
    (fun sourceWord => ⟨native_realization round sourceWord, source_round_after _ _,
      SourcePrimeClockSplitting.source_reconstruction sourceWord, coversAt_factorizes _ .particleWave,
      coversAt_factorizes _ .particleWave⟩),
    SourceClockModel.projection_fibre_iff, scaled_density_clock _, actual_scaled_joint_tendsto round,
    no_continuous_clock_recovery round, SourceGeneratedJointTime.sourceGeneratedJointTimeRecovery round,
    runtime_eq _, coversAt_factorizes _ .particleWave, coversAt_factorizes _ .particleWave⟩

end
end SourceGeneratedJointClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
