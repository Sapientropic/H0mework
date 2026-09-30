import H0mework.Versions.X.Fock.PrimeField.ClockResidualInformation

/-! Full completion loses a clock fibre; native source fidelity and actual-history recovery remain intact. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockResidual

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

theorem clock_not_projectable : ¬ ∃ decode : SourcePrimeCompletion.Field → ℤ,
    ∀ value : JointField, decode (primeProjection value) = clockRead value := by
  rintro ⟨decode, reads⟩
  have empty := reads 0
  have unit := reads residual
  rw [map_zero, map_zero] at empty
  rw [residual_prime_zero, residual_clock_unit, empty] at unit
  exact zero_ne_one unit

theorem source_projection_faithful (left right : SourceOperationNative.Carrier process) :
    primeProjection (sourceMap nativeAction jointObservation left) =
      primeProjection (sourceMap nativeAction jointObservation right) ↔ left = right := by
  rw [projection_source, projection_source]
  exact (SourcePrimeHistoryRecovery.sourceMap_injective sourceOwner).eq_iff

theorem finite_silence_not_complete_zero (bound : Nat) :
    sourceMap nativeAction observation (word bound) ≠ 0 := by
  intro vanished
  have empty : word bound = 0 := SourcePrimeHistoryRecovery.sourceMap_injective sourceOwner
    (vanished.trans (map_zero (sourceMap nativeAction observation)).symm)
  have unit := clock_unit bound
  rw [empty, map_zero] at unit
  exact zero_ne_one unit

theorem recovered_single_actor (current : LivingRuntimeState process) :
    FiniteRecurrence.Native.conditional (process := process) jointRead 0 current 0 0 = PMF.pure 0 ∧
      type_of% (clock_cost_zero current 0) :=
  ⟨conditional_pure current 0 0, clock_cost_zero current 0⟩

theorem genuine_cost_gain (bound width : Nat) (multiple : 0 < bound) :
    error (historyPMF bound) (SourcePrimeObservationDelay.shortQuery sourceOwner bound width)
      (SourcePrimeObservationDelay.clockTask sourceOwner bound width)
      (fun _ => (((SourcePrimeObservationDelay.firstState sourceOwner (bound + width) : ℝ) + bound / 2 : ℝ) : ℂ)) >
    error (historyPMF bound) (observe (SourcePrimeObservationDelay.startRuntime sourceOwner bound width) bound)
      (SourcePrimeObservationDelay.clockTask sourceOwner bound width) decodeClock := by
  apply sub_pos.mp
  rw [prime_loss_joint_recovery]
  have positive : (0 : ℝ) < bound := by exact_mod_cast multiple
  positivity

end
end SourcePrimeClockResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
