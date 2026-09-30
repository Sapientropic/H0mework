import H0mework.Fock.FiniteObservers.SourceLaws

/-! The same finite-query bridge preserves the original pulse clock cost and both original residuals. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObservation.Pulse

open SourceGeneratedActionObservationHistory SourceWeightedRecovery SourceConditionalTransfer
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert.Controls
open SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

abbrev observe := FiniteRecurrence.Native.query (process := process) pulse 0 runtimeSeed 2

theorem query_zero (index : Fin 3) : observe index = 0 := by
  funext position
  fin_cases position
  change pulse (runtimeAt (index.val + 1)).state = 0
  rw [runtimeAt_state]
  simp [pulse]

theorem field_read_zero : FiniteRecurrence.Native.fieldRead pulse 0 (fieldPoint (process := process) pulse 1) = 0 := by
  have original := FiniteRecurrence.Native.fieldRead_query pulse 0 runtimeSeed 2 (0 : Fin 3)
  rw [Runtime.Actor.Pulse.next_sample] at original
  exact original.trans (query_zero 0)

theorem finite_clock_error (decoder : (Fin 1 → ZMod 2) → ℂ) :
    error (historyPMF 2) observe Runtime.Actor.Pulse.clockTask decoder =
      (2 / 3 : ℝ) + ‖(1 : ℂ) - decoder 0‖ ^ 2 := by
  rw [FiniteRecurrence.Native.finiteError_is_original, Runtime.Actor.Pulse.exact_clock_error]
  rw [field_read_zero]

theorem finite_mean_one :
    FiniteRecurrence.Native.mean pulse 0 runtimeSeed 2 Runtime.Actor.Pulse.clockTask 0 = 1 := by
  have actual := FiniteRecurrence.Native.completeTransfer_finite pulse 0 runtimeSeed 2 (fun _ => 0) pulse_source_law
    Runtime.Actor.Pulse.clockTask (0 : Fin 3)
  rw [Runtime.Actor.Pulse.next_sample, Runtime.Actor.Pulse.next_mean_one] at actual
  have mean := FiniteRecurrence.Native.mean_at_query pulse 0 runtimeSeed 2 Runtime.Actor.Pulse.clockTask (0 : Fin 3)
  change FiniteRecurrence.Native.mean pulse 0 runtimeSeed 2 Runtime.Actor.Pulse.clockTask (observe 0) = _ at mean
  rw [query_zero] at mean
  exact mean.trans actual.symm

theorem finite_mean_attains :
    error (historyPMF 2) observe Runtime.Actor.Pulse.clockTask
      (FiniteRecurrence.Native.mean pulse 0 runtimeSeed 2 Runtime.Actor.Pulse.clockTask) = (2 / 3 : ℝ) := by
  have achieved := FiniteRecurrence.Native.finite_attains pulse 0 runtimeSeed 2 (fun _ => 0) pulse_source_law Runtime.Actor.Pulse.clockTask
  dsimp only at achieved
  rw [Runtime.Actor.Pulse.actor_loss_sixth, Runtime.Actor.Pulse.field_loss_half] at achieved
  exact achieved.trans (by norm_num)

end
end SourceFiniteObservation.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
