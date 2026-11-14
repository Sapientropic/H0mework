import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Conditional.Coarsening.Loss
import H0mework.Probability.EmpiricalRecovery.ActorConditional

/-! The original field's two source-generated pulse atoms receive the same exact clock costs. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePulseCoarsening

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert.Controls
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceConditionalTransfer
open SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical

noncomputable section

theorem field_sample (bound : Nat) (point : Fin (bound + 1)) :
    fieldSample pulse runtimeSeed bound point =
      if point.val = 0 then fieldPoint (process := process) pulse 0 else fieldPoint pulse 1 := by
  change fieldPoint pulse (runtimeAt point.val).state = _
  rw [runtimeAt_state]
  cases seen : point.val with
  | zero => rfl
  | succ value => exact point_successors_equal value 0

theorem next_field_sample (bound : Nat) (point : Fin (bound + 1)) :
    nextAtom pulse runtimeSeed bound point = fieldPoint (process := process) pulse 1 := by
  rw [nextAtom, fieldSample, fieldPoint_action]
  change fieldPoint pulse ((runtimeAt point.val).state + 1) = _
  rw [runtimeAt_state]
  exact point_successors_equal point.val 0

theorem current_field_error (bound : Nat) (decoder : Field (process := process) pulse → ℂ) :
    error (historyPMF bound) (fieldSample pulse runtimeSeed bound) (clockTask bound) decoder =
      (bound : ℝ) * (bound - 1) / 12 +
      ‖decoder (fieldPoint pulse 0)‖ ^ 2 / (bound + 1 : ℝ) +
      (bound : ℝ) / (bound + 1 : ℝ) *
        ‖(((bound + 1 : ℝ) / 2 : ℝ) : ℂ) - decoder (fieldPoint pulse 1)‖ ^ 2 := by
  let raw : ZMod 2 → ℂ := fun value => if value = 1 then decoder (fieldPoint pulse 0) else decoder (fieldPoint pulse 1)
  have response : ∀ point : Fin (bound + 1), raw (observe bound point) =
      decoder (fieldSample pulse runtimeSeed bound point) := by
    intro point
    rw [observe_actual, field_sample]
    by_cases first : point.val = 0 <;> simp [raw, first]
  have readback : error (historyPMF bound) (observe bound) (clockTask bound) raw =
      error (historyPMF bound) (fieldSample pulse runtimeSeed bound) (clockTask bound) decoder := by
    simp only [error, response]
  simpa only [raw, if_pos rfl, if_neg (zero_ne_one : (0 : ZMod 2) ≠ 1)] using
    readback.symm.trans (current_clock_error bound raw)

theorem next_field_error (bound : Nat) (decoder : Field (process := process) pulse → ℂ) :
    Runtime.Actor.rawError pulse runtimeSeed bound (clockTask bound) decoder =
      (bound : ℝ) * (bound + 2) / 12 +
        ‖(((bound : ℝ) / 2 : ℝ) : ℂ) - decoder (fieldPoint pulse 1)‖ ^ 2 := by
  simpa only [Runtime.Actor.rawError, error, clock_actual, next_field_sample, mul_one, one_mul,
    zero_add, one_pow, Complex.ofReal_natCast] using
    ObservationRefinement.uniform_clock_error bound 0 1 (decoder (fieldPoint (process := process) pulse 1))

def currentFieldDecoder (bound : Nat) (atom : Field (process := process) pulse) : ℂ :=
  if atom = fieldPoint pulse 0 then 0 else (((bound + 1 : ℝ) / 2 : ℝ) : ℂ)

theorem field_decoder_attains (bound : Nat) :
    error (historyPMF bound) (fieldSample pulse runtimeSeed bound) (clockTask bound) (currentFieldDecoder bound) =
      (bound : ℝ) * (bound - 1) / 12 := by
  rw [current_field_error]
  simp [currentFieldDecoder, point_zero_ne_one.symm]

theorem current_field_lower_bound (bound : Nat) (decoder : Field (process := process) pulse → ℂ) :
    (bound : ℝ) * (bound - 1) / 12 ≤
      error (historyPMF bound) (fieldSample pulse runtimeSeed bound) (clockTask bound) decoder := by
  rw [current_field_error]
  exact (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (by positivity))

end
end SourcePulseCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
