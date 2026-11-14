import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Dependent.FinitePrefixRecovery
import H0mework.Versions.Rf94092ef.Probability.Empirical.ObservedAtomic
import H0mework.Versions.Rf94092ef.Fock.SourceHistory.ConditionalObserved
import H0mework.Versions.Rf94092ef.Fock.SourceHistory.ConditionalRecoveryRegression

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Dependent.Pulse

open Filter SourceGeneratedEmpiricalHilbert SourceGeneratedEmpiricalHilbert.Controls
open SourceConditionalTransfer SourceConditionalTransfer.Pulse
open SourceGeneratedScalarDifferentialResidual
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace Topology

private def clock (r : LivingRuntimeState process) : LivingRuntimeState process := r.tick.next

local notation "Clock" => clock
local notation "Action" => fun r : LivingRuntimeState process => transfer pulse r 1
local notation "Question" => SourceGeneratedAtomicObservation.Runtime.cotestAt pulse 1 (0 : Fin 2)
local notation "Read" => fun r : LivingRuntimeState process => innerSL ℂ (Question r)
local notation "Eval" => stageEvaluator Clock Action Read
local notation "Model" => Runtime.source (process := process) pulse 1 Question
local notation "after" => runtime.tick.next

/-- The existing atomic query after the actual tick is approximated from the finite successor readings. -/
def finiteNext (n : Nat) : Space pulse after 1 :=
  PrefixRecovery.approximate (Eval after) (fun j : Fin n => Eval runtime (j.val+1) indicatorValue)

theorem finite_prefix_actual_next :
    Tendsto finiteNext atTop (𝓝 (Runtime.realizationAt (process := process) pulse 1 Question after
      (Runtime.next (process := process) pulse 1 Question runtime (canonicalResidual (Model runtime) indicatorValue)))) :=
  finite_prefix_next Clock Action Read runtime indicatorValue

theorem finite_prefix_atomic_half :
    Tendsto (fun n => Read after (finiteNext n)) atTop (𝓝 (1/2 : ℂ)) := by
  have approximation := finite_prefix_next_read Clock Action Read runtime indicatorValue
  have queryPrice := SourceGeneratedAtomicObservation.Runtime.next_conditional pulse 1 (0 : Fin 2) runtime indicatorValue
  have evaluation := Runtime.next_read (process := process) pulse 1 Question runtime indicatorValue
  have price := evaluation.symm.trans queryPrice
  change Read after (Action runtime indicatorValue) =
    conditionalValue pulse runtime 1 indicatorValue query next_query_supported at price
  have paid := price.trans conditionalValue_half
  change Tendsto (fun n => Read after (finiteNext n)) atTop
    (𝓝 (Read after (Action runtime indicatorValue))) at approximation
  rwa [paid] at approximation

private theorem keep_time_floor {bill time observation fit : ℝ}
    (total : bill = time+observation^2+fit^2) (paid : time = (1/4 : ℝ)) : (1/4 : ℝ) ≤ bill := by
  rw [total, paid]
  exact (le_add_of_nonneg_right (sq_nonneg observation)).trans (le_add_of_nonneg_right (sq_nonneg fit))

/-- Each finite decoder retains the original temporal loss of the actual pulse. -/
theorem finite_prefix_time_loss (n : Nat) :
    (1/4 : ℝ) ≤ ‖indicatorValue - Runtime.recoveredPullback (process := process) pulse 1 Question runtime
      (canonicalResidual (Model after) (finiteNext n))‖^2 := by
  let decoded := canonicalResidual (Model after) (finiteNext n)
  have bill := Runtime.decoder_error (process := process) pulse 1 Question runtime indicatorValue decoded
  change _ ≤ ‖indicatorValue - Runtime.recoveredPullback (process := process) pulse 1 Question runtime decoded‖^2
  exact keep_time_floor bill SourceConditionalRecovery.Pulse.residual_energy

theorem finite_prefix_original_receipt (n : Nat) :
    type_of% (Installed.runtime_observation_consumed pulse 1 Question indicatorValue
      (canonicalResidual (Model after) (finiteNext n))) :=
  Installed.runtime_observation_consumed pulse 1 Question indicatorValue
    (canonicalResidual (Model after) (finiteNext n))

end SourceGeneratedActionObservationHistory.Dependent.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
