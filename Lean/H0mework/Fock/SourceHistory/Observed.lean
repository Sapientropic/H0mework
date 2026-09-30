import H0mework.Probability.Empirical.ObservedRecovery
import H0mework.Fock.SourceHistory.ConditionalRecoveryRegression

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Dependent.Pulse

open SourceGeneratedEmpiricalHilbert SourceGeneratedEmpiricalHilbert.Controls
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarDifferentialResidual SourceConditionalTransfer SourceConditionalTransfer.Pulse
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance pulseFieldMeasurable : MeasurableSpace (Field pulse) := fieldBorel pulse

def unitQuestion (current : LivingRuntimeState process) : Space pulse current 1 :=
  (memLp_const (1 : ℂ) : MemLp (fun _ : Field pulse => (1 : ℂ)) 2
    (empirical pulse current 1).toMeasure).toLp (fun _ => 1)

theorem unitQuestion_sample (current : LivingRuntimeState process) (index : Fin 2) :
    unitQuestion current (fieldSample pulse current 1 index) = 1 :=
  SourceConditionalTransfer.ae_at_sample pulse current 1 index (memLp_const (1 : ℂ)).coeFn_toLp

theorem unit_next_read :
    Runtime.reader (process := process) pulse 1 unitQuestion runtime.tick.next
        (Runtime.next (process := process) pulse 1 unitQuestion runtime
          (canonicalResidual (Runtime.source (process := process) pulse 1 unitQuestion runtime) indicatorValue)) =
      (1 / 2 : ℂ) := by
  rw [Runtime.next_read, inner_source_sum]
  have each (index : Fin 2) :
      ⟪unitQuestion runtime.tick.next (fieldSample pulse runtime.tick.next 1 index),
        transfer pulse runtime 1 indicatorValue (fieldSample pulse runtime.tick.next 1 index)⟫_ℂ =
          (1 / 2 : ℂ) := by
    have same : nextAtom pulse runtime 1 index = query := nextObservation_constant index
    rw [unitQuestion_sample, ← nextAtom_eq_next_sample, same, transfer_half]
    norm_num
  simp_rw [each]
  norm_num [Fin.sum_univ_two, historyPMF_apply]

theorem unit_next_ne_zero :
    Runtime.next (process := process) pulse 1 unitQuestion runtime
      (canonicalResidual (Runtime.source (process := process) pulse 1 unitQuestion runtime) indicatorValue) ≠ 0 := by
  intro vanished
  have killed := congrArg (Runtime.reader (process := process) pulse 1 unitQuestion runtime.tick.next) vanished
  have halfZero : (1 / 2 : ℂ) = 0 := unit_next_read.symm.trans
    (killed.trans (map_zero (Runtime.reader (process := process) pulse 1 unitQuestion runtime.tick.next)))
  norm_num at halfZero

variable (cotest : ∀ current : LivingRuntimeState process, Space pulse current 1)

local instance pulseClosed (current : LivingRuntimeState process) :
    IsClosed (LinearMap.ker (Runtime.source (process := process) pulse 1 cotest current) : Set (Space pulse current 1)) :=
  kernel_closed (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer pulse r 1) (fun r => innerSL ℂ (cotest r)) current

local instance pulseComplete (current : LivingRuntimeState process) :
    CompleteSpace (LinearMap.ker (Runtime.source (process := process) pulse 1 cotest current)) :=
  (pulseClosed cotest current).isComplete.completeSpace_coe

theorem every_future_decoder_pays_original_residual
    (decoder : ResidualCarrier (Runtime.source (process := process) pulse 1 cotest runtime.tick.next)) :
    (1 / 4 : ℝ) ≤ ‖indicatorValue - Runtime.recoveredPullback (process := process) pulse 1 cotest runtime decoder‖ ^ 2 := by
  let timeLoss := ‖residual pulse runtime 1 indicatorValue‖ ^ 2
  let questionLoss := ‖IsometricRetainedTransfer.residual
    (Runtime.realizationAt (process := process) pulse 1 cotest runtime.tick.next)
    (transfer pulse runtime 1 indicatorValue)‖ ^ 2
  let decoderLoss := ‖Runtime.next (process := process) pulse 1 cotest runtime
    (canonicalResidual (Runtime.source (process := process) pulse 1 cotest runtime) indicatorValue) - decoder‖ ^ 2
  have error : ‖indicatorValue - Runtime.recoveredPullback (process := process) pulse 1 cotest runtime decoder‖ ^ 2 =
      timeLoss + questionLoss + decoderLoss :=
    Runtime.decoder_error (process := process) pulse 1 cotest runtime indicatorValue decoder
  have paid : timeLoss = (1 / 4 : ℝ) := SourceConditionalRecovery.Pulse.residual_energy
  have questionNonnegative : 0 ≤ questionLoss := sq_nonneg _
  have decoderNonnegative : 0 ≤ decoderLoss := sq_nonneg _
  exact paid.symm.trans_le (((le_add_of_nonneg_right questionNonnegative).trans
    (le_add_of_nonneg_right decoderNonnegative)).trans_eq error.symm)

theorem retained_source_recovered :
    Runtime.recoveredPullback (process := process) pulse 1 cotest runtime
        (Runtime.next (process := process) pulse 1 cotest runtime
          (canonicalResidual (Runtime.source (process := process) pulse 1 cotest runtime) indicatorValue)) +
      (residual pulse runtime 1 indicatorValue + pullback pulse runtime 1
        (IsometricRetainedTransfer.residual (Runtime.realizationAt (process := process) pulse 1 cotest runtime.tick.next)
          (transfer pulse runtime 1 indicatorValue))) = indicatorValue :=
  Runtime.complete_reconstruction (process := process) pulse 1 cotest runtime indicatorValue

end
end SourceGeneratedActionObservationHistory.Dependent.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
