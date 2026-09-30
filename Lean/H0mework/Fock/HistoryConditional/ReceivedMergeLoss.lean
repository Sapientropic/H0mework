import H0mework.Fock.HistoryConditional.ReceivedMergeInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse] [Fintype Fine]

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def lostEnergy (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (forget : Fine → Coarse) : ℝ :=
  ∑ key : Fine,
    (SourceFibreExactState.restoreState (inventoryBound runtime) (maximumIndex runtime).val nonunit samples key).1 /
      (inventoryBound runtime + 1 : ℝ) *
    ‖SourceConditionalVector.realizeModel runtime (SourceFibreExactState.model runtime nonunit (samples key)) -
      decoder runtime nonunit samples forget (forget key)‖ ^ 2

theorem lost_energy_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    lostEnergy runtime nonunit samples forget = SourceConditionalMergeLoss.gap runtime read forget := by
  have fine (key : Fine) : SourceConditionalVector.realizeModel runtime
      (SourceFibreExactState.model runtime nonunit (samples key)) = SourceConditionalNativePosterior.decoder runtime read key := by
    rw [SourceFibreExactState.model_source runtime nonunit (samples key) read key (budgets key)]
    rfl
  rw [lostEnergy, SourceFibreExactState.state_source runtime nonunit samples read budgets, SourceConditionalMergeLoss.gap]
  simp_rw [fine, decoder_source runtime nonunit samples read forget _ budgets,
    SourceUniformFibreVariance.source_weight]
  have paid := source_sum read (inventoryBound runtime) (fun key => (inventoryBound runtime + 1 : ℝ)⁻¹ *
    ‖SourceConditionalNativePosterior.decoder runtime read key - SourceConditionalMergeLoss.decoder runtime read forget (forget key)‖ ^ 2)
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using paid

theorem information_zero_iff (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    information forget (inventoryBound runtime)
      (SourceFibreExactState.restoreState (inventoryBound runtime) (maximumIndex runtime).val nonunit samples) = 0 ↔
        lostEnergy runtime nonunit samples forget = 0 := by
  rw [received_information runtime nonunit samples read forget budgets,
    lost_energy_source runtime nonunit samples read forget budgets]
  exact SourceConditionalInformationLoss.amount_zero_iff_gap runtime read forget

theorem loss (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        decoder runtime nonunit samples forget (forget (read actor.val))‖ ^ 2) =
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalVector.realizeModel runtime (SourceFibreExactState.model runtime nonunit (samples (read actor.val)))‖ ^ 2) +
        lostEnergy runtime nonunit samples forget := by
  have fine (key : Fine) : SourceConditionalVector.realizeModel runtime
      (SourceFibreExactState.model runtime nonunit (samples key)) = SourceConditionalNativePosterior.decoder runtime read key := by
    rw [SourceFibreExactState.model_source runtime nonunit (samples key) read key (budgets key)]
    rfl
  simp_rw [fine, decoder_source runtime nonunit samples read forget _ budgets]
  rw [lost_energy_source runtime nonunit samples read forget budgets]
  exact SourceConditionalMergeLoss.loss runtime read forget

end
end SourceReceivedConditionalMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
