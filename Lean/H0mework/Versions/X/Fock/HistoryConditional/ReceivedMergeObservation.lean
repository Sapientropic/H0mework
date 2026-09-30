import H0mework.Versions.X.Fock.HistoryConditional.ReceivedMergeNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse] [Fintype Fine]

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors nextRead positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def noiseEnergy (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) : ℝ :=
  ∑ key : Fine,
    (SourceFibreExactState.restoreState (inventoryBound runtime) (maximumIndex runtime).val nonunit samples key).1 /
      (inventoryBound runtime + 1 : ℝ) * ‖SourceFibreExactState.residual runtime nonunit (samples key)‖ ^ 2

theorem noise_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    noiseEnergy runtime nonunit samples =
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceFibreExactState.residual runtime nonunit (samples (read actor.val))‖ ^ 2 := by
  rw [noiseEnergy, SourceFibreExactState.state_source runtime nonunit samples read budgets]
  simp_rw [SourceUniformFibreVariance.source_weight]
  have paid := source_sum read (inventoryBound runtime) (fun key => (inventoryBound runtime + 1 : ℝ)⁻¹ *
    ‖SourceFibreExactState.residual runtime nonunit (samples key)‖ ^ 2)
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using paid

theorem observation_balance (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        decoder runtime nonunit samples forget (forget (read actor.val))‖ ^ 2) + noiseEnergy runtime nonunit samples =
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalVector.realizeModel runtime (SourceFibreExactState.observed runtime nonunit (samples (read actor.val)))‖ ^ 2) +
        lostEnergy runtime nonunit samples forget := by
  let source := historyPMF (inventoryBound runtime)
  let query : Actors runtime → Fine := fun actor => read actor.val
  let values : Actors runtime → SourceJointClockGraph.Carrier :=
    fun actor => SourceConditionalVector.realizeModel runtime (nextRead runtime actor)
  have means (actor : Actors runtime) :
      SourceVectorMoment.mean (SourceConditionalHistory.conditional source query (query actor)
        (SourceWeightedRecovery.observed_supported source query actor (positive runtime actor))) values =
          SourceConditionalNativePosterior.decoder runtime read (query actor) :=
    (SourceConditionalNativePosterior.decoder_mean runtime read (read actor.val)
      (SourceWeightedRecovery.observed_supported source query actor (positive runtime actor))).symm
  have fine := SourceVectorMoment.conditional_error source query (positive runtime) values
    (SourceConditionalNativePosterior.decoder runtime read)
  simp only [means, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, add_zero] at fine
  have observed := SourceVectorMoment.conditional_error source query (positive runtime) values
    (fun key => SourceConditionalVector.realizeModel runtime (SourceFibreExactState.observed runtime nonunit (samples key)))
  rw [← fine] at observed
  simp only [means] at observed
  dsimp only [source, query, values] at observed
  have error (key : Fine) :
      ‖SourceConditionalNativePosterior.decoder runtime read key -
        SourceConditionalVector.realizeModel runtime (SourceFibreExactState.observed runtime nonunit (samples key))‖ ^ 2 =
      ‖SourceFibreExactState.residual runtime nonunit (samples key)‖ ^ 2 := by
    rw [SourceFibreExactState.residual, SourceFibreExactState.model_source runtime nonunit (samples key) read key (budgets key)]
    change ‖SourceConditionalNativePosterior.decoder runtime read key -
      SourceConditionalVector.realizeModel runtime (SourceFibreExactState.observed runtime nonunit (samples key))‖ ^ 2 =
      ‖SourceConditionalVector.realizeModel runtime (SourceFibreExactState.observed runtime nonunit (samples key)) -
        SourceConditionalNativePosterior.decoder runtime read key‖ ^ 2
    rw [norm_sub_rev (SourceConditionalNativePosterior.decoder runtime read key)]
  simp_rw [error] at observed
  have coarse := SourceConditionalMergeLoss.loss runtime read forget
  simp_rw [decoder_source runtime nonunit samples read forget _ budgets]
  rw [noise_source runtime nonunit samples read budgets, lost_energy_source runtime nonunit samples read forget budgets,
    SourceConditionalMergeLoss.gap]
  linarith only [observed, coarse]

end
end SourceReceivedConditionalMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
