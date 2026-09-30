import H0mework.Versions.X.Fock.HistoryConditional.ReceivedMergeLoss

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse] [Fintype Fine]

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

theorem recovery_budget [MeasurableSpace Coarse] [MeasurableSingletonClass Coarse] (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    SourceConditionalInventory.cost (inventoryBound runtime) (fun actor : Actors runtime => forget (read actor.val)) /
        (inventoryBound runtime + 1 : ℝ) +
      (Real.exp (2 * (SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
        (fun actor : Actors runtime => read actor.val) (SourceConditionalNext.Image.actual (nextRead runtime)) (SourceConditionalModel.positive runtime) +
          information forget (inventoryBound runtime)
            (SourceFibreExactState.restoreState (inventoryBound runtime) (maximumIndex runtime).val nonunit samples))) - 1) / 12 ≤
        (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
          ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
            SourceConditionalVector.realizeModel runtime (SourceFibreExactState.model runtime nonunit (samples (read actor.val)))‖ ^ 2) +
          lostEnergy runtime nonunit samples forget := by
  have fine (key : Fine) : SourceConditionalVector.realizeModel runtime
      (SourceFibreExactState.model runtime nonunit (samples key)) = SourceConditionalNativePosterior.decoder runtime read key := by
    rw [SourceFibreExactState.model_source runtime nonunit (samples key) read key (budgets key)]
    rfl
  simp_rw [fine]
  rw [received_information runtime nonunit samples read forget budgets,
    lost_energy_source runtime nonunit samples read forget budgets]
  exact SourceConditionalInformationLoss.recovery_budget runtime read forget

theorem no_free_merge (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse)
    (left right : Actors runtime) (merged : forget (read left.val) = forget (read right.val))
    (different : read left.val ≠ read right.val)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    0 < lostEnergy runtime nonunit samples forget := by
  rw [lost_energy_source runtime nonunit samples read forget budgets]
  exact SourceConditionalMergeLoss.gap_positive_of_collision runtime read forget left right merged different

end
end SourceReceivedConditionalMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
