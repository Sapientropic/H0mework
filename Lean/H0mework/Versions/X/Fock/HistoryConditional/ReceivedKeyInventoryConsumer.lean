import H0mework.Versions.X.Fock.HistoryConditional.ReceivedKeyInventoryFieldNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedKeyInventory

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalModel (Actors fullRead dynamicRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem compression_loss (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (depth : Nat)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    SourceConditionalVector.dynamicError runtime depth
      (fieldDecoder runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples depth) =
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime
          (model runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun index => clockRead 0 index.val))
            samples (fullRead runtime actor)) -
          fieldDecoder runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun index => clockRead 0 index.val))
            samples depth (dynamicRead runtime depth actor)‖ ^ 2 := by
  have fine (actor : Actors runtime) : SourceConditionalVector.realizeModel runtime
      (model runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun index => clockRead 0 index.val))
        samples (fullRead runtime actor)) = SourceConditionalNativeObservers.decoder runtime (fullRead runtime actor) := by
    rw [model_source runtime nonunit (clockRead 0) samples (fullRead runtime actor) budgets]
    rfl
  simp_rw [fine, field_decoder_source runtime nonunit samples depth budgets]
  have paid := SourceConditionalNativeMerge.compression_loss runtime depth
  rw [SourceConditionalNativeObservers.error_zero, zero_add, SourceConditionalNativeMerge.decoder_original] at paid
  exact paid

theorem full_mixture (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : ZMod 2)
    (supported : key ∈ (SourceConditionalHistory.observed
      (SourceConditionalHistory.observed (historyPMF (inventoryBound runtime)) (fullRead runtime))
        SourceConditionalNativeMerge.forgetClock).support)
    (actor : Actors runtime)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    ((merge runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun index => clockRead 0 index.val))
      samples SourceConditionalNativeMerge.forgetClock key).2 actor : ℝ) =
      (SourceConditionalHistory.Coarsening.mixture (historyPMF (inventoryBound runtime)) (fullRead runtime)
        SourceConditionalNativeMerge.forgetClock key supported actor).toReal := by
  rw [clock_parity runtime nonunit samples budgets]
  have paid := SourceConditionalNativeMerge.full_mixture runtime key supported actor
  rw [SourceConditionalNativeMerge.state_original] at paid
  exact paid

end
end SourceReceivedKeyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
