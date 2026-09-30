import H0mework.Versions.X.Fock.HistoryConditional.ReceivedKeyInventoryModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedKeyInventory

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalModel (Actors fullRead nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem clock_recovers (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (actor : Actors runtime)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    model runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
      samples (fullRead runtime actor) = nextRead runtime actor := by
  rw [model_source runtime nonunit (clockRead 0) samples (fullRead runtime actor) budgets]
  exact SourceConditionalNativeObservers.model_recovers runtime actor

theorem clock_next_recovers (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (actor : Actors runtime.tick.next)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    SourceConditionalVector.realizeModel runtime.tick.next
      (SourceFibreExactState.nextModel runtime nonunit
        (extend (inventoryBound runtime) (maximumIndex runtime).val
          (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun index => clockRead 0 index.val)) samples)
        (clockRead 0 runtime.tick.next.state) (fullRead runtime.tick.next actor)) =
      SourceCopyNativeModelStep.sourceValue ((history runtimeSeed (inventoryBound runtime.tick.next)).stageAt actor).next := by
  rw [SourceFibreExactState.next_model_source runtime nonunit _ (clockRead 0) _
    (extended_budgets runtime nonunit (clockRead 0) samples budgets)]
  exact SourceConditionalNativeObservers.decoder_recovers runtime.tick.next actor

end
end SourceReceivedKeyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
