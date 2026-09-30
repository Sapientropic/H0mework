import H0mework.Fock.HistoryConditional.ReceivedKeyInventoryClock

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedKeyInventory

variable {Key Coarse : Type*} [DecidableEq Key] [DecidableEq Coarse]

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def merge (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (forget : Key → Coarse) : SourceConditionalNativeObservers.State Coarse (inventoryBound runtime) :=
  SourceConditionalNativeMerge.inventoryMerge keys forget (inventoryBound runtime)
    (restore (inventoryBound runtime) (maximumIndex runtime).val nonunit keys samples)

theorem merge_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (forget : Key → Coarse)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    merge runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples forget =
      SourceConditionalNativeObservers.generate (forget ∘ read) (inventoryBound runtime) := by
  rw [merge, restored_source runtime nonunit read samples budgets]
  exact SourceConditionalNativeMerge.merged_generated read forget (inventoryBound runtime)

open SourceConditionalNativeObservers (clockRead)

theorem clock_parity (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    merge runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
      samples SourceConditionalNativeMerge.forgetClock = SourceConditionalNativeKeys.generate (inventoryBound runtime) := by
  rw [merge, restored_source runtime nonunit (clockRead 0) samples budgets]
  exact SourceConditionalNativeMerge.state_original (inventoryBound runtime)

end
end SourceReceivedKeyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
