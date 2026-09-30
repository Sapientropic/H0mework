import H0mework.Versions.X.Fock.HistoryConditional.ReceivedKeyInventoryFeedback

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedKeyInventory

variable {Key Coarse : Type*} [DecidableEq Key] [DecidableEq Coarse]

def advanceMerged (bound stride : Nat) (nonunit : stride ≠ 0) (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples bound (stride + 1))
    (forget : Key → Coarse) (added : Key) : SourceConditionalNativeObservers.State Coarse (bound + 1) :=
  SourceConditionalNativeMerge.inventoryMerge (insert added keys) forget (bound + 1)
    (SourceConditionalNativeObservers.advance (fun _ => added) bound (restore bound stride nonunit keys samples))

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem merged_next_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (forget : Key → Coarse)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    advanceMerged (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples forget
      (read runtime.tick.next.state) = SourceConditionalNativeObservers.generate (forget ∘ read) (inventoryBound runtime + 1) := by
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  rw [advanceMerged, restored_source runtime nonunit read samples budgets, receipt, ← SourceConditionalInventory.outputs_append]
  have actual : SourceConditionalNativeObservers.advance (fun _ => read (inventoryBound runtime + 1)) (inventoryBound runtime)
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime)) =
        SourceConditionalNativeObservers.generate read (inventoryBound runtime + 1) := rfl
  rw [actual]
  exact SourceConditionalNativeMerge.merged_generated read forget (inventoryBound runtime + 1)

end
end SourceReceivedKeyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
