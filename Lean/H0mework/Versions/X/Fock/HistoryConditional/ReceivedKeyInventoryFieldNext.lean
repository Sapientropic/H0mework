import H0mework.Versions.X.Fock.HistoryConditional.ReceivedKeyInventoryField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedKeyInventory

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem table_next (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (depth : Nat)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    SourceConditionalNativeKeys.embed (inventoryBound runtime + 1) depth
      (advanceMerged (inventoryBound runtime) (maximumIndex runtime).val nonunit
        (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
        SourceConditionalNativeMerge.forgetClock (clockRead 0 runtime.tick.next.state)) =
      SourceConditionalRationalStream.advance (inventoryBound runtime) depth
        (SourceConditionalNativeKeys.embed (inventoryBound runtime) depth
          (merge runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
            samples SourceConditionalNativeMerge.forgetClock)) := by
  rw [merged_next_source runtime nonunit (clockRead 0) SourceConditionalNativeMerge.forgetClock samples budgets,
    clock_parity runtime nonunit samples budgets]
  have keys : SourceConditionalNativeMerge.forgetClock ∘ clockRead 0 = (fun index : Nat => (index : ZMod 2)) :=
    funext SourceConditionalNativeMerge.clock_factor
  rw [keys]
  have paid := SourceConditionalNativeMerge.table_next runtime depth
  rw [SourceConditionalNativeMerge.state_original, SourceConditionalNativeMerge.state_original, SourceActualImageStep.next_bound] at paid
  exact paid

end
end SourceReceivedKeyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
