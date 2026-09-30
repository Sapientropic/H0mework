import H0mework.Fock.HistoryConditional.ReceivedMergeMaterial
import H0mework.Probability.Information.InventoryGrowth

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedKeyInventory

variable {Key : Type*} [DecidableEq Key]

def extend (bound stride : Nat) (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples bound (stride + 1)) :
    Key → SourceRationalWindowReadout.Samples bound (stride + 1) := fun key =>
  if present : key ∈ keys then samples ⟨key, present⟩ else 0

def restore (bound stride : Nat) (nonunit : stride ≠ 0) (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples bound (stride + 1)) :
    SourceConditionalNativeObservers.State Key bound :=
  SourceFibreExactState.restoreState bound stride nonunit (extend bound stride keys samples)

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem extended_budgets (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    ∀ key : Key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0
          (extend (inventoryBound runtime) (maximumIndex runtime).val
            (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2 := by
  intro key
  by_cases present : key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)
  · simpa only [extend, dif_pos present] using budgets ⟨key, present⟩
  · have absent : SourceConditionalNativePosterior.decoder runtime read key = 0 := by
      simp only [SourceConditionalNativePosterior.decoder, SourceConditionalNativePosterior.model,
        SourceReceivedConditionalMerge.outside_row read (inventoryBound runtime) key present,
        Rat.cast_zero, zero_smul, Finset.sum_const_zero, map_zero]
    rw [extend, dif_neg present, absent, map_zero, sub_zero]
    have positive := SourcePosteriorStability.threshold_positive runtime
    simpa [SourceWindowPrecision.sampleEnergy, SourceRationalWindowReadout.embed,
      SourceFiniteObserverCalculation.finiteRead] using sq_pos_of_pos positive

theorem restored_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    restore (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples =
        SourceConditionalNativeObservers.generate read (inventoryBound runtime) := by
  rw [restore]
  exact SourceFibreExactState.state_source runtime nonunit _ read (extended_budgets runtime nonunit read samples budgets)

theorem keys_next (runtime : LivingRuntimeState process) (read : Nat → Key) :
    insert (read runtime.tick.next.state)
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) =
        SourceUniformFibreVariance.outputs (inventoryBound runtime.tick.next) (fun actor => read actor.val) := by
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  rw [receipt, SourceActualImageStep.next_bound, SourceConditionalInventory.outputs_append]

end
end SourceReceivedKeyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
