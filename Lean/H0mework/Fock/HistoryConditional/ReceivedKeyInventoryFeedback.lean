import H0mework.Fock.HistoryConditional.ReceivedKeyInventoryMerge

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedKeyInventory

variable {Key : Type*} [DecidableEq Key]
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem next_residual (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    let received := extend (inventoryBound runtime) (maximumIndex runtime).val
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
    SourceConditionalVector.realizeModel runtime.tick.next
      (SourceStableReceivedCount.updatedModel runtime nonunit (received key) (decide (key = read runtime.tick.next.state))) -
      SourceConditionalVector.realizeModel runtime.tick.next
        (SourceFibreExactState.nextModel runtime nonunit received (read runtime.tick.next.state) key) =
      if key = read runtime.tick.next.state then
        (SourceStableReceivedCount.contraction
          (restore (inventoryBound runtime) (maximumIndex runtime).val nonunit
            (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples key).1 : ℂ) •
          SourceFibreExactState.residual runtime nonunit (received key)
      else SourceFibreExactState.residual runtime nonunit (received key) :=
  SourceFibreExactState.next_residual runtime nonunit _ read key (extended_budgets runtime nonunit read samples budgets)

end
end SourceReceivedKeyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
