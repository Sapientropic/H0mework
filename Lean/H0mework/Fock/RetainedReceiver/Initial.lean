import H0mework.Fock.RetainedReceiver.Residual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem start_value (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key) :
    value runtime (start (inventoryBound runtime) (maximumIndex runtime).val nonunit keys samples) key =
      SourceConditionalVector.realizeModel runtime (SourceFibreExactState.observed runtime nonunit
        (SourceReceivedKeyInventory.extend (inventoryBound runtime) (maximumIndex runtime).val keys samples key)) := by
  rw [value, start_raw]
  exact SourceRationalWindowReadout.decoded_model runtime nonunit _

theorem start_model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key) :
    model runtime (start (inventoryBound runtime) (maximumIndex runtime).val nonunit keys samples) key =
      SourceFibreExactState.model runtime nonunit
        (SourceReceivedKeyInventory.extend (inventoryBound runtime) (maximumIndex runtime).val keys samples key) := rfl

theorem start_residual (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key) :
    residual runtime (start (inventoryBound runtime) (maximumIndex runtime).val nonunit keys samples) key =
      SourceFibreExactState.residual runtime nonunit
        (SourceReceivedKeyInventory.extend (inventoryBound runtime) (maximumIndex runtime).val keys samples key) := by
  rw [residual, start_value, start_model]
  rfl

theorem start_bound (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    ‖residual runtime (start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples) key‖ ^ 2 ≤
      SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
        SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
          (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0
            (SourceReceivedKeyInventory.extend (inventoryBound runtime) (maximumIndex runtime).val
              (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples key) -
            SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
              (SourceConditionalNativePosterior.decoder runtime read key)) := by
  rw [start_residual]
  exact SourceFibreExactState.residual_bound runtime nonunit _ read key
    (SourceReceivedKeyInventory.extended_budgets runtime nonunit read samples budgets key)

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
