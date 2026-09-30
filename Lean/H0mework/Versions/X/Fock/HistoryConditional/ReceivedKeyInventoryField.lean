import H0mework.Versions.X.Fock.HistoryConditional.ReceivedKeyInventoryUpdate
import H0mework.Versions.X.Fock.HistoryConditional.NativeMergeConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedKeyInventory

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def fieldDecoder (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : Finset (ℤ × ℤ))
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (depth : Nat) (value : Field parity) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
    (SourceConditionalNativeKeys.embed (inventoryBound runtime) depth
      (merge runtime nonunit keys samples SourceConditionalNativeMerge.forgetClock) value).2)

theorem field_decoder_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (depth : Nat)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    fieldDecoder runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
      samples depth = SourceConditionalNativeKeys.decoder runtime depth := by
  funext value
  rw [fieldDecoder, clock_parity runtime nonunit samples budgets]
  rfl

theorem information_cost (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : Finset (ℤ × ℤ))
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime depth (fieldDecoder runtime nonunit keys samples depth)) :=
  SourceInformationReadback.model_decoder_cost runtime depth _

theorem compression_positive (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (depth : Nat) (enough : 2 ≤ inventoryBound runtime)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    0 < SourceConditionalVector.dynamicError runtime depth
      (fieldDecoder runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples depth) := by
  rw [field_decoder_source runtime nonunit samples depth budgets]
  have paid := SourceConditionalNativeMerge.compression_positive runtime enough depth
  rw [SourceConditionalNativeMerge.decoder_original] at paid
  exact paid

end
end SourceReceivedKeyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
