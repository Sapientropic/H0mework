import H0mework.Versions.X.Fock.RetainedReceiver.Complete

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

open SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceConditionalNativeObservers (clockRead)
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def fieldDecoder (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ)) (depth : Nat) (value : Field parity) :
    SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
    (SourceConditionalNativeKeys.embed (inventoryBound runtime) depth
      (SourceConditionalNativeMerge.inventoryMerge frame.keys SourceConditionalNativeMerge.forgetClock
        (inventoryBound runtime) frame.native) value).2)

theorem field_source (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ)) (depth : Nat)
    (source : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) :
    fieldDecoder runtime frame depth = SourceConditionalNativeKeys.decoder runtime depth := by
  funext value
  rw [fieldDecoder, source, keys]
  rw [show SourceConditionalNativeMerge.inventoryMerge _ _ _ _ = _ from
    SourceConditionalNativeMerge.state_original (inventoryBound runtime)]
  rfl

theorem field_information (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ)) (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime depth (fieldDecoder runtime frame depth)) :=
  SourceInformationReadback.model_decoder_cost runtime depth _

theorem continued_field (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (steps depth : Nat) :
    let initial := start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
    fieldDecoder (runtime.advance steps)
      (trajectory runtime initial (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) steps) depth =
        SourceConditionalNativeKeys.decoder (runtime.advance steps) depth := by
  dsimp only
  apply field_source
  · exact trajectory_native runtime _ (clockRead 0)
      (start_native runtime nonunit (clockRead 0) samples budgets) steps
  · exact trajectory_keys runtime _ (clockRead 0) rfl steps

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
