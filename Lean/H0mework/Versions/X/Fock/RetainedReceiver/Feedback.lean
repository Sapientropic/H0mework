import H0mework.Versions.X.Fock.RetainedReceiver.Information

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalModel (Actors fullRead nextRead dynamicRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem clock_recovers (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ))
    (source : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (actor : Actors runtime) :
    model runtime frame (fullRead runtime actor) = nextRead runtime actor := by
  rw [model_source runtime frame (clockRead 0) _ source]
  exact SourceConditionalNativeObservers.model_recovers runtime actor

theorem history_next (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ))
    (source : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (actor : Actors runtime) :
    SourceConditionalVector.realizeModel runtime (model runtime frame (fullRead runtime actor)) =
      SourceCopyNativeModelStep.sourceValue ((history runtimeSeed (inventoryBound runtime)).stageAt actor).next := by
  rw [model_source runtime frame (clockRead 0) _ source]
  exact SourceConditionalNativeObservers.decoder_recovers runtime actor

theorem field_loss (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ))
    (source : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (depth : Nat) :
    SourceConditionalVector.dynamicError runtime depth (fieldDecoder runtime frame depth) =
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalVector.realizeModel runtime (model runtime frame (fullRead runtime actor))‖ ^ 2) +
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (model runtime frame (fullRead runtime actor)) -
          fieldDecoder runtime frame depth (dynamicRead runtime depth actor)‖ ^ 2) := by
  simp only [field_source runtime frame depth source keys,
    model_source runtime frame (clockRead 0) _ source]
  have paid := SourceConditionalNativeMerge.compression_loss runtime depth
  rw [SourceConditionalNativeMerge.decoder_original] at paid
  simpa only [SourceConditionalNativeObservers.decoder, SourceConditionalNativeObservers.model] using paid

theorem field_positive (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ))
    (source : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (depth : Nat) (enough : 2 ≤ inventoryBound runtime) :
    0 < SourceConditionalVector.dynamicError runtime depth (fieldDecoder runtime frame depth) := by
  rw [field_source runtime frame depth source keys]
  have paid := SourceConditionalNativeMerge.compression_positive runtime enough depth
  rw [SourceConditionalNativeMerge.decoder_original] at paid
  exact paid

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
