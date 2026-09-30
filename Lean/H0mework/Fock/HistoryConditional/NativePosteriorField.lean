import H0mework.Fock.HistoryConditional.NativePosteriorEffect
import H0mework.Fock.HistoryConditional.NativeKeysConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativePosterior

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem parity_decoder (runtime : LivingRuntimeState process) (depth : Nat) (key : ZMod 2) :
    SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key) =
      decoder runtime (fun index : Nat => (index : ZMod 2)) key := by
  rw [SourceConditionalNativeKeys.decoder, SourceConditionalNativeKeys.embed_at, decoder, model]
  simp only [map_sum, map_smul]
  change SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
    (∑ index : SourceConditionalModel.Actors runtime,
      (SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 index •
        SourceConditionalRationalStream.sourceWord (inventoryBound runtime) index)) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [map_smul, ← algebraMap_smul ℂ, map_smul, SourceConditionalRationalStream.source_embed,
    SourceConditionalWordStream.source_read, SourceConditionalInventory.values_original]
  rfl

theorem parity_model (runtime : LivingRuntimeState process) (depth : Nat) (key : ZMod 2) :
    SourceConditionalNativeKeys.model runtime depth (SourceConditionalNativeKeys.observed depth key) =
      model runtime (fun index : Nat => (index : ZMod 2)) key := by
  rw [SourceConditionalNativeKeys.model, parity_decoder, decoder]
  exact SourceConditionalStream.project_realization runtime _


theorem field_error (runtime : LivingRuntimeState process) (depth : Nat) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map
      (fun actor : SourceConditionalModel.Actors runtime => (actor.val : ZMod 2))).support)
    (candidate : SourceJointClockGraph.Carrier) :
    (∑ actor : SourceConditionalModel.Actors runtime,
      ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (SourceConditionalModel.nextRead runtime actor) - candidate‖ ^ 2) =
    (∑ actor : SourceConditionalModel.Actors runtime,
      ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (SourceConditionalModel.nextRead runtime actor) -
        SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key)‖ ^ 2) +
      ‖SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key) - candidate‖ ^ 2 := by
  rw [parity_decoder]
  exact error_decomposition runtime (fun index : Nat => (index : ZMod 2)) key supported candidate

theorem field_residual (runtime : LivingRuntimeState process) (depth : Nat) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map
      (fun actor : SourceConditionalModel.Actors runtime => (actor.val : ZMod 2))).support) :
    (∑ actor : SourceConditionalModel.Actors runtime,
      ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next
        (SourceConditionalModel.nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) -
        SourceConditionalVector.realizeModel runtime.tick.next
          (SourceCopyNativeSharedUpdate.modelStep runtime.tick.next
            (SourceConditionalNativeKeys.model runtime depth (SourceConditionalNativeKeys.observed depth key)))‖ ^ 2) =
    (∑ actor : SourceConditionalModel.Actors runtime,
      ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (SourceConditionalModel.nextRead runtime actor) -
        SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key)‖ ^ 2) := by
  rw [parity_model, parity_decoder]
  simpa only [effect, SourceConditionalNativeKeys.generate] using
    effect_residual runtime (fun index : Nat => (index : ZMod 2)) key supported

end
end SourceConditionalNativePosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
