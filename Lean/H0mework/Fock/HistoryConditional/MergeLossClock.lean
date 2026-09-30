import H0mework.Fock.HistoryConditional.MergeLossLoss

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalMergeLoss

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead dynamicRead fullRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem clock_decoder (runtime : LivingRuntimeState process) (depth : Nat) (key : ZMod 2) :
    decoder runtime (SourceConditionalNativeObservers.clockRead 0) SourceConditionalNativeMerge.forgetClock key =
      SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key) := by
  have same : SourceConditionalNativeMerge.forgetClock ∘ SourceConditionalNativeObservers.clockRead 0 =
      (fun index : Nat => (index : ZMod 2)) := funext SourceConditionalNativeMerge.clock_factor
  rw [decoder_original, same, ← SourceConditionalNativePosterior.parity_decoder runtime depth]

theorem clock_fine (runtime : LivingRuntimeState process) (actor : Actors runtime) :
    SourceConditionalNativePosterior.decoder runtime (SourceConditionalNativeObservers.clockRead 0)
      (SourceConditionalNativeObservers.clockRead 0 actor.val) =
      SourceConditionalNativeObservers.decoder runtime (fullRead runtime actor) := by
  rw [SourceConditionalNativeObservers.full_source]
  rfl

theorem clock_field (runtime : LivingRuntimeState process) (depth : Nat) (actor : Actors runtime) :
    decoder runtime (SourceConditionalNativeObservers.clockRead 0) SourceConditionalNativeMerge.forgetClock
      (SourceConditionalNativeMerge.forgetClock (SourceConditionalNativeObservers.clockRead 0 actor.val)) =
      SourceConditionalNativeKeys.decoder runtime depth (dynamicRead runtime depth actor) := by
  rw [SourceConditionalNativeMerge.clock_factor, clock_decoder runtime depth]
  have observed := SourceConditionalNativeKeys.source_observed (inventoryBound runtime) depth actor
  rw [SourceConditionalInventory.observation_original] at observed
  rw [observed]

theorem clock_loss (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalVector.dynamicError runtime depth (SourceConditionalNativeKeys.decoder runtime depth) =
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalNativeObservers.decoder runtime (fullRead runtime actor)‖ ^ 2) +
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalNativeObservers.decoder runtime (fullRead runtime actor) -
          SourceConditionalNativeKeys.decoder runtime depth (dynamicRead runtime depth actor)‖ ^ 2) := by
  have paid := loss runtime (SourceConditionalNativeObservers.clockRead 0) SourceConditionalNativeMerge.forgetClock
  simpa only [clock_fine, clock_field runtime depth, SourceConditionalVector.dynamicError] using paid

end
end SourceConditionalMergeLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
