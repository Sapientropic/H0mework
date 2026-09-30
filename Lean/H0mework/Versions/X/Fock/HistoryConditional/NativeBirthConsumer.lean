import H0mework.Versions.X.Fock.HistoryConditional.NativeBirthBudget

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeBirth

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem parity_total (runtime : LivingRuntimeState process) (depth : Nat) :
    total runtime (fun index : Nat => (index : ZMod 2)) =
      ((inventoryBound runtime + 1 : Nat) : ℝ) *
        SourceConditionalVector.dynamicError runtime depth (SourceConditionalNativeKeys.decoder runtime depth) := by
  rw [SourceConditionalVector.dynamicError, SourceConditionalInventory.sum_count]
  simp only [← SourceConditionalInventory.values_original]
  dsimp only [total]
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceConditionalMergeLoss.fine_field runtime depth]

theorem parity_stale (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalVector.dynamicError runtime.tick.next depth (SourceConditionalNativeKeys.decoder runtime.tick.next depth) <
      SourceConditionalVector.dynamicError runtime.tick.next depth (SourceConditionalNativeKeys.decoder runtime depth) := by
  have paid := stale_strict runtime (fun index : Nat => (index : ZMod 2))
  rw [parity_total runtime.tick.next depth] at paid
  have atNext (actor : Actors runtime.tick.next) :
      SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalModel.dynamicRead runtime.tick.next depth actor) =
        SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) (actor.val : ZMod 2) := by
    change SourceConditionalNativeKeys.decoder runtime depth
      (SourceConditionalInventory.observation (inventoryBound runtime.tick.next) depth actor) = _
    rw [SourceConditionalNativeKeys.source_observed, SourceConditionalNativePosterior.parity_decoder]
  have right : ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ) *
      SourceConditionalVector.dynamicError runtime.tick.next depth (SourceConditionalNativeKeys.decoder runtime depth) =
      ∑ actor : Actors runtime.tick.next, ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
        SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) (actor.val : ZMod 2)‖ ^ 2 := by
    rw [SourceConditionalVector.dynamicError, SourceConditionalInventory.sum_count]
    simp only [atNext, ← SourceConditionalInventory.values_original]
  rw [← right] at paid
  exact (mul_lt_mul_iff_right₀ (by positivity : (0 : ℝ) < (inventoryBound runtime.tick.next + 1 : Nat))).mp paid

theorem parity_model_update (runtime : LivingRuntimeState process) (depth : Nat) (key : ZMod 2) :
    update runtime (fun index : Nat => (index : ZMod 2)) key =
      SourceConditionalModelUpdate.updateModel runtime depth (SourceConditionalNativeKeys.observed depth key) := by
  rw [update_is_next, ← SourceConditionalNativePosterior.parity_model runtime.tick.next depth key,
    SourceConditionalNativeKeys.model_original, SourceConditionalRationalStream.model_original,
    SourceConditionalWordStream.model_original, SourceConditionalFiniteStream.model_next]

end
end SourceConditionalNativeBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
