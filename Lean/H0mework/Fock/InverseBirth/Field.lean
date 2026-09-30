import H0mework.Fock.InverseBirth.Born

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimalBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem total_optimal {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (guess : Key → SourceJointClockGraph.Carrier) :
    total runtime depth word read ≤
      ∑ actor : Actors runtime, ‖SourceConditionalInventory.values (inventoryBound runtime) actor -
        SourceCompiledGWord.effect depth word (guess (read actor.val))‖ ^ 2 := by
  rw [total_decomposition]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem field_total (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) :
    total runtime depth word (fun index : Nat => (index : ZMod 2)) =
      ((inventoryBound runtime + 1 : Nat) : ℝ) *
        SourceConditionalVector.dynamicError runtime depth
          (fun observed => project depth word (SourceConditionalNativeKeys.decoder runtime depth observed)) := by
  rw [SourceConditionalVector.dynamicError, SourceConditionalInventory.sum_count]
  dsimp only [total]
  simp only [← SourceConditionalInventory.values_original]
  apply Finset.sum_congr rfl
  intro actor _
  change ‖SourceConditionalInventory.values (inventoryBound runtime) actor -
      decoder runtime depth word (fun index : Nat => (index : ZMod 2)) (actor.val : ZMod 2)‖ ^ 2 =
    ‖SourceConditionalInventory.values (inventoryBound runtime) actor -
      project depth word (SourceConditionalNativeKeys.decoder runtime depth
        (SourceConditionalInventory.observation (inventoryBound runtime) depth actor))‖ ^ 2
  rw [SourceConditionalNativeKeys.source_observed, SourceConditionalNativePosterior.parity_decoder]
  rfl

theorem field_minimum_update (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) :
    ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ) *
      SourceConditionalVector.dynamicError runtime.tick.next depth
        (fun observed => project depth word (SourceConditionalNativeKeys.decoder runtime.tick.next depth observed)) =
    ((inventoryBound runtime + 1 : Nat) : ℝ) *
      SourceConditionalVector.dynamicError runtime depth
        (fun observed => project depth word (SourceConditionalNativeKeys.decoder runtime depth observed)) +
      increment runtime depth word (fun index : Nat => (index : ZMod 2)) := by
  rw [← field_total, ← field_total]
  exact minimum_update runtime depth word (fun index : Nat => (index : ZMod 2))

theorem minimum_monotone {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    total runtime depth word read ≤ total runtime.tick.next depth word read := by
  rw [minimum_update]
  apply le_add_of_nonneg_right
  dsimp only [increment]
  positivity

end
end SourceInverseDistributionOptimalBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
