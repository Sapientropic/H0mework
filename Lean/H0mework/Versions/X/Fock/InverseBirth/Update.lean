import H0mework.Versions.X.Fock.InverseBirth.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimalBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem next_bias (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    (∑ actor : Actors runtime, ‖decoder runtime depth word read (read actor.val) -
      decoder runtime.tick.next depth word read (read actor.val)‖ ^ 2) =
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 *
        ‖decoder runtime depth word read (read (inventoryBound runtime + 1)) -
          decoder runtime.tick.next depth word read (read (inventoryBound runtime + 1))‖ ^ 2 := by
  have count := congrArg (fun value : Nat => (value : ℝ))
    (SourceConditionalNativePosterior.count_sum read (inventoryBound runtime) (read (inventoryBound runtime + 1)))
  push_cast at count
  rw [count, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro actor _
  by_cases selected : read actor.val = read (inventoryBound runtime + 1)
  · rw [selected, if_pos rfl, one_mul]
  · rw [decoder_next, if_neg selected, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), if_neg selected, zero_mul]

theorem minimum_difference (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    total runtime.tick.next depth word read = total runtime depth word read +
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 *
        ‖decoder runtime depth word read (read (inventoryBound runtime + 1)) -
          decoder runtime.tick.next depth word read (read (inventoryBound runtime + 1))‖ ^ 2 +
      ‖SourceConditionalInventory.born (inventoryBound runtime) -
        decoder runtime.tick.next depth word read (read (inventoryBound runtime + 1))‖ ^ 2 := by
  rw [total, SourceConditionalNativeBirth.total_append runtime read (decoder runtime.tick.next depth word read)]
  change (∑ actor : Actors runtime, ‖SourceConditionalInventory.values (inventoryBound runtime) actor -
      SourceCompiledGWord.effect depth word
        (SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime.tick.next read (read actor.val)))‖ ^ 2) + _ = _
  rw [total_decomposition runtime depth word read
    (fun key => SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime.tick.next read key))]
  change total runtime depth word read +
    (∑ actor : Actors runtime, ‖decoder runtime depth word read (read actor.val) - decoder runtime.tick.next depth word read (read actor.val)‖ ^ 2) + _ = _
  rw [next_bias]

end
end SourceInverseDistributionOptimalBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
