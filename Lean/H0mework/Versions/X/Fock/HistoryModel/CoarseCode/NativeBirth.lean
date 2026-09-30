import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionLoss
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Transport
import H0mework.Versions.X.Fock.HistoryConditional.NativeBirthInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem transported_bit_word {left right : Nat} (same : left = right)
    (word : List (Letter (left + 1))) (bit : ZMod 2) :
    SourceWordFutureBit.bitWord (right + 1)
        (SourceWordFutureBitGrowth.transportWord same word) bit =
      SourceWordFutureBit.bitWord (left + 1) word bit := by
  cases same
  rfl

theorem old_next_bit_word (depth : Nat) (word : List (Letter (depth + 1)))
    (bit : ZMod 2) :
    SourceWordFutureBit.bitWord (inventoryBound (runtimeAt (depth + 1)) + 1)
        (SourceWordFutureBitGrowth.nextWordAt depth word) bit =
      SourceWordFutureBit.bitWord (inventoryBound (runtimeAt depth) + 1)
        (SourceWordFutureBitGrowth.oldWordAt depth word) bit := by
  calc
    _ = SourceWordFutureBit.bitWord (depth + 2)
        (word.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter (depth + 1))) bit :=
      transported_bit_word _ _ _
    _ = SourceWordFutureBit.bitWord (depth + 1) word bit :=
      SourceWordFutureBitGrowth.old_bit_word (depth + 1) word bit
    _ = _ := (transported_bit_word _ _ _).symm

/-- The source's old word survives the actual new actor, while the same
    source-generated coarse action pays its new fine/coarse count difference. -/
theorem original_native_birth_information_loss (depth : Nat)
    (before after : List (Letter (depth + 1))) :
    let oldRead : Nat → ZMod 2 := SourceWordObservedCode.readAt
      (inventoryBound (runtimeAt depth)) (SourceWordFutureBitGrowth.oldWordAt depth before)
    let nextRead : Nat → ZMod 2 := SourceWordObservedCode.readAt
      (inventoryBound (runtimeAt (depth + 1))) (SourceWordFutureBitGrowth.nextWordAt depth before)
    let oldForget : ZMod 2 → ZMod 2 := SourceWordFutureBit.bitWord
      (inventoryBound (runtimeAt depth) + 1) (SourceWordFutureBitGrowth.oldWordAt depth after)
    let nextForget : ZMod 2 → ZMod 2 := SourceWordFutureBit.bitWord
      (inventoryBound (runtimeAt (depth + 1)) + 1) (SourceWordFutureBitGrowth.nextWordAt depth after)
    ((inventoryBound (runtimeAt (depth + 1)) + 1 : Nat) : ℝ) *
      SourceConditionalInformationLoss.amount (runtimeAt (depth + 1)) nextRead nextForget =
    ((inventoryBound (runtimeAt depth) + 1 : Nat) : ℝ) *
      SourceConditionalInformationLoss.amount (runtimeAt depth) oldRead oldForget +
      SourceConditionalNativeBirth.informationIncrement
        (SourceConditionalNativeMerge.count oldRead oldForget (inventoryBound (runtimeAt depth))
          (SourceConditionalNativeObservers.generate oldRead (inventoryBound (runtimeAt depth)))
          (oldForget (oldRead (inventoryBound (runtimeAt depth) + 1)))) -
      SourceConditionalNativeBirth.informationIncrement
        (SourceConditionalNativeObservers.generate oldRead (inventoryBound (runtimeAt depth))
          (oldRead (inventoryBound (runtimeAt depth) + 1))).1 := by
  dsimp only
  have sameRead :
      SourceWordObservedCode.readAt (inventoryBound (runtimeAt (depth + 1)))
          (SourceWordFutureBitGrowth.nextWordAt depth before) =
        SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
          (SourceWordFutureBitGrowth.oldWordAt depth before) := by
    funext index
    exact SourceWordFutureBitGrowth.old_next_read_at depth before index
  have sameForget :
      SourceWordFutureBit.bitWord (inventoryBound (runtimeAt (depth + 1)) + 1)
          (SourceWordFutureBitGrowth.nextWordAt depth after) =
        SourceWordFutureBit.bitWord (inventoryBound (runtimeAt depth) + 1)
          (SourceWordFutureBitGrowth.oldWordAt depth after) := by
    funext bit
    exact old_next_bit_word depth after bit
  rw [sameRead, sameForget, SourceWordFutureBitGrowth.next_runtime]
  exact SourceConditionalNativeBirth.amount_next (runtimeAt depth)
    (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
      (SourceWordFutureBitGrowth.oldWordAt depth before))
    (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt depth) + 1)
      (SourceWordFutureBitGrowth.oldWordAt depth after))

private theorem actual_copy_fine_birth_count :
    (SourceConditionalNativeObservers.generate
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
        (SourceWordFutureBitGrowth.oldWordAt 3 []))
      (inventoryBound (runtimeAt 3))
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
        (SourceWordFutureBitGrowth.oldWordAt 3 [])
        (inventoryBound (runtimeAt 3) + 1))).1 = 2 := by
  decide

private theorem actual_copy_coarse_birth_count :
    SourceConditionalNativeMerge.count
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
        (SourceWordFutureBitGrowth.oldWordAt 3 []))
      (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 3) + 1)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]))
      (inventoryBound (runtimeAt 3))
      (SourceConditionalNativeObservers.generate
        (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
          (SourceWordFutureBitGrowth.oldWordAt 3 []))
        (inventoryBound (runtimeAt 3)))
      (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 3) + 1)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
        (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
          (SourceWordFutureBitGrowth.oldWordAt 3 [])
          (inventoryBound (runtimeAt 3) + 1))) = 4 := by
  decide

theorem actual_copy_native_birth_information_loss :
    let oldRead : Nat → ZMod 2 := SourceWordObservedCode.readAt
      (inventoryBound (runtimeAt 3)) (SourceWordFutureBitGrowth.oldWordAt 3 [])
    let nextRead : Nat → ZMod 2 := SourceWordObservedCode.readAt
      (inventoryBound (runtimeAt 4)) (SourceWordFutureBitGrowth.nextWordAt 3 [])
    let oldForget : ZMod 2 → ZMod 2 := SourceWordFutureBit.bitWord
      (inventoryBound (runtimeAt 3) + 1)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
    let nextForget : ZMod 2 → ZMod 2 := SourceWordFutureBit.bitWord
      (inventoryBound (runtimeAt 4) + 1)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
    (5 : ℝ) * SourceConditionalInformationLoss.amount (runtimeAt 4) nextRead nextForget =
      (4 : ℝ) * SourceConditionalInformationLoss.amount (runtimeAt 3) oldRead oldForget +
        SourceConditionalNativeBirth.informationIncrement 4 -
          SourceConditionalNativeBirth.informationIncrement 2 := by
  have birth := original_native_birth_information_loss 3 [] [SourceWordDynamicNext.copyOne]
  dsimp only at birth ⊢
  rw [actual_copy_coarse_birth_count, actual_copy_fine_birth_count] at birth
  simpa only [inventory_bound, runtimeAt_state, Nat.reduceAdd, Nat.cast_ofNat] using birth

theorem actual_copy_birth_correction_positive :
    0 < SourceConditionalNativeBirth.informationIncrement 4 -
      SourceConditionalNativeBirth.informationIncrement 2 := by
  have strict : (6 : ℝ) * Real.log 2 + 3 * Real.log 3 < 5 * Real.log 5 := by
    have comparison := Real.log_lt_log
      (show (0 : ℝ) < 2 ^ 6 * 3 ^ 3 by norm_num)
      (show (2 : ℝ) ^ 6 * 3 ^ 3 < 5 ^ 5 by norm_num)
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow] at comparison
    norm_num at comparison ⊢
    exact comparison
  have four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  unfold SourceConditionalNativeBirth.informationIncrement
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
  rw [four]
  nlinarith

theorem original_native_birth_empty_tail_correction (depth : Nat)
    (before : List (Letter (depth + 1))) :
    let read : Nat → ZMod 2 := SourceWordObservedCode.readAt
      (inventoryBound (runtimeAt depth)) (SourceWordFutureBitGrowth.oldWordAt depth before)
    let forget : ZMod 2 → ZMod 2 := SourceWordFutureBit.bitWord
      (inventoryBound (runtimeAt depth) + 1) (SourceWordFutureBitGrowth.oldWordAt depth [])
    SourceConditionalNativeBirth.informationIncrement
      (SourceConditionalNativeMerge.count read forget (inventoryBound (runtimeAt depth))
        (SourceConditionalNativeObservers.generate read (inventoryBound (runtimeAt depth)))
        (forget (read (inventoryBound (runtimeAt depth) + 1)))) -
      SourceConditionalNativeBirth.informationIncrement
        (SourceConditionalNativeObservers.generate read (inventoryBound (runtimeAt depth))
          (read (inventoryBound (runtimeAt depth) + 1))).1 = 0 := by
  dsimp only
  have oldForget : SourceWordFutureBit.bitWord
      (inventoryBound (runtimeAt depth) + 1)
      (SourceWordFutureBitGrowth.oldWordAt depth []) = id := by
    funext bit
    exact transported_bit_word _ _ bit
  have nextForget : SourceWordFutureBit.bitWord
      (inventoryBound (runtimeAt (depth + 1)) + 1)
      (SourceWordFutureBitGrowth.nextWordAt depth []) = id := by
    funext bit
    exact (old_next_bit_word depth [] bit).trans (congrFun oldForget bit)
  have birth := original_native_birth_information_loss depth before []
  dsimp only at birth
  rw [oldForget, nextForget] at birth
  have oldZero := (SourceConditionalInformationLoss.amount_lossless_iff
    (runtimeAt depth)
    (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
      (SourceWordFutureBitGrowth.oldWordAt depth before)) id).mpr
    (by intro _ _ same; exact same)
  have nextZero := (SourceConditionalInformationLoss.amount_lossless_iff
    (runtimeAt (depth + 1))
    (SourceWordObservedCode.readAt (inventoryBound (runtimeAt (depth + 1)))
      (SourceWordFutureBitGrowth.nextWordAt depth before)) id).mpr
    (by intro _ _ same; exact same)
  rw [oldZero, nextZero] at birth
  simp only [mul_zero, zero_add] at birth
  rw [oldForget]
  exact birth.symm

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
