import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.Consumer
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Controls
import H0mework.Versions.X.Fock.HistoryConditional.InformationLossRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
attribute [local instance] fieldUniformSpace fieldMeasurable fieldBorelSpace fieldT2

theorem actual_word_append (depth : Nat) (before after : List (Letter depth))
    (state : Current) :
    actualWord depth (before ++ after) state =
      actualWord depth after (actualWord depth before state) := by
  induction before generalizing state with
  | nil => rfl
  | cons letter rest ih =>
      change actualWord depth (rest ++ after) (step depth letter state) =
        actualWord depth after (actualWord depth rest (step depth letter state))
      exact ih _

theorem source_query_append (runtime : LivingRuntimeState process)
    (before after : List (Letter (inventoryBound runtime + 1)))
    (actor : SourceConditionalModel.Actors runtime) :
    SourceWordObservedCode.sourceQuery runtime (before ++ after) actor =
      SourceWordFutureBit.bitWord (inventoryBound runtime + 1) after
        (SourceWordObservedCode.sourceQuery runtime before actor) := by
  let state : Current :=
    ((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.current.visit.current
  change SourceWordObservedCode.observe
      (actualWord (inventoryBound runtime + 1) (before ++ after) state) =
    SourceWordFutureBit.bitWord (inventoryBound runtime + 1) after
      (SourceWordObservedCode.observe (actualWord (inventoryBound runtime + 1) before state))
  exact (congrArg SourceWordObservedCode.observe
    (actual_word_append (inventoryBound runtime + 1) before after state)).trans
      (SourceWordFutureBit.word_observe _ after _)

theorem original_field_action_square (depth : Nat)
    (before after : List (Letter (depth + 1))) (actor : Fin (depth + 1)) :
    fieldCode depth (before ++ after) (Actor.nextRead (depth + 1) depth actor) =
      SourceWordFutureBit.bitWord (depth + 1) after
        (fieldCode depth before (Actor.nextRead (depth + 1) depth actor)) := by
  rw [actual_square, actual_square]
  unfold SourceWordObservedCode.readAt
  rw [actual_word_append]
  exact SourceWordFutureBit.word_observe _ after _

theorem read_at_append (depth : Nat)
    (before after : List (Letter (depth + 1))) (index : Nat) :
    SourceWordObservedCode.readAt depth (before ++ after) index =
      SourceWordFutureBit.bitWord (depth + 1) after
        (SourceWordObservedCode.readAt depth before index) := by
  unfold SourceWordObservedCode.readAt
  rw [actual_word_append]
  exact SourceWordFutureBit.word_observe _ after _

theorem source_information_tower (runtime : LivingRuntimeState process)
    (before after : List (Letter (inventoryBound runtime + 1))) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
      (SourceWordObservedCode.sourceQuery runtime before)
      (SourceConditionalNext.Image.actual (SourceConditionalModel.nextRead runtime))
      (SourceConditionalModel.positive runtime) +
    SourceConditionalInformationLoss.amount runtime
      (SourceWordObservedCode.readAt (inventoryBound runtime) before)
      (SourceWordFutureBit.bitWord (inventoryBound runtime + 1) after) =
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
      (SourceWordObservedCode.sourceQuery runtime (before ++ after))
      (SourceConditionalNext.Image.actual (SourceConditionalModel.nextRead runtime))
      (SourceConditionalModel.positive runtime) := by
  have beforeQuery : (fun actor : SourceConditionalModel.Actors runtime =>
      SourceWordObservedCode.readAt (inventoryBound runtime) before actor.val) =
      SourceWordObservedCode.sourceQuery runtime before := by
    funext actor
    exact (SourceWordObservedCode.source_query_read runtime before actor).symm
  have afterQuery : (fun actor : SourceConditionalModel.Actors runtime =>
      SourceWordFutureBit.bitWord (inventoryBound runtime + 1) after
        (SourceWordObservedCode.readAt (inventoryBound runtime) before actor.val)) =
      SourceWordObservedCode.sourceQuery runtime (before ++ after) := by
    funext actor
    rw [← read_at_append]
    exact (SourceWordObservedCode.source_query_read runtime (before ++ after) actor).symm
  have balance := SourceConditionalInformationLoss.information_balance runtime
    (SourceWordObservedCode.readAt (inventoryBound runtime) before)
    (SourceWordFutureBit.bitWord (inventoryBound runtime + 1) after)
  simpa only [Function.comp_apply, beforeQuery, afterQuery] using balance

theorem native_tail_no_information_loss (runtime : LivingRuntimeState process)
    (before : List (Letter (inventoryBound runtime + 1))) :
    SourceConditionalInformationLoss.amount runtime
      (SourceWordObservedCode.readAt (inventoryBound runtime) before)
      (SourceWordFutureBit.bitWord (inventoryBound runtime + 1) [.inl ()]) = 0 := by
  apply (SourceConditionalInformationLoss.amount_lossless_iff runtime _ _).mpr
  intro left right same
  change SourceWordObservedCode.readAt (inventoryBound runtime) before left.val + 1 =
    SourceWordObservedCode.readAt (inventoryBound runtime) before right.val + 1 at same
  exact add_right_cancel same

theorem actual_copy_loss_positive :
    0 < SourceConditionalInformationLoss.amount (runtimeAt 3)
      (SourceWordObservedCode.readAt 3 [])
      (SourceWordFutureBit.bitWord 4 [SourceWordDynamicNext.copyOne]) := by
  let left : SourceConditionalModel.Actors (runtimeAt 3) := ⟨0, by decide⟩
  let right : SourceConditionalModel.Actors (runtimeAt 3) := ⟨1, by decide⟩
  apply (SourceConditionalInformationLoss.amount_positive_iff_gap
    (runtimeAt 3) (SourceWordObservedCode.readAt 3 [])
    (SourceWordFutureBit.bitWord 4 [SourceWordDynamicNext.copyOne])).mpr
  apply SourceConditionalMergeLoss.gap_positive_of_collision
    (runtimeAt 3) (SourceWordObservedCode.readAt 3 [])
    (SourceWordFutureBit.bitWord 4 [SourceWordDynamicNext.copyOne]) left right
  · change SourceWordFutureBit.bitAction (inventoryBound (runtimeAt 3) + 1)
        SourceWordDynamicNext.copyOne
        (SourceWordObservedCode.readAt 3 [] left.val) =
      SourceWordFutureBit.bitAction (inventoryBound (runtimeAt 3) + 1)
        SourceWordDynamicNext.copyOne
        (SourceWordObservedCode.readAt 3 [] right.val)
    exact (SourceWordFutureBit.actual_copyOne_erases_future_bit _).trans
      (SourceWordFutureBit.actual_copyOne_erases_future_bit _).symm
  · decide

theorem actual_copy_information_strict :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound (runtimeAt 3)))
      (SourceWordObservedCode.sourceQuery (runtimeAt 3) [])
      (SourceConditionalNext.Image.actual (SourceConditionalModel.nextRead (runtimeAt 3)))
      (SourceConditionalModel.positive (runtimeAt 3)) <
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound (runtimeAt 3)))
      (SourceWordObservedCode.sourceQuery (runtimeAt 3) [SourceWordDynamicNext.copyOne])
      (SourceConditionalNext.Image.actual (SourceConditionalModel.nextRead (runtimeAt 3)))
      (SourceConditionalModel.positive (runtimeAt 3)) := by
  have tower := source_information_tower (runtimeAt 3) [] [SourceWordDynamicNext.copyOne]
  have positive := actual_copy_loss_positive
  have result := (lt_add_of_pos_right _ positive).trans_eq tower
  simpa only [List.nil_append] using result

theorem original_field_residual_tower (depth : Nat)
    (before after : List (Letter (depth + 1))) (task : Fin (depth + 1) → ℂ) :
    ‖SourceWeightedRecovery.residual (historyPMF depth)
      (fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth)
      (SourceWeightedRecovery.taskValue (historyPMF depth) task)‖ ^ 2 =
    ‖SourceWeightedRecovery.residual (historyPMF depth)
      (fieldCode depth before ∘ Actor.nextRead (depth + 1) depth)
      (SourceWeightedRecovery.taskValue (historyPMF depth) task)‖ ^ 2 +
    SourceWeightedRecovery.error (historyPMF depth)
      (fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth)
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF depth)
        (fieldCode depth before ∘ Actor.nextRead (depth + 1) depth) task
        (fieldCode depth before (Actor.nextRead (depth + 1) depth actor)))
      (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
        (fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth) task) := by
  have square :
      fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth =
        SourceWordFutureBit.bitWord (depth + 1) after ∘
          (fieldCode depth before ∘ Actor.nextRead (depth + 1) depth) := by
    funext actor
    exact original_field_action_square depth before after actor
  have gain := SourceWeightedRecovery.ObservationRefinement.optimal_gain
    (historyPMF depth)
    (fieldCode depth before ∘ Actor.nextRead (depth + 1) depth)
    (SourceWordFutureBit.bitWord (depth + 1) after) task
  rw [← square] at gain
  simpa only [SourceWeightedRecovery.optimal_attains, Function.comp_apply] using gain

private theorem actual_error_positive_of_collision
    (read : Fin 4 → ZMod 2) (task : Fin 4 → ℂ) (decoder : ZMod 2 → ℂ)
    (left right : Fin 4) (merged : read left = read right)
    (different : task left ≠ task right) :
    0 < SourceWeightedRecovery.error (historyPMF 3) read task decoder := by
  have nonnegative : 0 ≤ SourceWeightedRecovery.error (historyPMF 3) read task decoder :=
    Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  apply lt_of_le_of_ne nonnegative
  intro zero
  have all := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))).mp zero.symm
  have recovered (actor : Fin 4) : task actor = decoder (read actor) := by
    have term := all actor (Finset.mem_univ actor)
    have weight : (historyPMF 3 actor).toReal ≠ 0 := by
      rw [SourceUniformFibreVariance.source_weight]
      norm_num
    have vanish := (mul_eq_zero.mp term).resolve_left weight
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp vanish))
  apply different
  calc
    task left = decoder (read left) := recovered left
    _ = decoder (read right) := congrArg decoder merged
    _ = task right := (recovered right).symm

def actualBitValue (bit : ZMod 2) : ℂ := if bit = 0 then 0 else 1

def actualBitTask (actor : Fin 4) : ℂ :=
  actualBitValue (SourceWordObservedCode.readAt 3 [] actor.val)

theorem actual_bit_before_exact :
    ‖SourceWeightedRecovery.residual (historyPMF 3)
      (fieldCode 3 [] ∘ Actor.nextRead 4 3)
      (SourceWeightedRecovery.taskValue (historyPMF 3) actualBitTask)‖ ^ 2 = 0 := by
  have exactError : SourceWeightedRecovery.error (historyPMF 3)
      (fieldCode 3 [] ∘ Actor.nextRead 4 3) actualBitTask actualBitValue = 0 := by
    unfold SourceWeightedRecovery.error
    apply Finset.sum_eq_zero
    intro actor _
    rw [Function.comp_apply, actual_square]
    simp only [actualBitTask, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have lower := SourceWeightedRecovery.optimal_lower_bound (historyPMF 3)
    (fieldCode 3 [] ∘ Actor.nextRead 4 3) actualBitTask actualBitValue
  have nonnegative : 0 ≤ SourceWeightedRecovery.error (historyPMF 3)
      (fieldCode 3 [] ∘ Actor.nextRead 4 3) actualBitTask
      (SourceWeightedRecovery.optimalDecoder (historyPMF 3)
        (fieldCode 3 [] ∘ Actor.nextRead 4 3) actualBitTask) :=
    Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  rw [exactError] at lower
  have zero := le_antisymm lower nonnegative
  rw [SourceWeightedRecovery.optimal_attains] at zero
  exact zero

theorem actual_bit_after_strict :
    0 < ‖SourceWeightedRecovery.residual (historyPMF 3)
      (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
      (SourceWeightedRecovery.taskValue (historyPMF 3) actualBitTask)‖ ^ 2 := by
  let left : Fin 4 := ⟨0, by decide⟩
  let right : Fin 4 := ⟨1, by decide⟩
  have merged : (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3) left =
      (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3) right := by
    simp only [Function.comp_apply, actual_square]
    decide
  have different : actualBitTask left ≠ actualBitTask right := by
    have leftBit : SourceWordObservedCode.readAt 3 [] left.val = 0 := by decide
    have rightBit : SourceWordObservedCode.readAt 3 [] right.val = 1 := by decide
    simp only [actualBitTask, leftBit, rightBit, actualBitValue]
    norm_num
  have strict := actual_error_positive_of_collision
    (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
    actualBitTask
    (SourceWeightedRecovery.optimalDecoder (historyPMF 3)
      (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3) actualBitTask)
    left right merged different
  rw [SourceWeightedRecovery.optimal_attains] at strict
  exact strict

theorem actual_copy_l2_increment_strict :
    0 < SourceWeightedRecovery.error (historyPMF 3)
      (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF 3)
        (fieldCode 3 [] ∘ Actor.nextRead 4 3) actualBitTask
        (fieldCode 3 [] (Actor.nextRead 4 3 actor)))
      (SourceWeightedRecovery.optimalDecoder (historyPMF 3)
        (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3) actualBitTask) := by
  have tower := original_field_residual_tower 3 [] [SourceWordDynamicNext.copyOne] actualBitTask
  simp only [List.nil_append] at tower
  rw [actual_bit_before_exact, zero_add] at tower
  have strict := actual_bit_after_strict
  rw [tower] at strict
  exact strict

theorem empty_tail_no_l2_increment (depth : Nat)
    (before : List (Letter (depth + 1))) (task : Fin (depth + 1) → ℂ) :
    SourceWeightedRecovery.error (historyPMF depth)
      (fieldCode depth (before ++ []) ∘ Actor.nextRead (depth + 1) depth)
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF depth)
        (fieldCode depth before ∘ Actor.nextRead (depth + 1) depth) task
        (fieldCode depth before (Actor.nextRead (depth + 1) depth actor)))
      (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
        (fieldCode depth (before ++ []) ∘ Actor.nextRead (depth + 1) depth) task) = 0 := by
  simp [SourceWeightedRecovery.error, Function.comp_apply]

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
