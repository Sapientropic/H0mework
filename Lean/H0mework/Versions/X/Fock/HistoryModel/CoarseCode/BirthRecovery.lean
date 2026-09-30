import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.NativeBirth
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionRisk

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

attribute [local instance] fieldUniformSpace fieldMeasurable fieldBorelSpace fieldT2

private theorem birth_before_read (actor : Fin 5) :
    (fieldCode 4 (SourceWordFutureBitGrowth.nextWordAt 3 []) ∘ Actor.nextRead 5 4) actor =
      SourceWordObservedCode.readAt 3 [] actor.val := by
  have square := actual_square (inventoryBound (runtimeAt 4))
    (SourceWordFutureBitGrowth.nextWordAt 3 []) actor
  have transport := SourceWordFutureBitGrowth.old_next_read_at 3 [] actor.val
  exact square.trans transport

private theorem birth_after_read (actor : Fin 5) :
    (fieldCode 4
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) ∘
        Actor.nextRead 5 4) actor = 0 := by
  have square := actual_square (inventoryBound (runtimeAt 4))
    (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) actor
  have transport := SourceWordFutureBitGrowth.old_next_read_at 3
    [SourceWordDynamicNext.copyOne] actor.val
  have action := read_at_append 3 [] [SourceWordDynamicNext.copyOne] actor.val
  change SourceWordObservedCode.readAt 3 [SourceWordDynamicNext.copyOne] actor.val =
    SourceWordFutureBit.bitAction 4 SourceWordDynamicNext.copyOne
      (SourceWordObservedCode.readAt 3 [] actor.val) at action
  exact square.trans (transport.trans
    (action.trans (SourceWordFutureBit.actual_copyOne_erases_future_bit _)))

private theorem birth_clock_task_value (actor : Fin 5) :
    (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4) actor =
      (((actor.val + 2 : Nat) : ℝ) : ℂ) := by
  rw [Function.comp_apply, SourceInverseDistributionStale.actor_clock]
  norm_num

private def birthBeforeRead : Fin 5 → ZMod 2 :=
  fieldCode 4 (SourceWordFutureBitGrowth.nextWordAt 3 []) ∘ Actor.nextRead 5 4

private def birthAfterRead : Fin 5 → ZMod 2 :=
  fieldCode 4 (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) ∘
    Actor.nextRead 5 4

private theorem birth_before_fibre_zero :
    SourceUniformFibreVariance.fibre 4 birthBeforeRead (0 : ZMod 2) =
      {⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩} := by
  ext actor
  simp only [SourceUniformFibreVariance.fibre_mem, birthBeforeRead, birth_before_read]
  fin_cases actor <;> decide

private theorem birth_before_fibre_one :
    SourceUniformFibreVariance.fibre 4 birthBeforeRead (1 : ZMod 2) =
      {⟨1, by decide⟩, ⟨3, by decide⟩} := by
  ext actor
  simp only [SourceUniformFibreVariance.fibre_mem, birthBeforeRead, birth_before_read]
  fin_cases actor <;> decide

private theorem birth_after_fibre_zero :
    SourceUniformFibreVariance.fibre 4 birthAfterRead (0 : ZMod 2) = Finset.univ := by
  ext actor
  simp only [SourceUniformFibreVariance.fibre_mem, birthAfterRead, birth_after_read,
    Finset.mem_univ]

private theorem birth_clock_decoder_before_zero :
    SourceWeightedRecovery.optimalDecoder (historyPMF 4) birthBeforeRead
      (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4) 0 = 4 := by
  have supported : (0 : ZMod 2) ∈ ((historyPMF 4).map birthBeforeRead).support := by
    apply SourceUniformFibreVariance.output_supported
    apply Finset.mem_image.mpr
    refine ⟨⟨0, by decide⟩, Finset.mem_univ _, ?_⟩
    simpa only [birthBeforeRead, birth_before_read] using
      (show SourceWordObservedCode.readAt 3 [] 0 = 0 by decide)
  have taskEq : (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4) =
      (fun actor : Fin 5 => (((actor.val + 2 : Nat) : ℝ) : ℂ)) := by
    funext actor
    exact birth_clock_task_value actor
  rw [taskEq, SourceUniformFibreVariance.optimalDecoder_fibre_mean
    4 birthBeforeRead (fun actor : Fin 5 => ((actor.val + 2 : Nat) : ℝ)) 0 supported,
    birth_before_fibre_zero]
  norm_num

private theorem birth_clock_decoder_before_one :
    SourceWeightedRecovery.optimalDecoder (historyPMF 4) birthBeforeRead
      (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4) 1 = 4 := by
  have supported : (1 : ZMod 2) ∈ ((historyPMF 4).map birthBeforeRead).support := by
    apply SourceUniformFibreVariance.output_supported
    apply Finset.mem_image.mpr
    refine ⟨⟨1, by decide⟩, Finset.mem_univ _, ?_⟩
    simpa only [birthBeforeRead, birth_before_read] using
      (show SourceWordObservedCode.readAt 3 [] 1 = 1 by decide)
  have taskEq : (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4) =
      (fun actor : Fin 5 => (((actor.val + 2 : Nat) : ℝ) : ℂ)) := by
    funext actor
    exact birth_clock_task_value actor
  rw [taskEq, SourceUniformFibreVariance.optimalDecoder_fibre_mean
    4 birthBeforeRead (fun actor : Fin 5 => ((actor.val + 2 : Nat) : ℝ)) 1 supported,
    birth_before_fibre_one]
  norm_num

private theorem birth_clock_decoder_after_zero :
    SourceWeightedRecovery.optimalDecoder (historyPMF 4) birthAfterRead
      (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4) 0 = 4 := by
  have supported : (0 : ZMod 2) ∈ ((historyPMF 4).map birthAfterRead).support := by
    apply SourceUniformFibreVariance.output_supported
    apply Finset.mem_image.mpr
    refine ⟨⟨0, by decide⟩, Finset.mem_univ _, ?_⟩
    exact birth_after_read _
  have taskEq : (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4) =
      (fun actor : Fin 5 => (((actor.val + 2 : Nat) : ℝ) : ℂ)) := by
    funext actor
    exact birth_clock_task_value actor
  rw [taskEq, SourceUniformFibreVariance.optimalDecoder_fibre_mean
    4 birthAfterRead (fun actor : Fin 5 => ((actor.val + 2 : Nat) : ℝ)) 0 supported,
    birth_after_fibre_zero]
  norm_num [Fin.sum_univ_succ]

private theorem birth_clock_decoder_before_any (bit : ZMod 2) :
    SourceWeightedRecovery.optimalDecoder (historyPMF 4) birthBeforeRead
      (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4) bit = 4 := by
  fin_cases bit
  · exact birth_clock_decoder_before_zero
  · exact birth_clock_decoder_before_one

/-- On the exact d3→d4 source birth, the transported old word and its copy
    have the same optimal decoder for the original clock task. -/
theorem actual_birth_copy_clock_l2_increment_zero :
    let beforeRead := fieldCode 4 (SourceWordFutureBitGrowth.nextWordAt 3 []) ∘
      Actor.nextRead 5 4
    let afterRead := fieldCode 4
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) ∘
      Actor.nextRead 5 4
    SourceWeightedRecovery.error (historyPMF 4) afterRead
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF 4) beforeRead
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4)
        (beforeRead actor))
      (SourceWeightedRecovery.optimalDecoder (historyPMF 4) afterRead
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4)) = 0 := by
  dsimp only
  change SourceWeightedRecovery.error (historyPMF 4) birthAfterRead
    (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF 4) birthBeforeRead
      (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4)
      (birthBeforeRead actor))
    (SourceWeightedRecovery.optimalDecoder (historyPMF 4) birthAfterRead
      (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4)) = 0
  unfold SourceWeightedRecovery.error
  apply Finset.sum_eq_zero
  intro actor _
  have afterZero : birthAfterRead actor = 0 := birth_after_read actor
  have beforeFour := birth_clock_decoder_before_any (birthBeforeRead actor)
  simp only [afterZero, beforeFour, birth_clock_decoder_after_zero,
    sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]

/-- The same native birth retains a strict information loss for the actual
    transported source word, despite the zero new clock recovery error. -/
theorem actual_birth_copy_information_amount_positive :
    0 < SourceConditionalInformationLoss.amount (runtimeAt 4)
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
        (SourceWordFutureBitGrowth.nextWordAt 3 []))
      (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])) := by
  have account := actual_copy_native_birth_information_loss
  dsimp only at account
  have oldPositive : 0 < SourceConditionalInformationLoss.amount (runtimeAt 3)
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
        (SourceWordFutureBitGrowth.oldWordAt 3 []))
      (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 3) + 1)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])) := by
    exact actual_copy_loss_positive
  have correction := actual_copy_birth_correction_positive
  nlinarith

theorem actual_birth_copy_full_model_gap_positive :
    0 < SourceConditionalMergeLoss.gap (runtimeAt 4)
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
        (SourceWordFutureBitGrowth.nextWordAt 3 []))
      (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])) :=
  (SourceConditionalInformationLoss.amount_positive_iff_gap _ _ _).mp
    actual_birth_copy_information_amount_positive

/-- The existing original Field residual tower consumes the executed birth
    word. For the original clock coordinate, copy changes no optimal L² residual
    at this new occurrence. -/
theorem actual_birth_copy_clock_residual_unchanged :
    let beforeRead := fieldCode 4 (SourceWordFutureBitGrowth.nextWordAt 3 []) ∘
      Actor.nextRead 5 4
    let afterRead := fieldCode 4
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) ∘
      Actor.nextRead 5 4
    ‖SourceWeightedRecovery.residual (historyPMF 4) afterRead
      (SourceWeightedRecovery.taskValue (historyPMF 4)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4))‖ ^ 2 =
      ‖SourceWeightedRecovery.residual (historyPMF 4) beforeRead
        (SourceWeightedRecovery.taskValue (historyPMF 4)
          (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4))‖ ^ 2 := by
  dsimp only
  change ‖SourceWeightedRecovery.residual (historyPMF 4) birthAfterRead
      (SourceWeightedRecovery.taskValue (historyPMF 4)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4))‖ ^ 2 =
    ‖SourceWeightedRecovery.residual (historyPMF 4) birthBeforeRead
      (SourceWeightedRecovery.taskValue (historyPMF 4)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4))‖ ^ 2
  have tower := original_field_residual_tower 4 []
    (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
    (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4)
  change ‖SourceWeightedRecovery.residual (historyPMF 4) birthAfterRead
      (SourceWeightedRecovery.taskValue (historyPMF 4)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4))‖ ^ 2 =
    ‖SourceWeightedRecovery.residual (historyPMF 4) birthBeforeRead
      (SourceWeightedRecovery.taskValue (historyPMF 4)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4))‖ ^ 2 +
    SourceWeightedRecovery.error (historyPMF 4) birthAfterRead
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF 4) birthBeforeRead
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4)
        (birthBeforeRead actor))
      (SourceWeightedRecovery.optimalDecoder (historyPMF 4) birthAfterRead
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4)) at tower
  have zero : SourceWeightedRecovery.error (historyPMF 4) birthAfterRead
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF 4) birthBeforeRead
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4)
        (birthBeforeRead actor))
      (SourceWeightedRecovery.optimalDecoder (historyPMF 4) birthAfterRead
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4)) = 0 :=
    actual_birth_copy_clock_l2_increment_zero
  rw [zero, add_zero] at tower
  exact tower

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
