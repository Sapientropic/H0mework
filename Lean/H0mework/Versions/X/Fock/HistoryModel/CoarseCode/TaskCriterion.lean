import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionLoss

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

/-- A task pays no additional error on an actual source word exactly when its
    old conditional mean is constant on each new observed fibre. -/
theorem original_task_increment_zero_iff (depth : Nat)
    (before after : List (Letter (depth + 1))) (task : Fin (depth + 1) → ℂ) :
    SourceWeightedRecovery.error (historyPMF depth)
      (fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth)
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF depth)
        (fieldCode depth before ∘ Actor.nextRead (depth + 1) depth) task
        (fieldCode depth before (Actor.nextRead (depth + 1) depth actor)))
      (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
        (fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth) task) = 0 ↔
    ∀ actor : Fin (depth + 1),
      SourceWeightedRecovery.optimalDecoder (historyPMF depth)
        (fieldCode depth before ∘ Actor.nextRead (depth + 1) depth) task
        (fieldCode depth before (Actor.nextRead (depth + 1) depth actor)) =
      SourceWeightedRecovery.optimalDecoder (historyPMF depth)
        (fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth) task
        (fieldCode depth (before ++ after) (Actor.nextRead (depth + 1) depth actor)) := by
  have positive (actor : Fin (depth + 1)) : (historyPMF depth actor).toReal ≠ 0 := by
    rw [SourceUniformFibreVariance.source_weight]
    positivity
  simpa only [Function.comp_apply] using
    (SourceWeightedRecovery.ObservationRefinement.error_zero_iff_of_positive
      (source := historyPMF depth)
      (read := fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth)
      positive
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF depth)
        (fieldCode depth before ∘ Actor.nextRead (depth + 1) depth) task
        (fieldCode depth before (Actor.nextRead (depth + 1) depth actor)))
      (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
        (fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth) task))

/-- The complete original unit-task inventory detects precisely the source
    distinctions erased by the actual appended word. -/
theorem all_original_unit_increments_zero_iff (depth : Nat)
    (before after : List (Letter (depth + 1))) :
    let oldRead := fieldCode depth before ∘ Actor.nextRead (depth + 1) depth
    let newRead := fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth
    (∀ index : Fin (depth + 1),
      SourceWeightedRecovery.error (historyPMF depth) newRead
        (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF depth) oldRead
          (fun point => (SourceConditionalInventory.unitTask depth index point : ℂ))
          (oldRead actor))
        (SourceWeightedRecovery.optimalDecoder (historyPMF depth) newRead
          (fun point => (SourceConditionalInventory.unitTask depth index point : ℂ))) = 0) ↔
      ∀ left right : Fin (depth + 1), newRead left = newRead right → oldRead left = oldRead right := by
  dsimp only
  let oldRead := fieldCode depth before ∘ Actor.nextRead (depth + 1) depth
  let newRead := fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth
  let forget := SourceWordFutureBit.bitWord (depth + 1) after
  have square : newRead = forget ∘ oldRead := by
    funext actor
    exact original_field_action_square depth before after actor
  constructor
  · intro all left right merged
    have costEq : SourceConditionalInventory.cost depth newRead =
        SourceConditionalInventory.cost depth oldRead := by
      unfold SourceConditionalInventory.cost
      apply Finset.sum_congr rfl
      intro index _
      have tower := original_field_residual_tower depth before after
        (fun point => (SourceConditionalInventory.unitTask depth index point : ℂ))
      have zero : SourceWeightedRecovery.error (historyPMF depth)
          (fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth)
          (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF depth)
            (fieldCode depth before ∘ Actor.nextRead (depth + 1) depth)
            (fun point => (SourceConditionalInventory.unitTask depth index point : ℂ))
            (fieldCode depth before (Actor.nextRead (depth + 1) depth actor)))
          (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
            (fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth)
            (fun point => (SourceConditionalInventory.unitTask depth index point : ℂ))) = 0 := by
        simpa only [oldRead, newRead, Function.comp_apply] using all index
      rw [zero, add_zero] at tower
      simpa only [oldRead, newRead] using tower
    have cardEq : (SourceUniformFibreVariance.outputs depth newRead).card =
        (SourceUniformFibreVariance.outputs depth oldRead).card := by
      rw [SourceConditionalInventory.cost_eq, SourceConditionalInventory.cost_eq] at costEq
      have realEq : ((SourceUniformFibreVariance.outputs depth newRead).card : ℝ) =
          ((SourceUniformFibreVariance.outputs depth oldRead).card : ℝ) := by
        linarith
      exact_mod_cast realEq
    have outputSquare : SourceUniformFibreVariance.outputs depth newRead =
        (SourceUniformFibreVariance.outputs depth oldRead).image forget := by
      simp only [SourceUniformFibreVariance.outputs, square, Finset.image_image]
    have injectiveOn : Set.InjOn forget
        (SourceUniformFibreVariance.outputs depth oldRead) :=
      Finset.card_image_iff.mp (by rw [← outputSquare]; exact cardEq)
    apply injectiveOn
    · exact Finset.mem_image.mpr ⟨left, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨right, Finset.mem_univ _, rfl⟩
    · change newRead left = newRead right at merged
      rw [square] at merged
      exact merged
  · intro faithful index
    apply (original_task_increment_zero_iff depth before after
      (fun point => (SourceConditionalInventory.unitTask depth index point : ℂ))).mpr
    intro actor
    let task : Fin (depth + 1) → ℂ :=
      fun point => (SourceConditionalInventory.unitTask depth index point : ℂ)
    have oldSupported := SourceWeightedRecovery.observed_supported
      (historyPMF depth) oldRead actor (SourceUniformFibreVariance.source_positive depth actor)
    have newSupported := SourceWeightedRecovery.observed_supported
      (historyPMF depth) newRead actor (SourceUniformFibreVariance.source_positive depth actor)
    have sameFibre (point : Fin (depth + 1)) :
        oldRead point = oldRead actor ↔ newRead point = newRead actor := by
      constructor
      · intro same
        rw [square]
        exact congrArg forget same
      · exact fun same => faithful point actor same
    have posterior := SourceConditionalHistory.conditional_eq_of_fibre
      (historyPMF depth) oldRead newRead (oldRead actor) (newRead actor)
      oldSupported newSupported sameFibre
    have means : SourceWeightedRecovery.optimalDecoder (historyPMF depth) oldRead task
        (oldRead actor) =
        SourceWeightedRecovery.optimalDecoder (historyPMF depth) newRead task
          (newRead actor) := by
      rw [SourceWeightedRecovery.optimal_is_conditional _ _ task _ oldSupported,
        SourceWeightedRecovery.optimal_is_conditional _ _ task _ newSupported]
      unfold SourceWeightedRecovery.conditionalMean
      rw [posterior]
    simpa only [oldRead, newRead, task, Function.comp_apply] using means

theorem all_original_unit_increments_zero_iff_information_loss_zero
    (runtime : LivingRuntimeState process)
    (before after : List (Letter (inventoryBound runtime + 1))) :
    let depth := inventoryBound runtime
    let oldRead := fieldCode depth before ∘ Actor.nextRead (depth + 1) depth
    let newRead := fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth
    (∀ index : Fin (depth + 1),
      SourceWeightedRecovery.error (historyPMF depth) newRead
        (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF depth) oldRead
          (fun point => (SourceConditionalInventory.unitTask depth index point : ℂ))
          (oldRead actor))
        (SourceWeightedRecovery.optimalDecoder (historyPMF depth) newRead
          (fun point => (SourceConditionalInventory.unitTask depth index point : ℂ))) = 0) ↔
      SourceConditionalInformationLoss.amount runtime
        (SourceWordObservedCode.readAt depth before)
        (SourceWordFutureBit.bitWord (depth + 1) after) = 0 := by
  dsimp only
  have criterion := all_original_unit_increments_zero_iff
    (inventoryBound runtime) before after
  dsimp only at criterion
  rw [criterion, SourceConditionalInformationLoss.amount_lossless_iff]
  simp only [Function.comp_apply, actual_square, read_at_append]

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
