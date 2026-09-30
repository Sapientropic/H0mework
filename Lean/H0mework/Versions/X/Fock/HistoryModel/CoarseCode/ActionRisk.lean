import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionLoss
import H0mework.Versions.X.Fock.InverseDistribution.Stale.Source

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

private theorem observed_query_is_original_field (runtime : LivingRuntimeState process)
    (word : List (Letter (inventoryBound runtime + 1))) :
    SourceWordCodeRisk.query runtime word
      (SourceWordObservedCode.encodeObserved runtime word) =
      fieldCode (inventoryBound runtime) word ∘
        Actor.nextRead (inventoryBound runtime + 1) (inventoryBound runtime) := by
  funext actor
  rw [SourceWordObservedCode.query_actual, Function.comp_apply, actual_square]
  exact SourceWordObservedCode.source_query_read runtime word actor

/-- The original acted G risk pays the new scalar recovery loss on the same
    source word and Field actor support. The physical effect and decoder deviation
    remain at the post-action occurrence. -/
theorem original_acted_g_risk_tower (runtime : LivingRuntimeState process)
    (before after : List (Letter (inventoryBound runtime + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    let depth := inventoryBound runtime
    let beforeRead := fieldCode depth before ∘ Actor.nextRead (depth + 1) depth
    let afterRead := fieldCode depth (before ++ after) ∘ Actor.nextRead (depth + 1) depth
    let clockTask := SourceJointClockGraph.clock ∘ SourceConditionalInventory.values depth
    SourceWordCodeRisk.risk runtime (before ++ after)
      (SourceWordObservedCode.encodeObserved runtime (before ++ after)) decoder =
      SourceConditionalInventory.cost depth afterRead / (depth + 1 : ℝ) +
      ((SourceCopyWordAffine.compile
        ((before ++ after).map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        (‖SourceWeightedRecovery.residual (historyPMF depth) beforeRead
          (SourceWeightedRecovery.taskValue (historyPMF depth) clockTask)‖ ^ 2 +
          SourceWeightedRecovery.error (historyPMF depth) afterRead
            (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF depth)
              beforeRead clockTask (beforeRead actor))
            (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
              afterRead clockTask)) +
      ∑ actor : SourceConditionalModel.Actors runtime,
        (historyPMF depth actor).toReal *
          ‖SourceCompiledGWord.effect (depth + 1) (before ++ after)
            (SourceVectorMoment.mean
              (SourceConditionalHistory.conditional (historyPMF depth)
                afterRead (afterRead actor)
                (SourceWeightedRecovery.observed_supported _ _ actor
                  (SourceUniformFibreVariance.source_positive _ actor)))
              (SourceConditionalInventory.values depth)) -
            decoder (afterRead actor)‖ ^ 2 := by
  dsimp only
  have account := SourceWordCodeRisk.risk_account runtime (before ++ after)
    (SourceWordObservedCode.encodeObserved runtime (before ++ after)) decoder
  rw [observed_query_is_original_field runtime (before ++ after)] at account
  have tower := original_field_residual_tower (inventoryBound runtime) before after
    (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values (inventoryBound runtime))
  rw [tower] at account
  simpa only [Function.comp_apply] using account

private theorem actual_clock_task_value (actor : Fin 4) :
    (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3) actor =
      (((actor.val + 2 : Nat) : ℝ) : ℂ) := by
  rw [Function.comp_apply, SourceInverseDistributionStale.actor_clock]
  norm_num

private theorem actual_before_clock_fibre_zero :
    SourceUniformFibreVariance.fibre 3
      (fieldCode 3 [] ∘ Actor.nextRead 4 3) (0 : ZMod 2) =
        {⟨0, by decide⟩, ⟨2, by decide⟩} := by
  ext actor
  simp only [SourceUniformFibreVariance.fibre_mem, Function.comp_apply, actual_square]
  fin_cases actor <;> decide

private theorem actual_before_clock_fibre_one :
    SourceUniformFibreVariance.fibre 3
      (fieldCode 3 [] ∘ Actor.nextRead 4 3) (1 : ZMod 2) =
        {⟨1, by decide⟩, ⟨3, by decide⟩} := by
  ext actor
  simp only [SourceUniformFibreVariance.fibre_mem, Function.comp_apply, actual_square]
  fin_cases actor <;> decide

private theorem actual_before_clock_decoder_zero :
    SourceWeightedRecovery.optimalDecoder (historyPMF 3)
      (fieldCode 3 [] ∘ Actor.nextRead 4 3)
      (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3) 0 = 3 := by
  have supported : (0 : ZMod 2) ∈ ((historyPMF 3).map
      (fieldCode 3 [] ∘ Actor.nextRead 4 3)).support := by
    apply SourceUniformFibreVariance.output_supported
    apply Finset.mem_image.mpr
    refine ⟨⟨0, by decide⟩, Finset.mem_univ _, ?_⟩
    rw [Function.comp_apply, actual_square]
    decide
  have taskEq : (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3) =
      (fun actor : Fin 4 => (((actor.val + 2 : Nat) : ℝ) : ℂ)) := by
    funext actor
    exact actual_clock_task_value actor
  rw [taskEq, SourceUniformFibreVariance.optimalDecoder_fibre_mean
    3 (fieldCode 3 [] ∘ Actor.nextRead 4 3)
    (fun actor : Fin 4 => ((actor.val + 2 : Nat) : ℝ)) 0 supported,
    actual_before_clock_fibre_zero]
  norm_num

private theorem actual_before_clock_decoder_one :
    SourceWeightedRecovery.optimalDecoder (historyPMF 3)
      (fieldCode 3 [] ∘ Actor.nextRead 4 3)
      (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3) 1 = 4 := by
  have supported : (1 : ZMod 2) ∈ ((historyPMF 3).map
      (fieldCode 3 [] ∘ Actor.nextRead 4 3)).support := by
    apply SourceUniformFibreVariance.output_supported
    apply Finset.mem_image.mpr
    refine ⟨⟨1, by decide⟩, Finset.mem_univ _, ?_⟩
    rw [Function.comp_apply, actual_square]
    decide
  have taskEq : (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3) =
      (fun actor : Fin 4 => (((actor.val + 2 : Nat) : ℝ) : ℂ)) := by
    funext actor
    exact actual_clock_task_value actor
  rw [taskEq, SourceUniformFibreVariance.optimalDecoder_fibre_mean
    3 (fieldCode 3 [] ∘ Actor.nextRead 4 3)
    (fun actor : Fin 4 => ((actor.val + 2 : Nat) : ℝ)) 1 supported,
    actual_before_clock_fibre_one]
  norm_num

private theorem actual_after_clock_read_constant (actor : Fin 4) :
    (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3) actor = 0 := by
  rw [Function.comp_apply, actual_square]
  have action := read_at_append 3 [] [SourceWordDynamicNext.copyOne] actor.val
  change SourceWordObservedCode.readAt 3 [SourceWordDynamicNext.copyOne] actor.val =
    SourceWordFutureBit.bitAction 4 SourceWordDynamicNext.copyOne
      (SourceWordObservedCode.readAt 3 [] actor.val) at action
  have erased (bit : ZMod 2) :
      SourceWordFutureBit.bitAction 4 SourceWordDynamicNext.copyOne bit = 0 := by
    fin_cases bit <;> decide
  rw [erased] at action
  exact action

private theorem actual_after_clock_fibre_zero :
    SourceUniformFibreVariance.fibre 3
      (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
      (0 : ZMod 2) = Finset.univ := by
  ext actor
  simp only [SourceUniformFibreVariance.fibre_mem, actual_after_clock_read_constant,
    Finset.mem_univ]

private theorem actual_after_clock_decoder_zero :
    SourceWeightedRecovery.optimalDecoder (historyPMF 3)
      (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
      (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3) 0 = 7 / 2 := by
  have supported : (0 : ZMod 2) ∈ ((historyPMF 3).map
      (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)).support := by
    apply SourceUniformFibreVariance.output_supported
    apply Finset.mem_image.mpr
    refine ⟨⟨0, by decide⟩, Finset.mem_univ _, ?_⟩
    exact actual_after_clock_read_constant _
  have taskEq : (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3) =
      (fun actor : Fin 4 => (((actor.val + 2 : Nat) : ℝ) : ℂ)) := by
    funext actor
    exact actual_clock_task_value actor
  rw [taskEq, SourceUniformFibreVariance.optimalDecoder_fibre_mean
    3 (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
    (fun actor : Fin 4 => ((actor.val + 2 : Nat) : ℝ)) 0 supported,
    actual_after_clock_fibre_zero]
  norm_num [Fin.sum_univ_succ]

/-- The original clock task, on the actual four-actor source and copy action,
    pays a new quarter-unit of scalar L² error. -/
theorem actual_copy_clock_l2_increment :
    SourceWeightedRecovery.error (historyPMF 3)
      (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF 3)
        (fieldCode 3 [] ∘ Actor.nextRead 4 3)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3)
        (fieldCode 3 [] (Actor.nextRead 4 3 actor)))
      (SourceWeightedRecovery.optimalDecoder (historyPMF 3)
        (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3)) = 1 / 4 := by
  unfold SourceWeightedRecovery.error
  simp only [actual_after_clock_read_constant, actual_after_clock_decoder_zero,
    SourceUniformFibreVariance.source_weight, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero, actual_square]
  norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd]
  have read0 : SourceWordObservedCode.readAt 3 [] 0 = 0 := by decide
  have read1 : SourceWordObservedCode.readAt 3 [] 1 = 1 := by decide
  have read2 : SourceWordObservedCode.readAt 3 [] 2 = 0 := by decide
  have read3 : SourceWordObservedCode.readAt 3 [] 3 = 1 := by decide
  rw [read0, read1, read2, read3, actual_before_clock_decoder_zero,
    actual_before_clock_decoder_one]
  norm_num

theorem actual_copy_clock_l2_increment_positive :
    0 < SourceWeightedRecovery.error (historyPMF 3)
      (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF 3)
        (fieldCode 3 [] ∘ Actor.nextRead 4 3)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3)
        (fieldCode 3 [] (Actor.nextRead 4 3 actor)))
      (SourceWeightedRecovery.optimalDecoder (historyPMF 3)
        (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3)) := by
  rw [actual_copy_clock_l2_increment]
  norm_num

/-- The executed copy's original G risk pays the clock task's exact new
    quarter-unit loss, amplified by its source-compiled physical slope. -/
theorem actual_copy_original_g_risk_account
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    let depth := inventoryBound (runtimeAt 3)
    let beforeRead := fieldCode depth [] ∘ Actor.nextRead (depth + 1) depth
    let afterRead := fieldCode depth [SourceWordDynamicNext.copyOne] ∘
      Actor.nextRead (depth + 1) depth
    let clockTask := SourceJointClockGraph.clock ∘ SourceConditionalInventory.values depth
    SourceWordCodeRisk.risk (runtimeAt 3) [SourceWordDynamicNext.copyOne]
      (SourceWordObservedCode.encodeObserved (runtimeAt 3)
        [SourceWordDynamicNext.copyOne]) decoder =
      SourceConditionalInventory.cost depth afterRead / (depth + 1 : ℝ) +
      ((SourceCopyWordAffine.compile
        ([SourceWordDynamicNext.copyOne].map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        (‖SourceWeightedRecovery.residual (historyPMF depth) beforeRead
          (SourceWeightedRecovery.taskValue (historyPMF depth) clockTask)‖ ^ 2 + 1 / 4) +
      ∑ actor : SourceConditionalModel.Actors (runtimeAt 3),
        (historyPMF depth actor).toReal *
          ‖SourceCompiledGWord.effect (depth + 1) [SourceWordDynamicNext.copyOne]
            (SourceVectorMoment.mean
              (SourceConditionalHistory.conditional (historyPMF depth)
                afterRead (afterRead actor)
                (SourceWeightedRecovery.observed_supported _ _ actor
                  (SourceUniformFibreVariance.source_positive _ actor)))
              (SourceConditionalInventory.values depth)) -
            decoder (afterRead actor)‖ ^ 2 := by
  dsimp only
  have paid := original_acted_g_risk_tower (runtimeAt 3) []
    [SourceWordDynamicNext.copyOne] decoder
  dsimp only at paid
  simp only [List.nil_append] at paid
  have increment :
      SourceWeightedRecovery.error (historyPMF (inventoryBound (runtimeAt 3)))
        (fieldCode (inventoryBound (runtimeAt 3)) [SourceWordDynamicNext.copyOne] ∘
          Actor.nextRead (inventoryBound (runtimeAt 3) + 1) (inventoryBound (runtimeAt 3)))
        (fun actor => SourceWeightedRecovery.optimalDecoder
          (historyPMF (inventoryBound (runtimeAt 3)))
          (fieldCode (inventoryBound (runtimeAt 3)) [] ∘
            Actor.nextRead (inventoryBound (runtimeAt 3) + 1) (inventoryBound (runtimeAt 3)))
          (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
            (inventoryBound (runtimeAt 3)))
          (fieldCode (inventoryBound (runtimeAt 3)) []
            (Actor.nextRead (inventoryBound (runtimeAt 3) + 1)
              (inventoryBound (runtimeAt 3)) actor)))
        (SourceWeightedRecovery.optimalDecoder
          (historyPMF (inventoryBound (runtimeAt 3)))
          (fieldCode (inventoryBound (runtimeAt 3)) [SourceWordDynamicNext.copyOne] ∘
            Actor.nextRead (inventoryBound (runtimeAt 3) + 1) (inventoryBound (runtimeAt 3)))
          (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
            (inventoryBound (runtimeAt 3)))) = 1 / 4 := by
    change SourceWeightedRecovery.error (historyPMF 3)
      (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
      (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF 3)
        (fieldCode 3 [] ∘ Actor.nextRead 4 3)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3)
        (fieldCode 3 [] (Actor.nextRead 4 3 actor)))
      (SourceWeightedRecovery.optimalDecoder (historyPMF 3)
        (fieldCode 3 [SourceWordDynamicNext.copyOne] ∘ Actor.nextRead 4 3)
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3)) = 1 / 4
    exact actual_copy_clock_l2_increment
  simp only [Function.comp_apply] at paid
  rw [increment] at paid
  simpa only [Function.comp_apply] using paid

theorem actual_copy_original_g_risk_at_least_one
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    1 ≤ SourceWordCodeRisk.risk (runtimeAt 3) [SourceWordDynamicNext.copyOne]
      (SourceWordObservedCode.encodeObserved (runtimeAt 3)
        [SourceWordDynamicNext.copyOne]) decoder := by
  let depth := inventoryBound (runtimeAt 3)
  let beforeRead := fieldCode depth [] ∘ Actor.nextRead (depth + 1) depth
  let afterRead := fieldCode depth [SourceWordDynamicNext.copyOne] ∘
    Actor.nextRead (depth + 1) depth
  let clockTask := SourceJointClockGraph.clock ∘ SourceConditionalInventory.values depth
  have account := actual_copy_original_g_risk_account decoder
  dsimp only at account
  have costNonneg : 0 ≤ SourceConditionalInventory.cost depth afterRead := by
    unfold SourceConditionalInventory.cost
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have costPartNonneg : 0 ≤ SourceConditionalInventory.cost depth afterRead /
      (depth + 1 : ℝ) := div_nonneg costNonneg (by positivity)
  have beforeNonneg : 0 ≤ ‖SourceWeightedRecovery.residual (historyPMF depth) beforeRead
      (SourceWeightedRecovery.taskValue (historyPMF depth) clockTask)‖ ^ 2 := sq_nonneg _
  have deviationNonneg : 0 ≤ ∑ actor : SourceConditionalModel.Actors (runtimeAt 3),
      (historyPMF depth actor).toReal *
        ‖SourceCompiledGWord.effect (depth + 1) [SourceWordDynamicNext.copyOne]
          (SourceVectorMoment.mean
            (SourceConditionalHistory.conditional (historyPMF depth)
              afterRead (afterRead actor)
              (SourceWeightedRecovery.observed_supported _ _ actor
                (SourceUniformFibreVariance.source_positive _ actor)))
            (SourceConditionalInventory.values depth)) - decoder (afterRead actor)‖ ^ 2 := by
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  have slopeNat : (SourceCopyWordAffine.compile
      ([SourceWordDynamicNext.copyOne].map SourceCopyNativeWord.encode)).1 = 2 := by decide
  have slopeSq : ((SourceCopyWordAffine.compile
      ([SourceWordDynamicNext.copyOne].map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 = 4 := by
    rw [slopeNat]
    norm_num
  rw [slopeSq] at account
  nlinarith

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
