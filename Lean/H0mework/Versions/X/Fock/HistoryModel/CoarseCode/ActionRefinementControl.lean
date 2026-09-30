import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.OptimalRiskControl.Old
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionRefinement

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem actual_copy_before_query (actor : Fin 5) :
    SourceWordObservedCode.sourceQuery (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 []) actor = (actor.val : ZMod 2) := by
  calc
    _ = SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
          (SourceWordFutureBitGrowth.nextWordAt 3 []) actor.val :=
      SourceWordObservedCode.source_query_read _ _ _
    _ = SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
          (SourceWordFutureBitGrowth.oldWordAt 3 []) actor.val :=
      SourceWordFutureBitGrowth.old_next_read_at _ _ _
    _ = SourceWordObservedCode.readAt 3 [] actor.val :=
      SourceWordFutureBitGrowth.transport_read_at _ _ _
    _ = (actor.val : ZMod 2) := by
      fin_cases actor <;> decide

theorem actual_copy_before_cost :
    SourceConditionalInventory.cost 4
      (SourceWordObservedCode.sourceQuery (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [])) = 3 := by
  have query : SourceWordObservedCode.sourceQuery (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 []) =
      (fun actor : Fin 5 => (actor.val : ZMod 2)) := by
    funext actor
    exact actual_copy_before_query actor
  have surjective : Function.Surjective (fun actor : Fin 5 => (actor.val : ZMod 2)) := by
    intro value
    fin_cases value
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  calc
    _ = (4 + 1 : ℝ) -
        (SourceUniformFibreVariance.outputs 4
          (SourceWordObservedCode.sourceQuery (runtimeAt 4)
            (SourceWordFutureBitGrowth.nextWordAt 3 []))).card :=
      SourceConditionalInventory.cost_eq _ _
    _ = 3 := by
      rw [query]
      rw [SourceUniformFibreVariance.outputs,
        Finset.image_univ_of_surjective surjective]
      norm_num

theorem gGap_cost_residual_account {Fine Coarse : Type*}
    [DecidableEq Fine] [DecidableEq Coarse]
    [MeasurableSpace Fine] [MeasurableSingletonClass Fine]
    [MeasurableSpace Coarse] [MeasurableSingletonClass Coarse]
    (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1)))
    (read : Nat → Fine) (forget : Fine → Coarse) :
    gGap runtime taskWord read forget =
      (SourceConditionalInventory.cost (inventoryBound runtime)
        (fun actor : SourceConditionalModel.Actors runtime => (forget ∘ read) actor.val) /
          (inventoryBound runtime + 1 : ℝ) +
        ((SourceCopyWordAffine.compile
          (taskWord.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
          ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime))
            (fun actor : SourceConditionalModel.Actors runtime => (forget ∘ read) actor.val)
            (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime))
              (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
                (inventoryBound runtime)))‖ ^ 2) -
      (SourceConditionalInventory.cost (inventoryBound runtime)
        (fun actor : SourceConditionalModel.Actors runtime => read actor.val) /
          (inventoryBound runtime + 1 : ℝ) +
        ((SourceCopyWordAffine.compile
          (taskWord.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
          ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime))
            (fun actor : SourceConditionalModel.Actors runtime => read actor.val)
            (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime))
              (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
                (inventoryBound runtime)))‖ ^ 2) := by
  have paid := gRisk_refinement runtime taskWord read forget
  have fine := gRisk_optimal_account runtime taskWord read
  have coarse := gRisk_optimal_account runtime taskWord (forget ∘ read)
  have decoder : gCoarseMean runtime taskWord read forget =
      gFineMean runtime taskWord (forget ∘ read) := by
    funext key
    unfold gCoarseMean gFineMean
    rw [SourceConditionalMergeLoss.decoder_original]
  rw [← decoder] at coarse
  linarith only [paid, fine, coarse]

private theorem actual_copy_transported_empty :
    SourceWordFutureBitGrowth.nextWordAt 3 [] = [] := by
  simp [SourceWordFutureBitGrowth.nextWordAt,
    SourceWordFutureBitGrowth.transportWord]
  rfl

private theorem actual_copy_refinement_query (actor : Fin 5) :
    SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
        (SourceWordFutureBitGrowth.nextWordAt 3 []) actor.val) =
      SourceWordObservedCode.sourceQuery (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) actor := by
  let taskWord := SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]
  calc
    _ = SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1) taskWord
          (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4)) [] actor.val) := by
      rw [actual_copy_transported_empty]
    _ = SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4)) taskWord actor.val := by
      simpa only [List.nil_append] using
        (read_at_append (inventoryBound (runtimeAt 4)) [] taskWord actor.val).symm
    _ = SourceWordObservedCode.sourceQuery (runtimeAt 4) taskWord actor :=
      (SourceWordObservedCode.source_query_read _ _ _).symm

private theorem actual_copy_query_field
    (word : List (Letter (inventoryBound (runtimeAt 4) + 1))) :
    (fun actor : Fin 5 => SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
      word actor.val) = fieldCode 4 word ∘ Actor.nextRead 5 4 := by
  funext actor
  exact (actual_square 4 word actor).symm

/-- On the actual d4 old-letter birth, the transported copy loses exactly
    one fifth of a unit of optimal physical G recovery, although the original
    clock task pays zero new scalar L² error. -/
theorem actual_transported_copy_g_gap_exact :
    gGap (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
        (SourceWordFutureBitGrowth.nextWordAt 3 []))
      (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])) = 1 / 5 := by
  let runtime := runtimeAt 4
  let taskWord := SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]
  let beforeWord := SourceWordFutureBitGrowth.nextWordAt 3 []
  let read := SourceWordObservedCode.readAt (inventoryBound runtime) beforeWord
  let forget := SourceWordFutureBit.bitWord (inventoryBound runtime + 1) taskWord
  have account := gGap_cost_residual_account runtime taskWord read forget
  have beforeQuery : (fun actor : SourceConditionalModel.Actors runtime => read actor.val) =
      SourceWordObservedCode.sourceQuery runtime beforeWord := by
    funext actor
    exact (SourceWordObservedCode.source_query_read runtime beforeWord actor).symm
  have afterQuery : (fun actor : SourceConditionalModel.Actors runtime => (forget ∘ read) actor.val) =
      SourceWordObservedCode.sourceQuery runtime taskWord := by
    funext actor
    exact actual_copy_refinement_query actor
  have beforeCost : SourceConditionalInventory.cost (inventoryBound runtime)
      (fun actor : SourceConditionalModel.Actors runtime => read actor.val) = 3 := by
    rw [beforeQuery]
    exact actual_copy_before_cost
  have afterCost : SourceConditionalInventory.cost (inventoryBound runtime)
      (fun actor : SourceConditionalModel.Actors runtime => (forget ∘ read) actor.val) = 4 := by
    rw [afterQuery]
    exact actual_copy_next_cost
  have clockResidual :
      ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime))
        (fun actor : SourceConditionalModel.Actors runtime => (forget ∘ read) actor.val)
        (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime))
          (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
            (inventoryBound runtime)))‖ ^ 2 =
      ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime))
        (fun actor : SourceConditionalModel.Actors runtime => read actor.val)
        (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime))
          (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
            (inventoryBound runtime)))‖ ^ 2 := by
    rw [afterQuery, beforeQuery]
    have old := actual_birth_copy_clock_residual_unchanged
    dsimp only at old
    rw [← actual_copy_query_field taskWord,
      ← actual_copy_query_field beforeWord] at old
    exact old
  have weightedResidual := congrArg
    (fun value : ℝ => ((SourceCopyWordAffine.compile
      (taskWord.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 * value)
    clockResidual
  dsimp only [runtime, taskWord, beforeWord, read, forget] at account beforeCost afterCost clockResidual weightedResidual ⊢
  simp only [SourceConditionalInventory.runtime_bound,
    Nat.cast_ofNat] at account beforeCost afterCost clockResidual weightedResidual
  linear_combination account + (1 / 5 : ℝ) * afterCost -
    (1 / 5 : ℝ) * beforeCost + weightedResidual

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
