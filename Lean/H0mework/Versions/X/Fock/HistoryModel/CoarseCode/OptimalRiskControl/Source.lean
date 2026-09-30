import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.RiskBirth
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.OptimalRiskBirth

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem actual_copy_next_query_zero (actor : Fin 5) :
    SourceWordObservedCode.sourceQuery (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) actor = 0 := by
  have action := read_at_append 3 [] [SourceWordDynamicNext.copyOne] actor.val
  change SourceWordObservedCode.readAt 3 [SourceWordDynamicNext.copyOne] actor.val =
    SourceWordFutureBit.bitAction 4 SourceWordDynamicNext.copyOne
      (SourceWordObservedCode.readAt 3 [] actor.val) at action
  have erased (bit : ZMod 2) :
      SourceWordFutureBit.bitAction 4 SourceWordDynamicNext.copyOne bit = 0 := by
    fin_cases bit <;> decide
  calc
    _ = SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
          (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) actor.val :=
      SourceWordObservedCode.source_query_read _ _ _
    _ = SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
          (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) actor.val :=
      SourceWordFutureBitGrowth.old_next_read_at _ _ _
    _ = SourceWordObservedCode.readAt 3 [SourceWordDynamicNext.copyOne] actor.val :=
      SourceWordFutureBitGrowth.transport_read_at _ _ _
    _ = 0 := action.trans (erased _)

theorem actual_copy_next_cost :
    SourceConditionalInventory.cost 4
      (SourceWordObservedCode.sourceQuery (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])) = 4 := by
  have query : SourceWordObservedCode.sourceQuery (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) =
      (fun _ : Fin 5 => (0 : ZMod 2)) := by
    funext actor
    exact actual_copy_next_query_zero actor
  calc
    _ = (4 + 1 : ℝ) -
        (SourceUniformFibreVariance.outputs 4
          (SourceWordObservedCode.sourceQuery (runtimeAt 4)
            (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]))).card :=
      SourceConditionalInventory.cost_eq _ _
    _ = 4 := by
      rw [query]
      have image : (Finset.univ : Finset (Fin 5)).image
          (fun _ => (0 : ZMod 2)) = {0} := by
        ext value
        simp [eq_comm]
      simp [SourceUniformFibreVariance.outputs, image]

theorem actual_copy_old_query_zero (actor : Fin 4) :
    SourceWordObservedCode.sourceQuery (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) actor = 0 := by
  have transported := SourceCompiledGWord.query_native_birth_old_actor 3
    [SourceWordDynamicNext.copyOne] actor
  have zero := actual_copy_next_query_zero actor.castSucc
  change SourceWordObservedCode.sourceQuery (runtimeAt 4)
    (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) actor.castSucc =
    SourceWordObservedCode.sourceQuery (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) actor at transported
  exact transported.symm.trans zero

theorem actual_copy_born_key_zero :
    SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
      (inventoryBound (runtimeAt 3) + 1) = 0 := by
  have nextZero := actual_copy_next_query_zero (Fin.last 4)
  have key := gBornKey_native_birth 3 [SourceWordDynamicNext.copyOne]
  change SourceWordObservedCode.sourceQuery (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
      (Fin.last 4) = _ at key
  exact key.symm.trans nextZero

theorem actual_copy_old_fibre_count :
    (SourceConditionalNativeObservers.generate
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]))
      (inventoryBound (runtimeAt 3))
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
        (inventoryBound (runtimeAt 3) + 1))).1 = 4 := by
  rw [actual_copy_born_key_zero,
    SourceConditionalNativePosterior.count_sum]
  change (∑ actor : Fin 4, if SourceWordObservedCode.readAt
    (inventoryBound (runtimeAt 3))
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
      actor.val = (0 : ZMod 2) then 1 else 0) = 4
  have readZero (actor : Fin 4) : SourceWordObservedCode.readAt
      (inventoryBound (runtimeAt 3))
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
      actor.val = 0 := by
    have source := SourceWordObservedCode.source_query_read (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
      (actor.cast (by simp only [SourceConditionalInventory.runtime_bound]))
    change SourceWordObservedCode.sourceQuery (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) actor =
      SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) actor.val at source
    exact source.symm.trans (actual_copy_old_query_zero actor)
  simp only [readZero, ite_true]
  norm_num

theorem actual_copy_optimal_g_total_birth :
    gTotal (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) =
      gTotal (runtimeAt 3)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) +
      (4 / 5 : ℝ) *
        ‖SourceCompiledGWord.image (runtimeAt 4)
            (inventoryBound (runtimeAt 4) + 1)
            (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
            (Fin.last (inventoryBound (runtimeAt 4))) -
          gBest (runtimeAt 3)
            (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) 0‖ ^ 2 := by
  have birth := gTotal_native_birth 3 [SourceWordDynamicNext.copyOne]
  dsimp only at birth
  have countZero : (SourceConditionalNativeObservers.generate
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]))
      (inventoryBound (runtimeAt 3)) (0 : ZMod 2)).1 = 4 := by
    simpa only [actual_copy_born_key_zero] using actual_copy_old_fibre_count
  rw [actual_copy_born_key_zero, countZero] at birth
  norm_num at birth
  exact birth

theorem actual_copy_next_clock_residual_sq :
    ‖SourceWeightedRecovery.residual (historyPMF 4)
        (SourceWordObservedCode.sourceQuery (runtimeAt 4)
          (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]))
        (SourceWeightedRecovery.taskValue (historyPMF 4)
          (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 4))‖ ^ 2 = 2 := by
  have query : SourceWordObservedCode.sourceQuery (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) =
      (fun _ : Fin 5 => (0 : ZMod 2)) := by
    funext actor
    exact actual_copy_next_query_zero actor
  rw [query, SourceGInformationCost.clock_signal]
  have pair := SourceUniformFibreVariance.residual_pairwise 4
    (fun _ : Fin 5 => (0 : ZMod 2)) (fun actor : Fin 5 => (actor.val : ℝ) + 2)
  rw [pair]
  have image : (Finset.univ : Finset (Fin 5)).image
      (fun _ => (0 : ZMod 2)) = {0} := by
    ext value
    simp [eq_comm]
  simp only [SourceUniformFibreVariance.outputs]
  rw [image]
  norm_num [SourceUniformFibreVariance.outputs, SourceUniformFibreVariance.fibre,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

theorem actual_copy_next_slope_sq :
    ((SourceCopyWordAffine.compile
      ((SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]).map
        SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 = 4 := by
  have slope : (SourceCopyWordAffine.compile
      ((SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]).map
        SourceCopyNativeWord.encode)).1 = 2 := by decide
  rw [slope]
  norm_num

theorem actual_copy_next_optimal_g_risk :
    SourceWordCodeRisk.risk (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
      (SourceWordObservedCode.encodeObserved (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]))
      (gBest (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])) = 44 / 5 := by
  have account := SourceWordCodeRisk.risk_account (runtimeAt 4)
    (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
    (SourceWordObservedCode.encodeObserved (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]))
    (gBest (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]))
  rw [SourceWordObservedCode.query_source] at account
  simp_rw [gBest_effect_mean] at account
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero, add_zero] at account
  have costValue : SourceConditionalInventory.cost (inventoryBound (runtimeAt 4))
      (SourceWordObservedCode.sourceQuery (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])) = 4 := by
    have bound : inventoryBound (runtimeAt 4) = 4 :=
      SourceConditionalInventory.runtime_bound 4
    cases bound
    exact actual_copy_next_cost
  have residualValue : ‖SourceWeightedRecovery.residual
      (historyPMF (inventoryBound (runtimeAt 4)))
      (SourceWordObservedCode.sourceQuery (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]))
      (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound (runtimeAt 4)))
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
          (inventoryBound (runtimeAt 4))))‖ ^ 2 = 2 := by
    have bound : inventoryBound (runtimeAt 4) = 4 :=
      SourceConditionalInventory.runtime_bound 4
    cases bound
    exact actual_copy_next_clock_residual_sq
  rw [costValue, actual_copy_next_slope_sq, residualValue] at account
  rw [SourceConditionalInventory.runtime_bound 4] at account
  norm_num at account
  exact account
end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
