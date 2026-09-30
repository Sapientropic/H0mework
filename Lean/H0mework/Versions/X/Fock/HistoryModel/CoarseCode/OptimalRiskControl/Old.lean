import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.OptimalRiskControl.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem actual_copy_old_cost :
    SourceConditionalInventory.cost 3
      (SourceWordObservedCode.sourceQuery (runtimeAt 3)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])) = 3 := by
  have query : SourceWordObservedCode.sourceQuery (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) =
      (fun _ : Fin 4 => (0 : ZMod 2)) := by
    funext actor
    exact actual_copy_old_query_zero actor
  calc
    _ = (3 + 1 : ℝ) -
        (SourceUniformFibreVariance.outputs 3
          (SourceWordObservedCode.sourceQuery (runtimeAt 3)
            (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]))).card :=
      SourceConditionalInventory.cost_eq _ _
    _ = 3 := by
      rw [query]
      have image : (Finset.univ : Finset (Fin 4)).image
          (fun _ => (0 : ZMod 2)) = {0} := by
        ext value
        simp [eq_comm]
      simp [SourceUniformFibreVariance.outputs, image]

theorem actual_copy_old_clock_residual_sq :
    ‖SourceWeightedRecovery.residual (historyPMF 3)
        (SourceWordObservedCode.sourceQuery (runtimeAt 3)
          (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]))
        (SourceWeightedRecovery.taskValue (historyPMF 3)
          (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values 3))‖ ^ 2 = 5 / 4 := by
  have query : SourceWordObservedCode.sourceQuery (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) =
      (fun _ : Fin 4 => (0 : ZMod 2)) := by
    funext actor
    exact actual_copy_old_query_zero actor
  rw [query, SourceGInformationCost.clock_signal]
  have pair := SourceUniformFibreVariance.residual_pairwise 3
    (fun _ : Fin 4 => (0 : ZMod 2)) (fun actor : Fin 4 => (actor.val : ℝ) + 2)
  rw [pair]
  have image : (Finset.univ : Finset (Fin 4)).image
      (fun _ => (0 : ZMod 2)) = {0} := by
    ext value
    simp [eq_comm]
  simp only [SourceUniformFibreVariance.outputs]
  rw [image]
  norm_num [SourceUniformFibreVariance.outputs, SourceUniformFibreVariance.fibre,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

theorem actual_copy_old_slope_sq :
    ((SourceCopyWordAffine.compile
      ((SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]).map
        SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 = 4 := by
  have slope : (SourceCopyWordAffine.compile
      ((SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]).map
        SourceCopyNativeWord.encode)).1 = 2 := by decide
  rw [slope]
  norm_num

theorem actual_copy_old_optimal_g_risk :
    SourceWordCodeRisk.risk (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
      (SourceWordObservedCode.encodeObserved (runtimeAt 3)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]))
      (gBest (runtimeAt 3)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])) = 23 / 4 := by
  have account := SourceWordCodeRisk.risk_account (runtimeAt 3)
    (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
    (SourceWordObservedCode.encodeObserved (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]))
    (gBest (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]))
  rw [SourceWordObservedCode.query_source] at account
  simp_rw [gBest_effect_mean] at account
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero, add_zero] at account
  have costValue : SourceConditionalInventory.cost (inventoryBound (runtimeAt 3))
      (SourceWordObservedCode.sourceQuery (runtimeAt 3)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])) = 3 := by
    have bound : inventoryBound (runtimeAt 3) = 3 :=
      SourceConditionalInventory.runtime_bound 3
    cases bound
    exact actual_copy_old_cost
  have residualValue : ‖SourceWeightedRecovery.residual
      (historyPMF (inventoryBound (runtimeAt 3)))
      (SourceWordObservedCode.sourceQuery (runtimeAt 3)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]))
      (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound (runtimeAt 3)))
        (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
          (inventoryBound (runtimeAt 3))))‖ ^ 2 = 5 / 4 := by
    have bound : inventoryBound (runtimeAt 3) = 3 :=
      SourceConditionalInventory.runtime_bound 3
    cases bound
    exact actual_copy_old_clock_residual_sq
  rw [costValue, actual_copy_old_slope_sq, residualValue] at account
  rw [SourceConditionalInventory.runtime_bound 3] at account
  norm_num at account
  exact account

theorem actual_copy_old_gTotal :
    gTotal (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) = 23 := by
  unfold gTotal
  rw [actual_copy_old_optimal_g_risk, SourceConditionalInventory.runtime_bound 3]
  norm_num

theorem actual_copy_next_gTotal :
    gTotal (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) = 44 := by
  unfold gTotal
  rw [actual_copy_next_optimal_g_risk, SourceConditionalInventory.runtime_bound 4]
  norm_num

theorem actual_copy_born_g_innovation_sq :
    ‖SourceCompiledGWord.image (runtimeAt 4)
        (inventoryBound (runtimeAt 4) + 1)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
        (Fin.last (inventoryBound (runtimeAt 4))) -
      gBest (runtimeAt 3)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) 0‖ ^ 2 =
      105 / 4 := by
  have birth := actual_copy_optimal_g_total_birth
  rw [actual_copy_old_gTotal, actual_copy_next_gTotal] at birth
  nlinarith

theorem actual_copy_optimal_g_total_gain_positive :
    0 < gTotal (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) -
      gTotal (runtimeAt 3)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne]) := by
  rw [actual_copy_old_gTotal, actual_copy_next_gTotal]
  norm_num
end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
