import H0mework.Fock.HistoryConditional.StabilitySupport

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorStability

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors NextModel nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def constantQuery (runtime : LivingRuntimeState process) : Actors runtime → Unit := fun _ => ()

theorem constant_supported (runtime : LivingRuntimeState process) :
    () ∈ ((historyPMF (inventoryBound runtime)).map (constantQuery runtime)).support :=
  SourceWeightedRecovery.observed_supported _ _ 0 (SourceConditionalModel.positive runtime 0)

def unobservedMean (runtime : LivingRuntimeState process) : NextModel runtime :=
  SourceConditionalVector.estimate runtime (constantQuery runtime) () (constant_supported runtime)

theorem unobserved_coordinate (runtime : LivingRuntimeState process) (actor : Actors runtime) :
    SourceGInformationCost.coordinateRead (actor.val + 1) (SourceConditionalVector.realizeModel runtime (unobservedMean runtime)) =
      ((1 / (inventoryBound runtime + 1 : ℝ) : ℝ) : ℂ) := by
  rw [unobservedMean, SourcePosteriorReadback.model_coordinate,
    SourceWeightedRecovery.ObservationRefinement.conditional_constant _ _ () (fun _ => rfl),
    SourceUniformFibreVariance.source_weight]

def mergedModel (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) : NextModel runtime :=
  unobservedMean runtime + (((inventoryBound runtime + 1 : ℝ)⁻¹ : ℝ) : ℂ) •
    (nextRead runtime (SourceConditionalModel.two runtime enough) - nextRead runtime 0)

theorem merged_zero (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) :
    SourcePosteriorReadback.readWeight runtime (mergedModel runtime enough) 0 = 0 := by
  rw [SourcePosteriorReadback.readWeight, mergedModel, map_add, map_smul, map_sub, map_add, map_smul, map_sub,
    unobserved_coordinate, ← SourceConditionalInventory.values_original, ← SourceConditionalInventory.values_original,
    SourceGInformationCost.coordinate_actual, SourceGInformationCost.coordinate_actual]
  rw [if_neg (SourceConditionalModel.two_ne_zero runtime enough), if_pos rfl]
  simp only [zero_sub, smul_eq_mul, mul_neg, mul_one, one_div, Complex.ofReal_inv, add_neg_cancel,
    Complex.zero_re, ENNReal.ofReal_zero]

theorem merged_distance (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) :
    ‖SourceConditionalVector.realizeModel runtime (mergedModel runtime enough) -
      SourceConditionalVector.realizeModel runtime (unobservedMean runtime)‖ ^ 2 =
        6 / (inventoryBound runtime + 1 : ℝ) ^ 2 := by
  rw [mergedModel, map_add, map_smul, map_sub, add_sub_cancel_left, norm_smul, mul_pow,
    norm_sub_rev, SourceConditionalVector.pair_distance runtime enough]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow]
  ring

theorem merged_fails_support (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) :
    restoredSupport runtime (mergedModel runtime enough) ≠
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (constantQuery runtime) () := by
  intro same
  have present : (0 : Actors runtime) ∈ SourceUniformFibreVariance.fibre (inventoryBound runtime) (constantQuery runtime) () := by
    rw [SourceUniformFibreVariance.fibre_mem]
  rw [← same, restoredSupport, Finset.mem_filter] at present
  rw [merged_zero, ENNReal.toReal_zero] at present
  exact (not_lt_of_ge (threshold_positive runtime).le) present.2

theorem arbitrarily_close_failure (tolerance : ℝ) (positive : 0 < tolerance) :
    ∃ (runtime : LivingRuntimeState process) (model : NextModel runtime),
      ‖SourceConditionalVector.realizeModel runtime model - SourceConditionalVector.realizeModel runtime (unobservedMean runtime)‖ < tolerance ∧
        restoredSupport runtime model ≠ SourceUniformFibreVariance.fibre (inventoryBound runtime) (constantQuery runtime) () := by
  obtain ⟨n, large⟩ := exists_nat_gt (6 / tolerance ^ 2 + 2)
  have enough : 2 ≤ inventoryBound (runtimeAt (n + 2)) := by
    rw [SourceConditionalInventory.runtime_bound]
    omega
  refine ⟨runtimeAt (n + 2), mergedModel _ enough, ?_, merged_fails_support _ enough⟩
  have square := merged_distance (runtimeAt (n + 2)) enough
  rw [SourceConditionalInventory.runtime_bound] at square
  have positiveSquare : 0 < tolerance ^ 2 := sq_pos_of_pos positive
  have six : 6 < (n : ℝ) * tolerance ^ 2 := (div_lt_iff₀ positiveSquare).mp (by linarith : 6 / tolerance ^ 2 < (n : ℝ))
  have growth : (n : ℝ) ≤ (n + 2 + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have scaled := mul_le_mul_of_nonneg_right growth (sq_nonneg tolerance)
  have fraction : 6 / (n + 2 + 1 : ℝ) ^ 2 < tolerance ^ 2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n + 2 + 1 : ℝ) ^ 2)).mpr
    nlinarith
  push_cast at square
  nlinarith [norm_nonneg (SourceConditionalVector.realizeModel (runtimeAt (n + 2)) (mergedModel _ enough) -
    SourceConditionalVector.realizeModel (runtimeAt (n + 2)) (unobservedMean _))]

end
end SourcePosteriorStability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
