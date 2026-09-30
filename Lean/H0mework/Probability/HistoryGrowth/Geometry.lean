import H0mework.Probability.Source.HistoryGrowth
import H0mework.Realization.HilbertTransfer.Transfer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryGrowth

open SourceWeightedRecovery SourceGeneratedAtomicObservation SourceGeneratedRuntimeHistoryProbability
open SourceUniformFibreVariance MeasureTheory
open scoped InnerProductSpace Classical
noncomputable section

variable {old fresh : Nat} (retained : old ≤ fresh)

theorem extend_norm (value : Space (historyPMF old)) :
    ‖extend retained value‖ = Real.sqrt (fraction old fresh) * ‖value‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [extend_norm_sq, mul_pow, Real.sq_sqrt (fraction_pos old fresh).le]

def normalizedInclusion : Space (historyPMF old) →ₗᵢ[ℂ] Space (historyPMF fresh) where
  toLinearMap := ((Real.sqrt (fraction old fresh))⁻¹ • extend retained).toLinearMap
  norm_map' value := by
    change ‖(Real.sqrt (fraction old fresh))⁻¹ • extend retained value‖ = ‖value‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (fraction_pos old fresh))),
      extend_norm, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr (fraction_pos old fresh)).ne', one_mul]

theorem transfer_is_restriction (value : Space (historyPMF fresh)) :
    IsometricRetainedTransfer.transfer (normalizedInclusion retained) value =
      Real.sqrt (fraction old fresh) • restrict retained value := by
  apply ext_inner_left ℂ
  intro left
  rw [IsometricRetainedTransfer.transfer, ContinuousLinearMap.adjoint_inner_right]
  change ⟪(Real.sqrt (fraction old fresh))⁻¹ • extend retained left, value⟫_ℂ = _
  rw [inner_smul_left_eq_star_smul]
  change (Real.sqrt (fraction old fresh))⁻¹ • ⟪extend retained left, value⟫_ℂ = _
  rw [inner_extend, inner_smul_right_eq_smul, smul_smul]
  have coefficient : (Real.sqrt (fraction old fresh))⁻¹ * fraction old fresh = Real.sqrt (fraction old fresh) := by
    calc
      _ = (Real.sqrt (fraction old fresh))⁻¹ *
          (Real.sqrt (fraction old fresh) * Real.sqrt (fraction old fresh)) :=
        congrArg ((Real.sqrt (fraction old fresh))⁻¹ * ·)
          (by nlinarith only [Real.sq_sqrt (fraction_pos old fresh).le])
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr (fraction_pos old fresh)).ne', one_mul]
  rw [coefficient]

abbrev remainder : Space (historyPMF fresh) →L[ℂ] Space (historyPMF fresh) :=
  IsometricRetainedTransfer.residual (normalizedInclusion retained)

theorem remainder_eq (value : Space (historyPMF fresh)) :
    remainder retained value = value - extend retained (restrict retained value) := by
  change value - normalizedInclusion retained
    (IsometricRetainedTransfer.transfer (normalizedInclusion retained) value) = _
  rw [transfer_is_restriction]
  change value - (Real.sqrt (fraction old fresh))⁻¹ •
    extend retained (Real.sqrt (fraction old fresh) • restrict retained value) = _
  rw [LinearMapClass.map_smul_of_tower, smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (fraction_pos old fresh)).ne', one_smul]

theorem energy_decomposition (value : Space (historyPMF fresh)) :
    ‖value‖ ^ 2 = fraction old fresh * ‖restrict retained value‖ ^ 2 + ‖remainder retained value‖ ^ 2 := by
  have original := IsometricRetainedTransfer.energy_decomposition (normalizedInclusion retained) value
  rw [transfer_is_restriction, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (fraction_pos old fresh).le] at original
  exact original

theorem restriction_bound (value : Space (historyPMF fresh)) :
    ‖restrict retained value‖ ≤ (Real.sqrt (fraction old fresh))⁻¹ * ‖value‖ := by
  have original := IsometricRetainedTransfer.transfer_norm_le (normalizedInclusion retained) value
  rw [transfer_is_restriction, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at original
  calc
    _ ≤ ‖value‖ / Real.sqrt (fraction old fresh) :=
      (le_div_iff₀ (Real.sqrt_pos.mpr (fraction_pos old fresh))).mpr (by simpa [mul_comm] using original)
    _ = _ := by ring

theorem restriction_norm : ‖restrict retained‖ = (Real.sqrt (fraction old fresh))⁻¹ := by
  apply le_antisymm
  · exact (restrict retained).opNorm_le_bound (by positivity) (restriction_bound retained)
  · let witness := cotest (historyPMF old) (0 : Fin (old + 1))
    have positive : 0 < ‖witness‖ := by
      rw [cotest_norm]
      exact Real.sqrt_pos.mpr (mass_positive _ _ (source_positive old 0))
    have actual := (restrict retained).le_opNorm (extend retained witness)
    rw [restrict_extend, extend_norm] at actual
    have scaled : 1 * ‖witness‖ ≤ (‖restrict retained‖ * Real.sqrt (fraction old fresh)) * ‖witness‖ := by
      simpa only [one_mul, mul_assoc] using actual
    have cancel := (mul_le_mul_iff_of_pos_right positive).mp scaled
    rw [← one_div]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr (fraction_pos old fresh))).mpr cancel

end
end SourceHistoryGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
