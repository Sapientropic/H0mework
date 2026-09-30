import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.ColumnGapMass
import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.ColumnAction
import H0mework.Versions.Y.Arithmetic.RieszColumns.Columns

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Complex Filter MeasureTheory Set
open OriginalRieszSource OriginalRieszFiniteSource OriginalRieszFiniteColumns OriginalRieszSourceGreen OriginalPaPhysicalGreen
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "E" => burnolQuarterZeroExtension

private theorem extension_mass (value : BurnolQuarterMeanZeroCarrier) :
    Integrable (E (value : BurnolQuarterIntervalL2)) ∧
      (∫ x : ℝ, E (value : BurnolQuarterIntervalL2) x) = 0 := by
  have cutoff : originalPhysicalCutoff q (E (value : BurnolQuarterIntervalL2)) = E (value : BurnolQuarterIntervalL2) := by
    change burnolRadiusZeroExtension q (burnolRadiusRestriction q
      (burnolRadiusZeroExtension q (value : BurnolQuarterIntervalL2))) = _
    rw [burnolRadiusRestriction_zeroExtension]
    rfl
  refine ⟨integrable_of_cutoff_eq_self q _ cutoff, ?_⟩
  change (∫ x : ℝ, burnolRadiusZeroExtension q (value : BurnolQuarterIntervalL2) x) = 0
  rw [integral_congr_ae (burnolRadiusZeroExtension_coe (value : BurnolQuarterIntervalL2)),
    integral_indicator (measurableSet_symmetricInterval q)]
  have mean := Constructor.mean_zero value
  rw [Constructor.mean_integral] at mean
  exact (mul_eq_zero.mp mean).resolve_left (by norm_num)

private theorem dilation_mass (value : BurnolL2) (shift : ℝ)
    (source : Integrable value ∧ (∫ x : ℝ, value x) = 0) :
    Integrable (burnolMultiplicativeDilation shift value) ∧
      (∫ x : ℝ, burnolMultiplicativeDilation shift value x) = 0 := by
  have read := burnolMultiplicativeDilation_coeFn shift value
  refine ⟨((source.1.comp_mul_left' (Real.exp_ne_zero shift)).const_mul
    (Real.exp (shift / 2) : ℂ)).congr read.symm, ?_⟩
  rw [integral_congr_ae read]
  change (∫ x : ℝ, (Real.exp (shift / 2) : ℂ) * value (Real.exp shift * x)) = 0
  rw [integral_const_mul, Measure.integral_comp_mul_left, source.2, smul_zero, mul_zero]

private theorem smul_mass (value : BurnolL2) (coefficient : ℂ)
    (source : Integrable value ∧ (∫ x : ℝ, value x) = 0) :
    Integrable (coefficient • value : BurnolL2) ∧
      (∫ x : ℝ, (coefficient • value : BurnolL2) x) = 0 := by
  refine ⟨(source.1.const_mul coefficient).congr (Lp.coeFn_smul coefficient value).symm, ?_⟩
  rw [integral_congr_ae (Lp.coeFn_smul coefficient value)]
  change (∫ x : ℝ, coefficient * value x) = 0
  rw [integral_const_mul, source.2, mul_zero]

private theorem sub_mass (left right : BurnolL2)
    (leftSource : Integrable left ∧ (∫ x : ℝ, left x) = 0)
    (rightSource : Integrable right ∧ (∫ x : ℝ, right x) = 0) :
    Integrable (left - right : BurnolL2) ∧ (∫ x : ℝ, (left - right : BurnolL2) x) = 0 := by
  refine ⟨(leftSource.1.sub rightSource.1).congr (Lp.coeFn_sub left right).symm, ?_⟩
  rw [integral_congr_ae (Lp.coeFn_sub left right)]
  change (∫ x : ℝ, left x - right x) = 0
  rw [integral_sub leftSource.1 rightSource.1, leftSource.2, rightSource.2, sub_self]

private theorem add_mass (left right : BurnolL2)
    (leftSource : Integrable left ∧ (∫ x : ℝ, left x) = 0)
    (rightSource : Integrable right ∧ (∫ x : ℝ, right x) = 0) :
    Integrable (left + right : BurnolL2) ∧ (∫ x : ℝ, (left + right : BurnolL2) x) = 0 := by
  refine ⟨(leftSource.1.add rightSource.1).congr (Lp.coeFn_add left right).symm, ?_⟩
  rw [integral_congr_ae (Lp.coeFn_add left right)]
  change (∫ x : ℝ, left x + right x) = 0
  rw [integral_add leftSource.1 rightSource.1, leftSource.2, rightSource.2, add_zero]

private theorem nativeIntegral_quarter (lambda : ℂ) (value : BurnolQuarterIntervalL2)
    (endpoint : ℝ) (nonnegative : 0 ≤ endpoint) :
    originalPhysicalCutoff q (nativeIntegral lambda (E value) endpoint) = nativeIntegral lambda (E value) endpoint := by
  apply intervalIntegral_cutoff_self _ _ _ _ (nativeIntegrand_integrable _ _ _)
  intro time inside
  rw [uIcc_of_le nonnegative] at inside
  apply cutoff_smul_self
  apply intervalDilation_cutoff_self
  exact mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ q)
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr inside.1))

private theorem edgeIntegral_quarter (coordinate : BurnolCompletedMellinCoordinate)
    (endpoint : ℝ) (nonnegative : 0 ≤ endpoint) :
    originalPhysicalCutoff q (edgeIntegral coordinate endpoint) = edgeIntegral coordinate endpoint :=
  cutoff_eq_self_of_ae_zero q _ (edgeIntegral_ae_zero coordinate endpoint q le_rfl
    (mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ q)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative))))

theorem positionColumn_quarter (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    originalPhysicalCutoff q (positionColumn coordinate shift) = positionColumn coordinate shift := by
  change (burnolRadiusZeroExtension q).comp (burnolRadiusRestriction q) (positionColumn coordinate shift) = _
  unfold positionColumn
  rw [map_sub, map_smul]
  change originalPhysicalCutoff q _ - Kernel.A coordinate • originalPhysicalCutoff q _ = _
  rw [nativeIntegral_quarter _ _ shift nonnegative, edgeIntegral_quarter coordinate shift nonnegative]

private theorem backwardIntegral_negative_quarter (lambda : ℂ) (value : BurnolQuarterIntervalL2)
    (endpoint : ℝ) (nonnegative : 0 ≤ endpoint) :
    originalPhysicalCutoff q (backwardIntegral lambda (E value) (-endpoint)) = backwardIntegral lambda (E value) (-endpoint) := by
  apply intervalIntegral_cutoff_self _ _ _ _ ((backwardIntegrand_continuous _ _ _).intervalIntegrable 0 (-endpoint))
  intro time inside
  rw [uIcc_of_ge (neg_nonpos.mpr nonnegative)] at inside
  apply cutoff_smul_self
  apply intervalDilation_cutoff_self
  simp only [neg_neg]
  exact mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ q) (Real.exp_le_one_iff.mpr inside.2)

private theorem reverseEdgeIntegral_negative_quarter (coordinate : BurnolCompletedMellinCoordinate)
    (endpoint : ℝ) (nonnegative : 0 ≤ endpoint) :
    originalPhysicalCutoff q (reverseEdgeIntegral coordinate (-endpoint)) = reverseEdgeIntegral coordinate (-endpoint) := by
  have integral := intervalIntegral_cutoff_self q (reverseEdgeIntegrand coordinate (-endpoint)) 0 (-endpoint)
    ((reverseEdgeIntegrand_continuous coordinate (-endpoint)).intervalIntegrable 0 (-endpoint)) (by
      intro time inside
      rw [uIcc_of_ge (neg_nonpos.mpr nonnegative)] at inside
      exact cutoff_smul_self q _ _ (edgeIntegral_quarter coordinate (-time) (neg_nonneg.mpr inside.2)))
  change (burnolRadiusZeroExtension q).comp (burnolRadiusRestriction q) (reverseEdgeIntegral coordinate (-endpoint)) = _
  unfold reverseEdgeIntegral
  rw [map_sub, map_smul]
  change (2 * (star coordinate.value - 1 / 2)) • originalPhysicalCutoff q _ - originalPhysicalCutoff q _ = _
  rw [integral, neg_neg, edgeIntegral_quarter coordinate endpoint nonnegative]

theorem fourierColumn_negative_quarter (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    originalPhysicalCutoff q (fourierColumn coordinate (-shift)) = fourierColumn coordinate (-shift) := by
  change (burnolRadiusZeroExtension q).comp (burnolRadiusRestriction q) (fourierColumn coordinate (-shift)) = _
  unfold fourierColumn
  rw [map_sub, map_smul]
  change originalPhysicalCutoff q _ - Kernel.beta coordinate • originalPhysicalCutoff q _ = _
  rw [backwardIntegral_negative_quarter _ _ shift nonnegative, reverseEdgeIntegral_negative_quarter coordinate shift nonnegative]

theorem fourierColumn_integral_zero (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (∫ x : ℝ, fourierColumn coordinate shift x) = 0 := by
  rw [fourierColumn_action]
  exact (sub_mass _ _
    (smul_mass _ (fullMellinTranslationCharacter (star coordinate.value) shift)
      (extension_mass (burnolRieszSingleFourierSource coordinate)))
    (dilation_mass _ (-shift) (extension_mass (burnolRieszSingleFourierSource coordinate)))).2

theorem positionColumn_integral_zero (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (∫ x : ℝ, positionColumn coordinate shift x) = 0 := by
  have split : positionColumn coordinate shift = gapDilationDifference coordinate shift +
      (burnolMultiplicativeDilation shift (E (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) -
        fullMellinTranslationCharacter (star coordinate.value) shift •
          E (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) := by
    rw [positionColumn_action]
    unfold gapDilationDifference
    rw [map_add, smul_add]
    module
  rw [split]
  exact (add_mass _ _
    ⟨gapDilationDifference_integrable coordinate shift, gapDilationDifference_integral_zero coordinate shift⟩
    (sub_mass _ _ (dilation_mass _ shift (extension_mass (Constructor.returnState coordinate)))
      (smul_mass _ (fullMellinTranslationCharacter (star coordinate.value) shift)
        (extension_mass (Constructor.returnState coordinate))))).2

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
