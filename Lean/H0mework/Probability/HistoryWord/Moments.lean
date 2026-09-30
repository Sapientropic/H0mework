import H0mework.Probability.HistoryWord.Hilbert

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryWord

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance SourceSuccessorBoundary
open MeasureTheory
noncomputable section

private theorem root_weight (bound : Nat) (index : Fin (bound + 1)) :
    Real.sqrt (historyPMF bound index).toReal = Real.sqrt (bound + 1 : ℝ) * (historyPMF bound index).toReal := by
  rw [coefficient_scale, source_weight]
  have positive : 0 < (bound + 1 : ℝ) := by positivity
  have rootPositive := Real.sqrt_pos.mpr positive
  have square := Real.sq_sqrt positive.le
  field_simp
  nlinarith only [square]

theorem mass_original_mean (bound : Nat) (value : Space (historyPMF bound)) :
    SourceMassCompletion.massRead (joint bound value) =
      Real.sqrt (bound + 1 : ℝ) • ∫ index, value index ∂(historyPMF bound).toMeasure := by
  rw [mass_joint, PMF.integral_eq_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [root_weight, Complex.ofReal_mul]
  simp only [Complex.real_smul]
  ring

theorem joint_norm_sq (bound : Nat) (value : Space (historyPMF bound)) :
    ‖joint bound value‖ ^ 2 = ‖value‖ ^ 2 +
      (bound + 1 : ℝ) * ‖∫ index, value index ∂(historyPMF bound).toMeasure‖ ^ 2 := by
  change ‖SourceMassCompletion.jointRead (word bound value)‖ ^ 2 = _
  rw [SourceMassCompletion.jointRead_apply, WithLp.prod_norm_sq_eq_of_L2]
  change ‖readWord (word bound value)‖ ^ 2 + ‖mass ℂ (word bound value)‖ ^ 2 = _
  rw [hilbert_norm_sq]
  have original := mass_original_mean bound value
  change mass ℂ (word bound value) = _ at original
  rw [original, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ bound + 1)]

end
end SourceHistoryWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
