import H0mework.Probability.Information.MatrixIdentity

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceBinaryMatrix

open scoped ComplexOrder
noncomputable section

variable {Index : Type*} [Fintype Index]

theorem deviation_le_determinant (weight : Index → ℝ)
    (state : Index → Matrix (Fin 2) (Fin 2) ℂ)
    (nonnegative : ∀ index, 0 ≤ weight index) (total : ∑ index, weight index = 1)
    (positive : ∀ index, (state index).PosSemidef)
    (normalized : ∀ index, (state index).trace = 1) :
    (∑ index, weight index * ((state index 0 0).re - (mixture weight state 0 0).re) ^ 2) ≤
      (mixture weight state).det.re := by
  have mixedness : 0 ≤ ∑ index, weight index * (state index).det.re :=
    Finset.sum_nonneg fun index _ => mul_nonneg (nonnegative index)
      (Complex.nonneg_iff.mp (positive index).det_nonneg).1
  have coherence : 0 ≤ ∑ index, weight index * ‖state index 0 1 - mixture weight state 0 1‖ ^ 2 :=
    Finset.sum_nonneg fun index _ => mul_nonneg (nonnegative index) (sq_nonneg _)
  have decomposition := determinant_decomposition weight state nonnegative total positive normalized
  linarith

theorem covariance_determinant_budget (weight value : Index → ℝ)
    (state : Index → Matrix (Fin 2) (Fin 2) ℂ)
    (nonnegative : ∀ index, 0 ≤ weight index) (total : ∑ index, weight index = 1)
    (positive : ∀ index, (state index).PosSemidef)
    (normalized : ∀ index, (state index).trace = 1) :
    (∑ index, weight index * ((state index 0 0).re - (mixture weight state 0 0).re) * value index) ^ 2 +
      (∑ index, weight index * value index ^ 2) * (∑ index, weight index * (state index).det.re) +
      (∑ index, weight index * value index ^ 2) *
        (∑ index, weight index * ‖state index 0 1 - mixture weight state 0 1‖ ^ 2) ≤
      (∑ index, weight index * value index ^ 2) * (mixture weight state).det.re := by
  have covariance :
      (∑ index, weight index * ((state index 0 0).re - (mixture weight state 0 0).re) * value index) ^ 2 ≤
        (∑ index, weight index * ((state index 0 0).re - (mixture weight state 0 0).re) ^ 2) *
          ∑ index, weight index * value index ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    · intro index _
      exact mul_nonneg (nonnegative index) (sq_nonneg _)
    · intro index _
      exact mul_nonneg (nonnegative index) (sq_nonneg _)
    · intro index _
      apply le_of_eq
      ring
  rw [determinant_decomposition weight state nonnegative total positive normalized]
  nlinarith only [covariance]

theorem covariance_determinant_bound (weight value : Index → ℝ)
    (state : Index → Matrix (Fin 2) (Fin 2) ℂ)
    (nonnegative : ∀ index, 0 ≤ weight index) (total : ∑ index, weight index = 1)
    (positive : ∀ index, (state index).PosSemidef)
    (normalized : ∀ index, (state index).trace = 1) :
    (∑ index, weight index * ((state index 0 0).re - (mixture weight state 0 0).re) * value index) ^ 2 ≤
      (∑ index, weight index * value index ^ 2) * (mixture weight state).det.re := by
  have variance : 0 ≤ ∑ index, weight index * value index ^ 2 :=
    Finset.sum_nonneg fun index _ => mul_nonneg (nonnegative index) (sq_nonneg _)
  have mixedness : 0 ≤ ∑ index, weight index * (state index).det.re :=
    Finset.sum_nonneg fun index _ => mul_nonneg (nonnegative index)
      (Complex.nonneg_iff.mp (positive index).det_nonneg).1
  have coherence : 0 ≤ ∑ index, weight index * ‖state index 0 1 - mixture weight state 0 1‖ ^ 2 :=
    Finset.sum_nonneg fun index _ => mul_nonneg (nonnegative index) (sq_nonneg _)
  have budget := covariance_determinant_budget weight value state nonnegative total positive normalized
  linarith [mul_nonneg variance mixedness, mul_nonneg variance coherence]

end
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceBinaryMatrix
