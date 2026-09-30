import H0mework.Probability.Runtime.History
import H0mework.Probability.Recovery.Error

/-! Original uniform history weights give the exact error of forgetting an affine source clock. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.ObservationRefinement

open SourceGeneratedRuntimeHistoryProbability

noncomputable section

private theorem affine_square_sum (bound : Nat) (start step : ℝ) (value : ℂ) :
    (∑ index : Fin (bound + 1), ‖((start + index.val * step : ℝ) : ℂ) - value‖ ^ 2) =
      (bound + 1) * (step ^ 2 * bound * (bound + 2) / 12 +
        ‖((start + bound / 2 * step : ℝ) : ℂ) - value‖ ^ 2) := by
  induction bound with
  | zero => simp
  | succ bound previous =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [previous]
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im]
      push_cast
      ring

theorem uniform_clock_error (bound : Nat) (start step : ℝ) (value : ℂ) :
    (∑ index : Fin (bound + 1), (historyPMF bound index).toReal *
      ‖((start + index.val * step : ℝ) : ℂ) - value‖ ^ 2) =
      step ^ 2 * bound * (bound + 2) / 12 +
        ‖((start + bound / 2 * step : ℝ) : ℂ) - value‖ ^ 2 := by
  simp only [historyPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum, affine_square_sum]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (bound : ℝ) + 1 ≠ 0), one_mul]

end
end SourceWeightedRecovery.ObservationRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
