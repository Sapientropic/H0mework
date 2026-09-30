import H0mework.Arithmetic.BurnolMellin.GaussianFourierKernel
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set

noncomputable section

theorem gammaReal_mul_positive_cpow_neg_eq_gaussianSuperposition
    (s : ℂ) (positiveS : 0 < s.re) {x : ℝ} (positiveX : 0 < x) :
    Gammaℝ s * (x : ℂ) ^ (-s) =
      ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (s / 2 - 1) *
          Complex.exp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * (t : ℂ))) := by
  have positiveHalf : 0 < (s / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  have positiveRate : 0 < Real.pi * x ^ 2 :=
    mul_pos Real.pi_pos (sq_pos_of_pos positiveX)
  rw [integral_cpow_mul_exp_neg_mul_Ioi positiveHalf positiveRate]
  rw [Gammaℝ_def]
  have reciprocalRate :
      (1 : ℂ) / ((Real.pi * x ^ 2 : ℝ) : ℂ) =
        ((1 / Real.pi : ℝ) : ℂ) * ((1 / x ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp [Real.pi_ne_zero, positiveX.ne']
  rw [reciprocalRate,
    Complex.mul_cpow_ofReal_nonneg
      (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
      (by positivity : (0 : ℝ) ≤ 1 / x ^ 2)]
  have piArg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact ne_of_lt Real.pi_pos
  rw [show ((1 / Real.pi : ℝ) : ℂ) = (Real.pi : ℂ)⁻¹ by
      push_cast; simp only [one_div],
    Complex.inv_cpow _ _ piArg, ← Complex.cpow_neg]
  have xSquare : ((1 / x ^ 2 : ℝ) : ℂ) = ((x : ℂ) ^ 2)⁻¹ := by
    push_cast
    field_simp [positiveX.ne']
  rw [xSquare, Complex.inv_cpow]
  · rw [← Complex.cpow_neg]
    have xPower : ((x : ℂ) ^ 2) ^ (-(s / 2)) = (x : ℂ) ^ (-s) := by
      rw [show (x : ℂ) ^ 2 = ((x ^ (2 : ℝ) : ℝ) : ℂ) by
        rw [Real.rpow_two]
        norm_num,
        ← Complex.cpow_mul_ofReal_nonneg positiveX.le 2]
      congr 1
      norm_num
      ring
    rw [xPower]
    ring
  · rw [show (x : ℂ) ^ 2 = ((x ^ 2 : ℝ) : ℂ) by norm_num,
      Complex.arg_ofReal_of_nonneg (sq_nonneg x)]
    exact ne_of_lt Real.pi_pos

theorem burnolGaussianMellinScaleKernel_integrableOn
    (s : ℂ) (positiveS : 0 < s.re)
    {rate : ℝ} (positiveRate : 0 < rate) :
    IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (s / 2 - 1) * Complex.exp (-(rate * t)))
      (Ioi 0) := by
  have positiveHalf : 0 < (s / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  let base : ℝ → ℂ := fun u =>
    Complex.exp (-u) * (u : ℂ) ^ (s / 2 - 1)
  have baseIntegrable : IntegrableOn base (Ioi 0) := by
    apply (Complex.GammaIntegral_convergent positiveHalf).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
    unfold base
    push_cast
    ring
  have scaled : IntegrableOn (fun t : ℝ => base (rate * t)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff base 0 positiveRate).mpr (by
      simpa using baseIntegrable)
  let coefficient : ℂ := (rate : ℂ) ^ (-(s / 2 - 1))
  apply (scaled.const_mul coefficient).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positiveT
  unfold base coefficient
  rw [Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg positiveRate.le positiveT.le]
  have ratePowerNe : (rate : ℂ) ^ (s / 2 - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Complex.ofReal_ne_zero.mpr positiveRate.ne')
  rw [Complex.cpow_neg]
  calc
    _ = ((rate : ℂ) ^ (s / 2 - 1))⁻¹ *
        (rate : ℂ) ^ (s / 2 - 1) *
        ((t : ℂ) ^ (s / 2 - 1) * Complex.exp (-(rate * t))) := by ring
    _ = _ := by rw [inv_mul_cancel₀ ratePowerNe, one_mul]

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
