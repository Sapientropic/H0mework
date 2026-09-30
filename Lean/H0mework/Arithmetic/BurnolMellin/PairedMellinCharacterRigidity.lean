import H0mework.Arithmetic.BurnolMellin.PairedMellinCharacter

/-! # Source-neutral rigidity of the paired Mellin character -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex

noncomputable section

theorem reciprocalMellinTranslationCharacter_eq_negativeShift
    (coordinate : ℂ) (shift : ℝ) :
    reciprocalMellinTranslationCharacter coordinate shift =
      fullMellinTranslationCharacter coordinate (-shift) := by
  unfold reciprocalMellinTranslationCharacter fullMellinTranslationCharacter
  congr 1
  push_cast
  ring

theorem pairedMellinTranslationCharacter_eq_cosh
    (coordinate : ℂ) (shift : ℝ) :
    pairedMellinTranslationCharacter coordinate shift =
      Complex.cosh (((1 / 2 : ℂ) - coordinate) * (shift : ℂ)) := by
  unfold pairedMellinTranslationCharacter fullMellinTranslationCharacter
    reciprocalMellinTranslationCharacter
  have reciprocalExponent :
      (coordinate - (1 / 2 : ℂ)) * (shift : ℂ) =
        -(((1 / 2 : ℂ) - coordinate) * (shift : ℂ)) := by
    ring
  rw [reciprocalExponent, ← Complex.two_cosh]
  ring

theorem complexCosh_re_formula (value : ℂ) :
    (Complex.cosh value).re =
      Real.cosh value.re * Real.cos value.im := by
  conv_lhs => rw [← Complex.re_add_im value]
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.cosh_ofReal_re,
    Complex.cosh_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, mul_one]

theorem complexCosh_im_formula (value : ℂ) :
    (Complex.cosh value).im =
      Real.sinh value.re * Real.sin value.im := by
  conv_lhs => rw [← Complex.re_add_im value]
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp only [Complex.add_im, Complex.mul_im, Complex.cosh_ofReal_re,
    Complex.cosh_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, add_zero, zero_add, mul_one]

theorem complexCosh_re_eq_zero_of_im_eq_zero_norm_le_one
    (value : ℂ) (realValue : (Complex.cosh value).im = 0)
    (contractive : ‖Complex.cosh value‖ ≤ 1) :
    value.re = 0 := by
  by_contra realNonzero
  have sinhNonzero : Real.sinh value.re ≠ 0 :=
    (Real.sinh_ne_zero).mpr realNonzero
  have sinZero : Real.sin value.im = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left sinhNonzero
    rw [← complexCosh_im_formula value]
    exact realValue
  rcases (Real.sin_eq_zero_iff_cos_eq.mp sinZero) with cosOne | cosNegOne
  · have valueEq : Complex.cosh value = (Real.cosh value.re : ℂ) := by
      apply Complex.ext
      · rw [complexCosh_re_formula, cosOne, mul_one]
        rfl
      · simpa using realValue
    have normEq : ‖Complex.cosh value‖ = Real.cosh value.re := by
      rw [valueEq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.cosh_pos value.re)]
    rw [normEq] at contractive
    exact (not_lt_of_ge contractive) ((Real.one_lt_cosh).mpr realNonzero)
  · have valueEq : Complex.cosh value = -(Real.cosh value.re : ℂ) := by
      apply Complex.ext
      · rw [complexCosh_re_formula, cosNegOne, mul_neg]
        simp
      · simpa using realValue
    have normEq : ‖Complex.cosh value‖ = Real.cosh value.re := by
      rw [valueEq, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.cosh_pos value.re)]
    rw [normEq] at contractive
    exact (not_lt_of_ge contractive) ((Real.one_lt_cosh).mpr realNonzero)

/-- At a nonzero log shift, realness and contractivity force the neutral
half-density line. -/
theorem pairedMellinTranslationCharacter_rigidity
    (coordinate : ℂ) (shift : ℝ) (shiftNonzero : shift ≠ 0)
    (realCharacter :
      (pairedMellinTranslationCharacter coordinate shift).im = 0)
    (contractive :
      ‖pairedMellinTranslationCharacter coordinate shift‖ ≤ 1) :
    coordinate.re = 1 / 2 := by
  let exponent : ℂ :=
    ((1 / 2 : ℂ) - coordinate) * (shift : ℂ)
  have exponentRealZero : exponent.re = 0 := by
    apply complexCosh_re_eq_zero_of_im_eq_zero_norm_le_one exponent
    · simpa [exponent, pairedMellinTranslationCharacter_eq_cosh] using
        realCharacter
    · simpa [exponent, pairedMellinTranslationCharacter_eq_cosh] using
        contractive
  have productZero : ((1 / 2 : ℝ) - coordinate.re) * shift = 0 := by
    simpa [exponent] using exponentRealZero
  rcases mul_eq_zero.mp productZero with centered | shiftZero
  · linarith
  · exact False.elim (shiftNonzero shiftZero)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
