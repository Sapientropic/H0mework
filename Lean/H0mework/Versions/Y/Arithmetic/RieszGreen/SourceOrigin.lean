import H0mework.Versions.Y.Arithmetic.RieszGreen.SourceOriginEstimate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex Filter FourierTransform MeasureTheory Set
open scoped Topology
open OriginalRieszSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "bRaw" => burnolRieszSingleFourierSourceRaw

theorem gap_fourier_halfWeight_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    ‖(Real.sqrt |x| : ℂ) * burnolGapTailFourierRaw q coordinate x‖ ≤
      (numeratorOriginBound coordinate / (2 * Real.pi)) *
        |x| ^ (originExponent coordinate - 1 / 2) := by
  by_cases zero : x = 0
  · simp only [zero, abs_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul, norm_zero]
    rw [Real.zero_rpow (by linarith [(originExponent_bounds coordinate).1]), mul_zero]
  have positive : 0 < |x| := abs_pos.mpr zero
  have scalarPositive : 0 < 2 * Real.pi * |x| := by positivity
  have powers : Real.sqrt |x| * |x| ^ originExponent coordinate =
      |x| ^ (originExponent coordinate - 1 / 2) * |x| := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add positive]
    calc
      _ = |x| ^ ((originExponent coordinate - 1 / 2) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add positive, Real.rpow_one]
  have read : ‖(Real.sqrt |x| : ℂ) * burnolGapTailFourierRaw q coordinate x‖ =
      (Real.sqrt |x| / (2 * Real.pi * |x|)) * ‖burnolGapTailFourierNumerator q coordinate x‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg |x|),
      burnolGapTailFourierRaw, norm_div, Complex.norm_ofNat, Complex.norm_I, mul_one,
      abs_of_pos Real.pi_pos]
    ring
  rw [read]
  calc
    _ ≤ (Real.sqrt |x| / (2 * Real.pi * |x|)) *
        (numeratorOriginBound coordinate * |x| ^ originExponent coordinate) :=
      mul_le_mul_of_nonneg_left (numerator_origin_holder coordinate x) (by positivity)
    _ = numeratorOriginBound coordinate * (Real.sqrt |x| * |x| ^ originExponent coordinate) /
        (2 * Real.pi * |x|) := by ring
    _ = numeratorOriginBound coordinate * (|x| ^ (originExponent coordinate - 1 / 2) * |x|) /
        (2 * Real.pi * |x|) := by rw [powers]
    _ = _ := by field_simp

theorem halfWeight_origin :
    Tendsto (fun x : ℝ => (Real.sqrt |x| : ℂ)) (𝓝 0) (𝓝 0) := by
  simpa only [Function.comp_def, abs_zero, Real.sqrt_zero, Complex.ofReal_zero] using
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_abs)).tendsto (0 : ℝ)

theorem gap_fourier_halfWeight_origin (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun x : ℝ => (Real.sqrt |x| : ℂ) * burnolGapTailFourierRaw q coordinate x)
      (𝓝 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have powerPositive : 0 < originExponent coordinate - 1 / 2 := by
    linarith [(originExponent_bounds coordinate).1]
  have boundLimit : Tendsto (fun x : ℝ =>
      (numeratorOriginBound coordinate / (2 * Real.pi)) *
        |x| ^ (originExponent coordinate - 1 / 2)) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, abs_zero, Real.zero_rpow powerPositive.ne', mul_zero] using
      (((Real.continuous_rpow_const powerPositive.le).comp continuous_abs).tendsto (0 : ℝ)).const_mul
        (numeratorOriginBound coordinate / (2 * Real.pi))
  exact squeeze_zero (fun x => norm_nonneg _) (gap_fourier_halfWeight_bound coordinate) boundLimit

theorem forcing_halfWeight_origin (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun x : ℝ => (Real.sqrt |x| : ℂ) * burnolRieszFourierForcingRaw coordinate x)
      (𝓝 0) (𝓝 0) := by
  have reflected : Tendsto (fun x : ℝ =>
      (Real.sqrt |x| : ℂ) * burnolGapTailFourierRaw q coordinate (-x)) (𝓝 0) (𝓝 0) := by
    have negative : Tendsto (fun x : ℝ => -x) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using (continuous_neg.tendsto (0 : ℝ))
    simpa only [Function.comp_def, abs_neg] using (gap_fourier_halfWeight_origin coordinate).comp negative
  have result := ((gap_fourier_halfWeight_origin coordinate).add reflected).const_mul (1 / 2 : ℂ)
  have subtracted := result.sub (halfWeight_origin.mul_const (Translator.ForcingMeanZero.mean coordinate))
  simp only [zero_add, mul_zero, zero_mul, sub_zero] at subtracted
  apply subtracted.congr
  intro x
  rw [Translator.ForcingMeanZero.forcingRaw_eq]
  unfold Translator.ForcingWhole.raw burnolEvenRaw
  ring

/-- The original singular forcing and the original smooth return generate the two-sided limit. -/
theorem source_halfWeight_origin (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun x : ℝ => (Real.sqrt |x| : ℂ) * bRaw coordinate x) (𝓝 0) (𝓝 0) := by
  have smooth := halfWeight_origin.mul ((Constructor.secondReturnRaw_continuous coordinate).tendsto (0 : ℝ))
  simp only [zero_mul] at smooth
  have combined := (forcing_halfWeight_origin coordinate).add smooth
  simp only [zero_add] at combined
  apply combined.congr
  intro x
  change _ = (Real.sqrt |x| : ℂ) * (burnolRieszFourierForcingRaw coordinate x + Constructor.secondReturnRaw coordinate x)
  ring

/-- No value, regularity, or trace certificate at zero is supplied by the caller. -/
theorem source_cross_origin (left right : BurnolCompletedMellinCoordinate) :
    Tendsto (fun x : ℝ => (x : ℂ) * star (bRaw left x) * bRaw right x) (𝓝 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have product := (source_halfWeight_origin left).star.mul (source_halfWeight_origin right)
  have normLimit := product.norm
  simp only [star_zero, zero_mul, norm_zero] at normLimit
  apply normLimit.congr
  intro x
  calc
    ‖star ((Real.sqrt |x| : ℂ) * bRaw left x) * ((Real.sqrt |x| : ℂ) * bRaw right x)‖ =
        (Real.sqrt |x|) ^ 2 * ‖bRaw left x‖ * ‖bRaw right x‖ := by
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg |x|)]
      ring
    _ = _ := by
      rw [Real.sq_sqrt (abs_nonneg x)]
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
