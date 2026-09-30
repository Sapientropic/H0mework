import H0mework.Arithmetic.MellinTateSource.TateCompact
import H0mework.Arithmetic.MobiusSource.MobiusReciprocalPairing

/-! # Full Fourier pairing of a compact source and its Tate reciprocal -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set Filter
open scoped SchwartzMap ContDiff

noncomputable section

private theorem fourier_zero_eq_integral (test : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier test 0 = ∫ t : ℝ, test t := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp

private theorem integral_fourier_eq_zero_value (test : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, FourierTransform.fourier test t) = test 0 := by
  rw [← fourier_zero_eq_integral (FourierTransform.fourier test)]
  simpa using sonine_fourier_fourier_apply test 0

private def burnolCompactForward (source : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℂ)⁻¹ * source (t / (n + 1 : ℕ))

/-- Full Schwartz pairing for the actual compact source and its Tate
reciprocal. Both constant modes are retained. -/
theorem burnolCompactFourier_pairing
    (source : burnolCompactAnnulusSource) (test : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, FourierTransform.fourier test t *
        burnolCompactAdditiveCoSum source t) =
      ∫ t : ℝ, test t *
        burnolCompactAdditiveCoSum
          (burnolCompactTateReciprocalSource source) t := by
  let reciprocal := burnolCompactTateReciprocalSource source
  let h : ℝ → ℂ := burnolCompactAdditiveSource source
  let g : ℝ → ℂ := fun u ↦ source.1 u
  let forwardH : ℝ → ℂ := burnolCompactForward h
  let forwardG : ℝ → ℂ := burnolCompactForward g
  let normalG := burnolCompactAdditiveNormalization source
  let normalH := burnolCompactAdditiveNormalization reciprocal
  have hMeasurable : Measurable h := burnolCompactAdditiveSource_measurable source
  have hZero : h 0 = 0 := by
    exact burnolCompactAdditiveSource_zero_of_abs_le_quarter source (by norm_num)
  have hEven : ∀ u, h (-u) = h u := burnolCompactAdditiveSource_even source
  have hWeighted : Integrable (fun u : ℝ ↦ ‖h u‖ / |u| ^ 3) := by
    simpa only [reciprocal, h, burnolCompactTateReciprocalSource,
      burnolCompactTateReciprocalSchwartz_apply] using
        burnolCompactAnnulusSource_norm_div_abs_cube_integrable reciprocal
  have gMeasurable : Measurable g := source.1.continuous.measurable
  have gZero : g 0 = 0 := source.2.2.1 0 (by norm_num)
  have gEven : ∀ u, g (-u) = g u := source.2.1
  have gWeighted : Integrable (fun u : ℝ ↦ ‖g u‖ / |u| ^ 3) := by
    simpa only [g] using
      burnolCompactAnnulusSource_norm_div_abs_cube_integrable source
  have readH := MobiusSourceFourierPairing.integral_forward_eq_positiveTheta
    h hMeasurable hZero hEven hWeighted test
  rw [MobiusSourceFourierPairing.integral_positiveTheta_eq_reciprocal] at readH
  have readH' :
      (∫ t : ℝ, FourierTransform.fourier test t * forwardH t) =
        ∫ u : ℝ in Ioi 0, g u *
          (coPoissonMuntzTheta test u -
            (u : ℂ)⁻¹ * FourierTransform.fourier test 0) := by
    calc
      _ = ∫ u : ℝ in Ioi 0, (((|u| : ℝ) : ℂ)⁻¹ * h u⁻¹) *
          (coPoissonMuntzTheta test u -
            (u : ℂ)⁻¹ * FourierTransform.fourier test 0) := by
        simpa only [forwardH, burnolCompactForward] using readH
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        have factor : (((|u| : ℝ) : ℂ)⁻¹ * h u⁻¹) = g u := by
          calc
            _ = burnolCompactAdditiveSource reciprocal u := by
              rw [burnolCompactAdditiveSource, if_neg hu.ne']
              congr 2
            _ = g u := burnolCompactTateReciprocalSource_additiveSource source u
        change ((((|u| : ℝ) : ℂ)⁻¹ * h u⁻¹) *
            (coPoissonMuntzTheta test u -
              (u : ℂ)⁻¹ * FourierTransform.fourier test 0)) =
          g u * (coPoissonMuntzTheta test u -
            (u : ℂ)⁻¹ * FourierTransform.fourier test 0)
        rw [factor]
  have readG := MobiusSourceFourierPairing.integral_forward_eq_positiveTheta
    g gMeasurable gZero gEven gWeighted (FourierTransform.fourierInv test)
  have readG' :
      (∫ t : ℝ, test t * forwardG t) =
        ∫ u : ℝ in Ioi 0, g u * coPoissonMuntzThetaNonzero test u := by
    simpa only [forwardG, burnolCompactForward,
      FourierTransform.fourier_fourierInv_eq] using readG
  have thetaIntegrable : IntegrableOn (fun u : ℝ ↦
      g u * coPoissonMuntzThetaNonzero test u) (Ioi 0) := by
    simpa only [FourierTransform.fourier_fourierInv_eq] using
      MobiusSourceFourierPairing.positiveTheta_integrable
        g gMeasurable gZero gEven gWeighted (FourierTransform.fourierInv test)
  have gIntegrable : IntegrableOn g (Ioi 0) := source.1.integrable.integrableOn
  have inverseGIntegrable : IntegrableOn (fun u : ℝ ↦
      (u : ℂ)⁻¹ * g u) (Ioi 0) := by
    simpa only [g] using
      (burnolCompactAnnulusSource_inv_mul_integrable source).integrableOn
  have gMoment : (∫ u : ℝ in Ioi 0, g u) = normalG := by
    simpa only [g, normalG, burnolCompactAdditiveNormalization] using
      burnolCompactAnnulusSource_positiveIntegral_eq_half source
  have inverseGMoment : (∫ u : ℝ in Ioi 0,
      (u : ℂ)⁻¹ * g u) = normalH := by
    simpa only [g, normalH, reciprocal] using
      burnolCompactTateReciprocalSource_reciprocalMoment source
  have reciprocalExpansion :
      (∫ u : ℝ in Ioi 0, g u *
          (coPoissonMuntzTheta test u -
            (u : ℂ)⁻¹ * FourierTransform.fourier test 0)) =
        (∫ u : ℝ in Ioi 0,
          g u * coPoissonMuntzThetaNonzero test u) +
          test 0 * normalG - FourierTransform.fourier test 0 * normalH := by
    calc
      _ = ∫ u : ℝ in Ioi 0,
          (g u * coPoissonMuntzThetaNonzero test u + test 0 * g u) -
            FourierTransform.fourier test 0 * ((u : ℂ)⁻¹ * g u) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _
        simp only [coPoissonMuntzTheta]
        ring
      _ = (∫ u : ℝ in Ioi 0,
          g u * coPoissonMuntzThetaNonzero test u + test 0 * g u) -
          ∫ u : ℝ in Ioi 0,
            FourierTransform.fourier test 0 * ((u : ℂ)⁻¹ * g u) := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_sub (μ := volume.restrict (Ioi (0 : ℝ)))
            (thetaIntegrable.add (gIntegrable.const_mul _))
            (inverseGIntegrable.const_mul _)
      _ = ((∫ u : ℝ in Ioi 0,
          g u * coPoissonMuntzThetaNonzero test u) +
          ∫ u : ℝ in Ioi 0, test 0 * g u) -
          ∫ u : ℝ in Ioi 0,
            FourierTransform.fourier test 0 * ((u : ℂ)⁻¹ * g u) := by
        rw [integral_add thetaIntegrable (gIntegrable.const_mul _)]
      _ = _ := by
        rw [integral_const_mul, integral_const_mul, gMoment, inverseGMoment]
  have originalProduct : Integrable (fun t : ℝ ↦
      FourierTransform.fourier test t * burnolCompactAdditiveCoSum source t) :=
    ((FourierTransform.fourier test).memLp 2 volume).integrable_mul
      (burnolCompactAdditiveCoSum_memLp_full source)
  have originalConstant : Integrable (fun t : ℝ ↦
      normalG * FourierTransform.fourier test t) :=
    (FourierTransform.fourier test).integrable.const_mul normalG
  have forwardHIntegrable : Integrable (fun t : ℝ ↦
      FourierTransform.fourier test t * forwardH t) := by
    refine (originalProduct.add originalConstant).congr (ae_of_all volume fun t ↦ ?_)
    change FourierTransform.fourier test t * (forwardH t - normalG) +
      normalG * FourierTransform.fourier test t =
        FourierTransform.fourier test t * forwardH t
    ring
  have originalExpansion :
      (∫ t : ℝ, FourierTransform.fourier test t *
          burnolCompactAdditiveCoSum source t) =
        (∫ t : ℝ, FourierTransform.fourier test t * forwardH t) -
          normalG * test 0 := by
    calc
      _ = ∫ t : ℝ, FourierTransform.fourier test t * forwardH t -
          normalG * FourierTransform.fourier test t := by
        apply integral_congr_ae
        filter_upwards with t
        change FourierTransform.fourier test t * (forwardH t - normalG) =
          FourierTransform.fourier test t * forwardH t -
            normalG * FourierTransform.fourier test t
        ring
      _ = _ := by
        rw [integral_sub forwardHIntegrable originalConstant,
          integral_const_mul, integral_fourier_eq_zero_value]
  have targetProduct : Integrable (fun t : ℝ ↦ test t *
      burnolCompactAdditiveCoSum reciprocal t) :=
    (test.memLp 2 volume).integrable_mul
      (burnolCompactAdditiveCoSum_memLp_full reciprocal)
  have targetConstant : Integrable (fun t : ℝ ↦ normalH * test t) :=
    test.integrable.const_mul normalH
  have reciprocalCoSum (t : ℝ) :
      burnolCompactAdditiveCoSum reciprocal t = forwardG t - normalH := by
    rw [burnolCompactAdditiveCoSum]
    congr 1
    apply tsum_congr
    intro n
    rw [burnolCompactTateReciprocalSource_additiveSource]
  have forwardGIntegrable : Integrable (fun t : ℝ ↦ test t * forwardG t) := by
    refine (targetProduct.add targetConstant).congr (ae_of_all volume fun t ↦ ?_)
    change test t * burnolCompactAdditiveCoSum reciprocal t + normalH * test t =
      test t * forwardG t
    rw [reciprocalCoSum]
    ring
  have targetExpansion :
      (∫ t : ℝ, test t * burnolCompactAdditiveCoSum reciprocal t) =
        (∫ t : ℝ, test t * forwardG t) -
          normalH * FourierTransform.fourier test 0 := by
    calc
      _ = ∫ t : ℝ, test t * forwardG t - normalH * test t := by
        apply integral_congr_ae
        filter_upwards with t
        rw [reciprocalCoSum]
        ring
      _ = _ := by
        rw [integral_sub forwardGIntegrable targetConstant,
          integral_const_mul, fourier_zero_eq_integral]
  rw [originalExpansion, readH', reciprocalExpansion, ← readG', targetExpansion]
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
