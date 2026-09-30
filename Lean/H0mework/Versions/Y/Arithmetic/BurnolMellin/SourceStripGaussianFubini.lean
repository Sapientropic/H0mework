import H0mework.Arithmetic.BurnolMellin.GaussianSuperpositionKernel
import H0mework.Arithmetic.BurnolMellin.GaussianHeatPair
import H0mework.Versions.Y.Arithmetic.BurnolMellin.SourceStripMellinConvergence

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

def burnolSourceStripGaussianKernel
    (source : burnolCompactAnnulusSource) (w : ℂ)
    (point : ℝ × ℝ) : ℂ :=
  (point.1 : ℂ) ^ (w / 2 - 1) *
    Complex.exp (-(((Real.pi * point.2 ^ 2 : ℝ) : ℂ) * (point.1 : ℂ))) *
      burnolCompactAdditiveCoSum source point.2

def burnolSourceStripGaussianMeasurableKernel
    (source : burnolCompactAnnulusSource) (w : ℂ)
    (point : ℝ × ℝ) : ℂ :=
  Complex.exp (((Real.log point.1 : ℝ) : ℂ) * (w / 2 - 1)) *
    Complex.exp (-(((Real.pi * point.2 ^ 2 : ℝ) : ℂ) * (point.1 : ℂ))) *
      burnolCompactAdditiveCoSum source point.2

theorem burnolSourceStripGaussianMeasurableKernel_measurable
    (source : burnolCompactAnnulusSource) (w : ℂ) :
    Measurable (burnolSourceStripGaussianMeasurableKernel source w) := by
  unfold burnolSourceStripGaussianMeasurableKernel
  have scaleMeasurable : Measurable (fun point : ℝ × ℝ =>
      Complex.exp (((Real.log point.1 : ℝ) : ℂ) * (w / 2 - 1))) :=
    Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp
        (Real.measurable_log.comp measurable_fst)).mul measurable_const)
  have gaussianMeasurable : Measurable (fun point : ℝ × ℝ =>
      Complex.exp (-(((Real.pi * point.2 ^ 2 : ℝ) : ℂ) *
        (point.1 : ℂ)))) := by
    fun_prop
  exact (scaleMeasurable.mul gaussianMeasurable).mul
    ((burnolCompactAdditiveCoSum_measurable source).comp measurable_snd)

theorem burnolSourceStripGaussianKernel_aeStronglyMeasurable
    (source : burnolCompactAnnulusSource) (w : ℂ) :
    AEStronglyMeasurable (burnolSourceStripGaussianKernel source w)
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
  have measurable :=
    (burnolSourceStripGaussianMeasurableKernel_measurable source w).aestronglyMeasurable
      (μ := (volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0)))
  apply measurable.congr
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod measurableSet_Ioi)] with point inside
  unfold burnolSourceStripGaussianKernel
    burnolSourceStripGaussianMeasurableKernel
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr inside.1.ne'),
    ← Complex.ofReal_log inside.1.le]

theorem norm_burnolSourceStripGaussianKernel
    (source : burnolCompactAnnulusSource) (w : ℂ)
    {t x : ℝ} (positiveT : 0 < t) :
    ‖burnolSourceStripGaussianKernel source w (t, x)‖ =
      t ^ (w.re / 2 - 1) * Real.exp (-(Real.pi * x ^ 2 * t)) *
        ‖burnolCompactAdditiveCoSum source x‖ := by
  unfold burnolSourceStripGaussianKernel
  rw [norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos positiveT,
    Complex.norm_exp]
  have exponentRe : (w / 2 - 1).re = w.re / 2 - 1 := by
    rw [Complex.sub_re, Complex.div_re]
    norm_num
    ring
  have gaussianRe :
      (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * (t : ℂ))).re =
        -(Real.pi * x ^ 2 * t) := by
    rw [Complex.neg_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [exponentRe, gaussianRe]

theorem one_div_sq_rpow_half_re_openStrip
    (w : ℂ) {x : ℝ} (positiveX : 0 < x) :
    (1 / x ^ 2) ^ (w.re / 2) = x ^ (-w.re) := by
  rw [one_div,
    Real.rpow_def_of_pos (inv_pos.mpr (sq_pos_of_pos positiveX)),
    Real.rpow_def_of_pos positiveX,
    Real.log_inv, Real.log_pow]
  congr 1
  ring

theorem integral_norm_burnolSourceStripGaussianKernel_eq_weight
    (source : burnolCompactAnnulusSource) (w : ℂ)
    (positiveW : 0 < w.re) {x : ℝ} (positiveX : 0 < x) :
    (∫ t : ℝ in Set.Ioi 0,
      ‖burnolSourceStripGaussianKernel source w (t, x)‖) =
      ((1 / Real.pi) ^ (w.re / 2) * Real.Gamma (w.re / 2)) *
        ‖(x : ℂ) ^ (-w) * burnolCompactAdditiveCoSum source x‖ := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht =>
    norm_burnolSourceStripGaussianKernel source w ht)]
  rw [integral_mul_const,
    Real.integral_rpow_mul_exp_neg_mul_Ioi
      (by linarith : 0 < w.re / 2)
      (mul_pos Real.pi_pos (sq_pos_of_pos positiveX)),
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positiveX]
  simp only [neg_re]
  have baseEq : 1 / (Real.pi * x ^ 2) =
      (1 / Real.pi) * (1 / x ^ 2) := by
    field_simp [Real.pi_ne_zero, positiveX.ne']
  rw [baseEq, Real.mul_rpow (by positivity) (by positivity),
    one_div_sq_rpow_half_re_openStrip w positiveX]
  ring

theorem burnolSourceStripGaussianKernel_integrableOn_scale
    (source : burnolCompactAnnulusSource) (w : ℂ)
    (positiveW : 0 < w.re) {x : ℝ} (positiveX : 0 < x) :
    IntegrableOn (fun t : ℝ =>
      burnolSourceStripGaussianKernel source w (t, x)) (Set.Ioi 0) := by
  change IntegrableOn (fun t : ℝ =>
    ((t : ℂ) ^ (w / 2 - 1) *
      Complex.exp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * (t : ℂ)))) *
        burnolCompactAdditiveCoSum source x) (Set.Ioi 0)
  exact (burnolGaussianMellinScaleKernel_integrableOn
    w positiveW (mul_pos Real.pi_pos (sq_pos_of_pos positiveX))).mul_const
      (burnolCompactAdditiveCoSum source x)

theorem burnolSourceStripGaussianKernel_integrable
    (source : burnolCompactAnnulusSource) (w : ℂ)
    (positiveW : 0 < w.re) (belowOneW : w.re < 1) :
    Integrable (burnolSourceStripGaussianKernel source w)
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
  rw [integrable_prod_iff'
    (burnolSourceStripGaussianKernel_aeStronglyMeasurable source w)]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positiveX
    exact burnolSourceStripGaussianKernel_integrableOn_scale
      source w positiveW positiveX
  · let coefficient : ℝ :=
      (1 / Real.pi) ^ (w.re / 2) * Real.Gamma (w.re / 2)
    have weighted :=
      (burnolCompactAdditiveMellin_integrableOn_strip
        source w positiveW belowOneW).norm.const_mul coefficient
    apply weighted.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positiveX
    symm
    exact integral_norm_burnolSourceStripGaussianKernel_eq_weight
      source w positiveW positiveX

def burnolCompactGaussianHeatPair
    (source : burnolCompactAnnulusSource)
    (scale : ℝ) (positive : 0 < scale) : ℂ :=
  inner ℂ (burnolGaussianL2 scale positive)
    (burnolCompactAdditiveL2 source)

def burnolCompactGaussianHeatPairTotal
    (source : burnolCompactAnnulusSource) (scale : ℝ) : ℂ :=
  if positive : 0 < scale then
    burnolCompactGaussianHeatPair source scale positive
  else 0

def burnolCompactGaussianPositivePair
    (source : burnolCompactAnnulusSource) (scale : ℝ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 0,
    Complex.exp (-Real.pi * scale * x ^ 2) *
      burnolCompactAdditiveCoSum source x

theorem burnolCompactGaussianHeatPair_eq_two_mul_positivePair
    (source : burnolCompactAnnulusSource)
    (scale : ℝ) (positive : 0 < scale) :
    burnolCompactGaussianHeatPair source scale positive =
      2 * burnolCompactGaussianPositivePair source scale := by
  have general := burnolGenericGaussianHeatPair_eq_two_mul_positivePair
    (burnolCompactAdditivePhysicalState source) positive
  rw [burnolGenericGaussianHeatPairTotal, dif_pos positive] at general
  change inner ℂ (burnolGaussianL2 scale positive)
      (burnolCompactAdditiveL2 source) = _
  calc
    _ = 2 * burnolGenericGaussianPositivePair
        (burnolCompactAdditiveL2 source) scale := general
    _ = 2 * burnolCompactGaussianPositivePair source scale := by
      congr 1
      unfold burnolGenericGaussianPositivePair
        burnolCompactGaussianPositivePair
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae
        (burnolCompactAdditiveL2_coeFn source)] with x sourceRead
      rw [sourceRead]
      unfold burnolGaussianRaw
      push_cast
      ring

theorem burnolGenericGaussianHeatPairTotal_compactAdditive
    (source : burnolCompactAnnulusSource) :
    burnolGenericGaussianHeatPairTotal (burnolCompactAdditiveL2 source) =
      burnolCompactGaussianHeatPairTotal source := by
  funext scale
  by_cases positive : 0 < scale
  · rw [burnolGenericGaussianHeatPairTotal, dif_pos positive,
      burnolCompactGaussianHeatPairTotal, dif_pos positive,
      burnolCompactGaussianHeatPair]
  · rw [burnolGenericGaussianHeatPairTotal, dif_neg positive,
      burnolCompactGaussianHeatPairTotal, dif_neg positive]

/-- The exact source-strip Fubini seam.  Its left side is the actual
compact co-Poisson Mellin read; no left-half ambient evaluator is assumed. -/
theorem burnolSourceStripGaussianFubini
    (source : burnolCompactAnnulusSource) (w : ℂ)
    (positiveW : 0 < w.re) (belowOneW : w.re < 1) :
    Gammaℝ w * burnolCompactAdditiveMellinRead source w =
      (1 / 2 : ℂ) * mellin
        (burnolGenericGaussianHeatPairTotal (burnolCompactAdditiveL2 source))
        (w / 2) := by
  rw [burnolGenericGaussianHeatPairTotal_compactAdditive]
  unfold burnolCompactAdditiveMellinRead mellin
  rw [show (∫ t : ℝ in Set.Ioi 0,
      (t : ℂ) ^ (w / 2 - 1) • burnolCompactGaussianHeatPairTotal source t) =
      ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (w / 2 - 1) *
          (2 * burnolCompactGaussianPositivePair source t) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t positiveT
    have positiveT' : 0 < t := positiveT
    simp only [smul_eq_mul]
    rw [burnolCompactGaussianHeatPairTotal, dif_pos positiveT',
      burnolCompactGaussianHeatPair_eq_two_mul_positivePair]]
  unfold burnolCompactGaussianPositivePair
  rw [show (1 / 2 : ℂ) * (∫ t : ℝ in Set.Ioi 0,
      (t : ℂ) ^ (w / 2 - 1) *
        (2 * ∫ x : ℝ in Set.Ioi 0,
          Complex.exp (-Real.pi * t * x ^ 2) *
            burnolCompactAdditiveCoSum source x)) =
      ∫ t : ℝ in Set.Ioi 0, ∫ x : ℝ in Set.Ioi 0,
        burnolSourceStripGaussianKernel source w (t, x) by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change (1 / 2 : ℂ) *
        ((t : ℂ) ^ (w / 2 - 1) *
          (2 * ∫ x : ℝ in Set.Ioi 0,
            Complex.exp (-Real.pi * t * x ^ 2) *
              burnolCompactAdditiveCoSum source x)) =
      ∫ x : ℝ in Set.Ioi 0,
        burnolSourceStripGaussianKernel source w (t, x)
    rw [show (1 / 2 : ℂ) *
        ((t : ℂ) ^ (w / 2 - 1) *
          (2 * ∫ x : ℝ in Set.Ioi 0,
            Complex.exp (-Real.pi * t * x ^ 2) *
              burnolCompactAdditiveCoSum source x)) =
        (t : ℂ) ^ (w / 2 - 1) *
          (∫ x : ℝ in Set.Ioi 0,
            Complex.exp (-Real.pi * t * x ^ 2) *
              burnolCompactAdditiveCoSum source x) by ring,
      ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    unfold burnolSourceStripGaussianKernel
    push_cast
    ring]
  have joint := burnolSourceStripGaussianKernel_integrable
    source w positiveW belowOneW
  rw [← integral_prod _ joint, integral_prod_symm _ joint,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x positiveX
  calc
    Gammaℝ w * ((x : ℂ) ^ (-w) *
        burnolCompactAdditiveCoSum source x) =
      (Gammaℝ w * (x : ℂ) ^ (-w)) *
        burnolCompactAdditiveCoSum source x := by ring
    _ = (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (w / 2 - 1) *
          Complex.exp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * (t : ℂ)))) *
            burnolCompactAdditiveCoSum source x := by
      rw [gammaReal_mul_positive_cpow_neg_eq_gaussianSuperposition
        w positiveW positiveX]
    _ = ∫ t : ℝ in Set.Ioi 0,
        burnolSourceStripGaussianKernel source w (t, x) := by
      rw [← integral_mul_const]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      rfl

end


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
