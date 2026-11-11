import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Pair
import H0mework.Versions.R7e4da746.Arithmetic.BurnolMellin.SourceStripGaussianFubini

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Mellin.EvenGaussian
open Complex FourierTransform MeasureTheory Set BurnolPhysicalState
open scoped ENNReal InnerProductSpace

private theorem heat_positive (value : BurnolL2) (even : reflectL2 value = value)
    {scale : ℝ} (positive : 0 < scale) :
    burnolGenericGaussianHeatPairTotal value scale =
      2 * burnolGenericGaussianPositivePair value scale := by
  rw [burnolGenericGaussianHeatPairTotal, dif_pos positive,
    inner_burnolGaussianL2_eq_integral]
  let raw : ℝ → ℂ := fun x => value x * burnolGaussianRaw scale x
  have rawIntegrable : Integrable raw := by
    exact (L2.integrable_inner (burnolGaussianL2 scale positive) value).congr (by
      filter_upwards [burnolGaussianL2_coeFn scale positive] with x gaussian
      rw [gaussian, RCLike.inner_apply, starRingEnd_apply, star_burnolGaussianRaw])
  have valueEven : ∀ᵐ x ∂volume, value (-x) = value x := by
    filter_upwards [Lp.coeFn_compMeasurePreserving value negMeasurePreserving]
      with x reflection
    calc
      value (-x) = reflectL2 value x := reflection.symm
      _ = value x := congrArg (fun state : BurnolL2 => state x) even
  have negative : (∫ x : ℝ in Iic 0, raw x) = ∫ x : ℝ in Ioi 0, raw x := by
    calc
      _ = ∫ x : ℝ in Iic 0, raw (-x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae valueEven] with x valueRead
        unfold raw
        rw [valueRead]
        congr 1
        simp [burnolGaussianRaw]
      _ = _ := by simpa only [neg_zero] using integral_comp_neg_Iic 0 raw
  change (∫ x : ℝ, raw x) = _
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      rawIntegrable.integrableOn rawIntegrable.integrableOn, negative]
  unfold burnolGenericGaussianPositivePair
  ring

private theorem heat_fourier (value : BurnolL2) (scale : ℝ) :
    burnolGenericGaussianHeatPairTotal (fourierL2 value) scale =
      (scale : ℂ) ^ (-(1 / 2 : ℂ)) *
        burnolGenericGaussianHeatPairTotal value scale⁻¹ := by
  by_cases positive : 0 < scale
  · rw [burnolGenericGaussianHeatPairTotal, dif_pos positive,
      inner_burnolGaussianL2_eq_integral,
      burnolGaussian_fourierL2_pairing value positive,
      burnolGenericGaussianHeatPairTotal, dif_pos (inv_pos.mpr positive),
      inner_burnolGaussianL2_eq_integral,
      burnolGaussianReciprocalScale_eq_cpow_neg_half positive]
  · have inverseNonpositive : ¬0 < scale⁻¹ :=
      not_lt_of_ge (inv_nonpos.mpr (le_of_not_gt positive))
    rw [burnolGenericGaussianHeatPairTotal, dif_neg positive,
      burnolGenericGaussianHeatPairTotal, dif_neg inverseNonpositive, mul_zero]

private theorem heat_homogeneous (value : BurnolL2) (w : ℂ) :
    mellin (burnolGenericGaussianHeatPairTotal (fourierL2 value)) (w / 2) =
      mellin (burnolGenericGaussianHeatPairTotal value) ((1 - w) / 2) := by
  rw [show burnolGenericGaussianHeatPairTotal (fourierL2 value) =
      fun scale : ℝ => (scale : ℂ) ^ (-(1 / 2 : ℂ)) •
        burnolGenericGaussianHeatPairTotal value scale⁻¹ by
    funext scale
    simpa only [smul_eq_mul] using heat_fourier value scale]
  rw [mellin_cpow_smul, mellin_comp_inv]
  congr 2
  ring

private def kernel (value : BurnolL2) (w : ℂ) (point : ℝ × ℝ) : ℂ :=
  (point.1 : ℂ) ^ (w / 2 - 1) *
    Complex.exp (-(((Real.pi * point.2 ^ 2 : ℝ) : ℂ) * (point.1 : ℂ))) *
      value point.2

private theorem kernel_measurable (value : BurnolL2) (w : ℂ) :
    AEStronglyMeasurable (kernel value w)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let scalar : ℝ × ℝ → ℂ := fun point =>
    Complex.exp (((Real.log point.1 : ℝ) : ℂ) * (w / 2 - 1)) *
      Complex.exp (-(((Real.pi * point.2 ^ 2 : ℝ) : ℂ) * (point.1 : ℂ)))
  have scalarMeasurable : Measurable scalar := by
    have scaleMeasurable : Measurable (fun point : ℝ × ℝ =>
        Complex.exp (((Real.log point.1 : ℝ) : ℂ) * (w / 2 - 1))) :=
      Complex.continuous_exp.measurable.comp
        ((Complex.measurable_ofReal.comp
          (Real.measurable_log.comp measurable_fst)).mul measurable_const)
    exact scaleMeasurable.mul (by fun_prop)
  have valueAES : AEStronglyMeasurable (fun point : ℝ × ℝ => value point.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    (Lp.aestronglyMeasurable value).restrict.comp_snd
  apply (scalarMeasurable.aestronglyMeasurable.mul valueAES).congr
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)]
    with point inside
  unfold kernel scalar
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr inside.1.ne'),
    ← Complex.ofReal_log inside.1.le]
  rfl

private theorem kernel_norm (value : BurnolL2) (w : ℂ)
    {t x : ℝ} (positiveT : 0 < t) :
    ‖kernel value w (t, x)‖ = t ^ (w.re / 2 - 1) *
      Real.exp (-(Real.pi * x ^ 2 * t)) * ‖value x‖ := by
  unfold kernel
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positiveT,
    Complex.norm_exp]
  have exponentRe : (w / 2 - 1).re = w.re / 2 - 1 := by
    rw [Complex.sub_re, Complex.div_re]
    norm_num
    ring
  have gaussianRe : (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * (t : ℂ))).re =
      -(Real.pi * x ^ 2 * t) := by
    rw [Complex.neg_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [exponentRe, gaussianRe]

private theorem kernel_norm_integral (value : BurnolL2) (w : ℂ)
    (positiveW : 0 < w.re) {x : ℝ} (positiveX : 0 < x) :
    (∫ t : ℝ in Ioi 0, ‖kernel value w (t, x)‖) =
      ((1 / Real.pi) ^ (w.re / 2) * Real.Gamma (w.re / 2)) *
        ‖(x : ℂ) ^ (-w) * value x‖ := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => kernel_norm value w ht),
    integral_mul_const, Real.integral_rpow_mul_exp_neg_mul_Ioi
      (by linarith : 0 < w.re / 2) (mul_pos Real.pi_pos (sq_pos_of_pos positiveX)),
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positiveX]
  simp only [neg_re]
  have baseEq : 1 / (Real.pi * x ^ 2) = (1 / Real.pi) * (1 / x ^ 2) := by
    field_simp [Real.pi_ne_zero, positiveX.ne']
  rw [baseEq, Real.mul_rpow (by positivity) (by positivity),
    one_div_sq_rpow_half_re_openStrip w positiveX]
  ring

private theorem kernel_scale_integrable (value : BurnolL2) (w : ℂ)
    (positiveW : 0 < w.re) {x : ℝ} (positiveX : 0 < x) :
    IntegrableOn (fun t : ℝ => kernel value w (t, x)) (Ioi 0) :=
  (burnolGaussianMellinScaleKernel_integrableOn w positiveW
    (mul_pos Real.pi_pos (sq_pos_of_pos positiveX))).mul_const (value x)

private theorem kernel_integrable (value : BurnolL2) (w : ℂ)
    (positiveW : 0 < w.re)
    (weighted : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-w) * value x) (Ioi 0)) :
    Integrable (kernel value w)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  rw [integrable_prod_iff' (kernel_measurable value w)]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positiveX
    exact kernel_scale_integrable value w positiveW positiveX
  · apply (weighted.norm.const_mul
      ((1 / Real.pi) ^ (w.re / 2) * Real.Gamma (w.re / 2))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positiveX
    exact (kernel_norm_integral value w positiveW positiveX).symm

/-- Gaussian superposition on an even L² vector, using its ordinary weighted integral. -/
theorem actual_gaussian_fubini (value : BurnolL2) (even : reflectL2 value = value)
    (w : ℂ) (positiveW : 0 < w.re)
    (weighted : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-w) * value x) (Ioi 0)) :
    Gammaℝ w * mellin (value : ℝ → ℂ) (1 - w) =
      (1 / 2 : ℂ) * mellin (burnolGenericGaussianHeatPairTotal value) (w / 2) := by
  unfold mellin
  simp only [show 1 - w - 1 = -w by ring, smul_eq_mul]
  rw [show (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (w / 2 - 1) * burnolGenericGaussianHeatPairTotal value t) =
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (w / 2 - 1) *
        (2 * burnolGenericGaussianPositivePair value t) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t positiveT
    dsimp only
    rw [heat_positive value even positiveT]]
  unfold burnolGenericGaussianPositivePair
  rw [show (1 / 2 : ℂ) * (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (w / 2 - 1) *
        (2 * ∫ x : ℝ in Ioi 0, value x * burnolGaussianRaw t x)) =
      ∫ t : ℝ in Ioi 0, ∫ x : ℝ in Ioi 0, kernel value w (t, x) by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [show (1 / 2 : ℂ) * ((t : ℂ) ^ (w / 2 - 1) *
        (2 * ∫ x : ℝ in Ioi 0, value x * burnolGaussianRaw t x)) =
        (t : ℂ) ^ (w / 2 - 1) *
          (∫ x : ℝ in Ioi 0, value x * burnolGaussianRaw t x) by ring,
      ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    unfold kernel burnolGaussianRaw
    push_cast
    ring]
  have joint := kernel_integrable value w positiveW weighted
  rw [← integral_prod _ joint, integral_prod_symm _ joint, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x positiveX
  calc
    Gammaℝ w * ((x : ℂ) ^ (-w) * value x) =
      (Gammaℝ w * (x : ℂ) ^ (-w)) * value x := by ring
    _ = (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (w / 2 - 1) *
        Complex.exp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * (t : ℂ)))) * value x := by
      rw [gammaReal_mul_positive_cpow_neg_eq_gaussianSuperposition w positiveW positiveX]
    _ = ∫ t : ℝ in Ioi 0, kernel value w (t, x) := by
      rw [← integral_mul_const]
      rfl

/-- Both integrability inputs are ordinary Mellin domains of the same L² Fourier pair. -/
theorem actual_fourier_mellin_weighted (value : BurnolL2)
    (even : reflectL2 value = value) (w : ℂ)
    (positiveW : 0 < w.re) (belowOneW : w.re < 1)
    (position : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-w) * value x) (Ioi 0))
    (frequency : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (w - 1) * fourierL2 value x) (Ioi 0)) :
    mellin (fourierL2 value : ℝ → ℂ) w =
      (Gammaℝ w / Gammaℝ (1 - w)) * mellin (value : ℝ → ℂ) (1 - w) := by
  have dualPositive : 0 < (1 - w).re := by simpa using sub_pos.mpr belowOneW
  have fourierEven : reflectL2 (fourierL2 value) = fourierL2 value := by
    rw [← fourierL2_reflectL2_commute, even]
  have first := actual_gaussian_fubini value even w positiveW position
  have second := actual_gaussian_fubini (fourierL2 value) fourierEven (1 - w)
    dualPositive (by simpa only [show -(1 - w) = w - 1 by ring] using frequency)
  rw [show 1 - (1 - w) = w by ring, heat_homogeneous value (1 - w),
    show 1 - (1 - w) = w by ring] at second
  have balance : Gammaℝ (1 - w) * mellin (fourierL2 value : ℝ → ℂ) w =
      Gammaℝ w * mellin (value : ℝ → ℂ) (1 - w) := second.trans first.symm
  have gammaNe := Gammaℝ_ne_zero_of_re_pos dualPositive
  apply (mul_left_cancel₀ gammaNe)
  rw [balance]
  field_simp

theorem actual_fourier_mellin (value : BurnolL2) (even : reflectL2 value = value)
    (w : ℂ) (positiveW : 0 < w.re) (belowOneW : w.re < 1)
    (position : MellinConvergent (value : ℝ → ℂ) (1 - w))
    (frequency : MellinConvergent (fourierL2 value : ℝ → ℂ) w) :
    mellin (fourierL2 value : ℝ → ℂ) w =
      (Gammaℝ w / Gammaℝ (1 - w)) * mellin (value : ℝ → ℂ) (1 - w) := by
  apply actual_fourier_mellin_weighted value even w positiveW belowOneW
  · simpa only [MellinConvergent, show 1 - w - 1 = -w by ring, smul_eq_mul] using position
  · simpa only [MellinConvergent, smul_eq_mul] using frequency

end OriginalKElementaryArithmeticAction.PeriodicPower.Mellin.EvenGaussian
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
