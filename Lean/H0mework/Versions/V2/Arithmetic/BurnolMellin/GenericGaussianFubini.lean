import H0mework.Arithmetic.BurnolMellin.GaussianSuperpositionKernel
import H0mework.Arithmetic.BurnolMellin.GaussianHeatPair
import H0mework.Versions.V2.Arithmetic.BurnolMellin.GenericPhysicalMellinRead

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

def burnolGaussianMellinSafeScalePower
    (coordinate : BurnolCompletedMellinCoordinate) (t : ℝ) : ℂ :=
  Complex.exp (((Real.log t : ℝ) : ℂ) * (coordinate.value / 2 - 1))

theorem burnolGaussianMellinSafeScalePower_eq_cpow
    (coordinate : BurnolCompletedMellinCoordinate)
    {t : ℝ} (positive : 0 < t) :
    burnolGaussianMellinSafeScalePower coordinate t =
      (t : ℂ) ^ (coordinate.value / 2 - 1) := by
  unfold burnolGaussianMellinSafeScalePower
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr positive.ne')]
  rw [← Complex.ofReal_log positive.le]

theorem one_div_sq_rpow_half_re
    (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (positiveX : 0 < x) :
    (1 / x ^ 2) ^ (coordinate.value.re / 2) =
      x ^ (-coordinate.value.re) := by
  rw [one_div,
    Real.rpow_def_of_pos (inv_pos.mpr (sq_pos_of_pos positiveX)),
    Real.rpow_def_of_pos positiveX,
    Real.log_inv, Real.log_pow]
  congr 1
  ring

def burnolGenericGaussianMellinKernel
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate)
    (point : ℝ × ℝ) : ℂ :=
  (point.1 : ℂ) ^ (coordinate.value / 2 - 1) *
    burnolGaussianRaw point.1 point.2 * (value : BurnolL2) point.2

def burnolGenericGaussianMellinMeasurableScalar
    (coordinate : BurnolCompletedMellinCoordinate)
    (point : ℝ × ℝ) : ℂ :=
  burnolGaussianMellinSafeScalePower coordinate point.1 *
    burnolGaussianRaw point.1 point.2

theorem burnolGenericGaussianMellinMeasurableScalar_measurable
    (coordinate : BurnolCompletedMellinCoordinate) :
    Measurable (burnolGenericGaussianMellinMeasurableScalar coordinate) := by
  unfold burnolGenericGaussianMellinMeasurableScalar
    burnolGaussianMellinSafeScalePower burnolGaussianRaw
  have scaleMeasurable : Measurable (fun point : ℝ × ℝ =>
      Complex.exp (((Real.log point.1 : ℝ) : ℂ) *
        (coordinate.value / 2 - 1))) :=
    Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp
        (Real.measurable_log.comp measurable_fst)).mul measurable_const)
  have gaussianMeasurable : Measurable (fun point : ℝ × ℝ =>
      Complex.exp (-((Real.pi * point.1 * point.2 ^ 2 : ℝ) : ℂ))) := by
    fun_prop
  exact scaleMeasurable.mul gaussianMeasurable

theorem burnolGenericGaussianMellinKernel_aeStronglyMeasurable
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    AEStronglyMeasurable (burnolGenericGaussianMellinKernel value coordinate)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  let productMeasure : Measure (ℝ × ℝ) :=
    (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))
  have scalarAES :=
    (burnolGenericGaussianMellinMeasurableScalar_measurable coordinate).aestronglyMeasurable
      (μ := productMeasure)
  have valueAES : AEStronglyMeasurable
      (fun point : ℝ × ℝ => (value : BurnolL2) point.2) productMeasure :=
    (Lp.aestronglyMeasurable (value : BurnolL2)).restrict.comp_snd
  apply (scalarAES.mul valueAES).congr
  dsimp [productMeasure]
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod measurableSet_Ioi)] with point inside
  unfold burnolGenericGaussianMellinKernel
    burnolGenericGaussianMellinMeasurableScalar
  change burnolGaussianMellinSafeScalePower coordinate point.1 *
      burnolGaussianRaw point.1 point.2 * (value : BurnolL2) point.2 =
    (point.1 : ℂ) ^ (coordinate.value / 2 - 1) *
      burnolGaussianRaw point.1 point.2 * (value : BurnolL2) point.2
  rw [burnolGaussianMellinSafeScalePower_eq_cpow coordinate inside.1]

theorem norm_burnolGenericGaussianMellinKernel
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate)
    {t x : ℝ} (positiveT : 0 < t) :
    ‖burnolGenericGaussianMellinKernel value coordinate (t, x)‖ =
      t ^ (coordinate.value.re / 2 - 1) *
        Real.exp (-(Real.pi * x ^ 2 * t)) * ‖(value : BurnolL2) x‖ := by
  unfold burnolGenericGaussianMellinKernel burnolGaussianRaw
  rw [norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos positiveT,
    Complex.norm_exp]
  have exponentRe : (coordinate.value / 2 - 1).re =
      coordinate.value.re / 2 - 1 := by
    rw [Complex.sub_re, Complex.div_re]
    norm_num
    ring
  have gaussianRe :
      (-((Real.pi * t * x ^ 2 : ℝ) : ℂ)).re =
        -(Real.pi * x ^ 2 * t) := by
    simp only [Complex.neg_re, Complex.ofReal_re]
    ring
  rw [exponentRe, gaussianRe]

theorem integral_norm_burnolGenericGaussianMellinKernel_eq_weight
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (positiveX : 0 < x) :
    (∫ t : ℝ in Set.Ioi 0,
      ‖burnolGenericGaussianMellinKernel value coordinate (t, x)‖) =
      ((1 / Real.pi) ^ (coordinate.value.re / 2) *
          Real.Gamma (coordinate.value.re / 2)) *
        ‖(x : ℂ) ^ (-coordinate.value) * (value : BurnolL2) x‖ := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht =>
    norm_burnolGenericGaussianMellinKernel value coordinate ht)]
  rw [integral_mul_const]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi
    (show 0 < coordinate.value.re / 2 by
      linarith [coordinate.rightHalf])
    (mul_pos Real.pi_pos (sq_pos_of_pos positiveX))]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positiveX]
  simp only [neg_re]
  have baseEq : 1 / (Real.pi * x ^ 2) =
      (1 / Real.pi) * (1 / x ^ 2) := by
    field_simp [Real.pi_ne_zero, positiveX.ne']
  rw [baseEq, Real.mul_rpow (by positivity) (by positivity),
    one_div_sq_rpow_half_re coordinate positiveX]
  ring

theorem burnolGenericGaussianMellinKernel_integrableOn_scale
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (positiveX : 0 < x) :
    IntegrableOn (fun t : ℝ =>
      burnolGenericGaussianMellinKernel value coordinate (t, x))
      (Set.Ioi 0) := by
  change IntegrableOn (fun t : ℝ =>
    (t : ℂ) ^ (coordinate.value / 2 - 1) *
      Complex.exp (-((Real.pi * t * x ^ 2 : ℝ) : ℂ)) *
        (value : BurnolL2) x) (Set.Ioi 0)
  have base := burnolGaussianMellinScaleKernel_integrableOn
    coordinate.value (lt_trans (by norm_num) coordinate.rightHalf)
      (mul_pos Real.pi_pos (sq_pos_of_pos positiveX))
  apply (base.mul_const ((value : BurnolL2) x)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positiveT
  congr 2
  push_cast
  ring

theorem burnolGenericGaussianMellinKernel_integrable
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (burnolGenericGaussianMellinKernel value coordinate)
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
  rw [integrable_prod_iff'
    (burnolGenericGaussianMellinKernel_aeStronglyMeasurable value coordinate)]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positiveX
    exact burnolGenericGaussianMellinKernel_integrableOn_scale
      value coordinate positiveX
  · let coefficient : ℝ :=
      (1 / Real.pi) ^ (coordinate.value.re / 2) *
        Real.Gamma (coordinate.value.re / 2)
    have weighted :=
      (burnolGenericPhysicalMellin_integrableOn_positive value coordinate).norm.const_mul
        coefficient
    apply weighted.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positiveX
    symm
    exact integral_norm_burnolGenericGaussianMellinKernel_eq_weight
      value coordinate positiveX

theorem burnolGenericGaussianFubini
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    Gammaℝ coordinate.value * burnolCompletedMellinEvaluator coordinate value =
      (1 / 2 : ℂ) * mellin
        (burnolGenericGaussianHeatPairTotal (value : BurnolL2))
        (coordinate.value / 2) := by
  rw [burnolCompletedMellinEvaluator_eq_positive_integral]
  unfold mellin
  rw [show (∫ t : ℝ in Set.Ioi 0,
      (t : ℂ) ^ (coordinate.value / 2 - 1) •
        burnolGenericGaussianHeatPairTotal (value : BurnolL2) t) =
      ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (coordinate.value / 2 - 1) *
          (2 * burnolGenericGaussianPositivePair (value : BurnolL2) t) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t positiveT
    simp only [smul_eq_mul]
    rw [burnolGenericGaussianHeatPair_eq_two_mul_positivePair value positiveT]]
  unfold burnolGenericGaussianPositivePair
  rw [show (1 / 2 : ℂ) * (∫ t : ℝ in Set.Ioi 0,
      (t : ℂ) ^ (coordinate.value / 2 - 1) *
        (2 * ∫ x : ℝ in Set.Ioi 0,
          (value : BurnolL2) x * burnolGaussianRaw t x)) =
      ∫ t : ℝ in Set.Ioi 0, ∫ x : ℝ in Set.Ioi 0,
        burnolGenericGaussianMellinKernel value coordinate (t, x) by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change (1 / 2 : ℂ) *
        ((t : ℂ) ^ (coordinate.value / 2 - 1) *
          (2 * ∫ x : ℝ in Set.Ioi 0,
            (value : BurnolL2) x * burnolGaussianRaw t x)) =
      ∫ x : ℝ in Set.Ioi 0,
        burnolGenericGaussianMellinKernel value coordinate (t, x)
    rw [show (1 / 2 : ℂ) *
        ((t : ℂ) ^ (coordinate.value / 2 - 1) *
          (2 * ∫ x : ℝ in Set.Ioi 0,
            (value : BurnolL2) x * burnolGaussianRaw t x)) =
        (t : ℂ) ^ (coordinate.value / 2 - 1) *
          (∫ x : ℝ in Set.Ioi 0,
            (value : BurnolL2) x * burnolGaussianRaw t x) by ring,
      ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    unfold burnolGenericGaussianMellinKernel
    ring]
  have joint := burnolGenericGaussianMellinKernel_integrable value coordinate
  rw [← integral_prod _ joint, integral_prod_symm _ joint]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x positiveX
  calc
    Gammaℝ coordinate.value *
        ((x : ℂ) ^ (-coordinate.value) * (value : BurnolL2) x) =
      (Gammaℝ coordinate.value * (x : ℂ) ^ (-coordinate.value)) *
        (value : BurnolL2) x := by ring
    _ = (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (coordinate.value / 2 - 1) *
          Complex.exp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * (t : ℂ)))) *
            (value : BurnolL2) x := by
      rw [gammaReal_mul_positive_cpow_neg_eq_gaussianSuperposition
        coordinate.value (lt_trans (by norm_num) coordinate.rightHalf) positiveX]
    _ = ∫ t : ℝ in Set.Ioi 0,
        burnolGenericGaussianMellinKernel value coordinate (t, x) := by
      rw [← integral_mul_const]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      unfold burnolGenericGaussianMellinKernel burnolGaussianRaw
      push_cast
      ring

/-- The Gaussian--Fubini representation is not restricted to the compact
annulus generators: it reads every vector in the admitted even Burnol face. -/
theorem burnolGenericHomogeneousGammaMellinBridge
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    Gammaℝ coordinate.value * burnolCompletedMellinEvaluator coordinate value =
      (1 / 2 : ℂ) * mellin
        (burnolGenericGaussianHeatPairTotal (value : BurnolL2))
        (coordinate.value / 2) :=
  burnolGenericGaussianFubini value coordinate



end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
