import H0mework.Versions.Y.Arithmetic.BurnolMellin.GenericGaussianFubini
import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set Filter Asymptotics
open scoped ENNReal InnerProductSpace Topology

noncomputable section

private theorem burnolGaussian_norm_integral
    {scale : ℝ} (positive : 0 < scale) :
    (∫ x : ℝ, ‖burnolGaussianRaw scale x‖) =
      scale ^ (-(1 / 2 : ℝ)) := by
  simp only [burnolGaussianRaw, Complex.norm_exp, Complex.neg_re,
    Complex.ofReal_re]
  have raw := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := ℝ) (b := Real.pi * scale) (mul_pos Real.pi_pos positive)
  rw [show (fun x : ℝ => Real.exp (-(Real.pi * scale) * ‖x‖ ^ 2)) =
      fun x : ℝ => Real.exp (-(Real.pi * scale * x ^ 2)) by
    funext x
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring] at raw
  rw [raw]
  norm_num [Real.pi_ne_zero, positive.ne']
  rw [show Real.pi / (Real.pi * scale) = scale⁻¹ by
    field_simp [Real.pi_ne_zero, positive.ne']]
  rw [Real.inv_rpow positive.le, ← Real.rpow_neg positive.le]

theorem burnolGaussian_norm_le_inverse_square
    {scale x : ℝ} (positiveScale : 0 < scale) (positiveX : 0 < x) :
    ‖burnolGaussianRaw scale x‖ ≤
      (Real.exp (-1) / Real.pi) * scale⁻¹ * (x ^ 2)⁻¹ := by
  have coefficientPositive : 0 < Real.pi * scale * x ^ 2 := by positivity
  have core := Real.mul_exp_neg_le_exp_neg_one
    (Real.pi * scale * x ^ 2)
  have divided : Real.exp (-(Real.pi * scale * x ^ 2)) ≤
      Real.exp (-1) / (Real.pi * scale * x ^ 2) :=
    (le_div_iff₀ coefficientPositive).2 (by simpa [mul_comm] using core)
  rw [burnolGaussianRaw, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  calc
    Real.exp (-(Real.pi * scale * x ^ 2)) ≤
        Real.exp (-1) / (Real.pi * scale * x ^ 2) := divided
    _ = (Real.exp (-1) / Real.pi) * scale⁻¹ * (x ^ 2)⁻¹ := by
      field_simp [Real.pi_ne_zero, positiveScale.ne', positiveX.ne']

theorem burnolPhysical_inverseSquare_integrableOn_tail
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    IntegrableOn (fun x : ℝ =>
      ‖(value : BurnolL2) x‖ * (x ^ 2)⁻¹)
      (Ioi burnolUnscaledCommonGapRadius) := by
  have weighted := (burnolMellinWeight_integrableOn_tail
    (2 : ℂ) (by norm_num) (value : BurnolL2)).norm
  apply weighted.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have positiveX : 0 < x := lt_trans
    (by norm_num [burnolUnscaledCommonGapRadius]) hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positiveX]
  have twoRe : (2 : ℂ).re = 2 := rfl
  rw [Complex.neg_re, twoRe]
  rw [Real.rpow_neg positiveX.le, Real.rpow_two]
  ring

private def burnolPhysicalHeatTailMoment
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) : ℝ :=
  ∫ x : ℝ in Ioi burnolUnscaledCommonGapRadius,
    ‖(value : BurnolL2) x‖ * (x ^ 2)⁻¹

private theorem burnolPhysicalHeatTailMoment_nonnegative
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    0 ≤ burnolPhysicalHeatTailMoment value := by
  unfold burnolPhysicalHeatTailMoment
  exact integral_nonneg_of_ae (ae_of_all _ fun x => by positivity)

private theorem burnolGenericGaussianHeatPair_norm_le
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    {scale : ℝ} (positive : 0 < scale) :
    ‖burnolGenericGaussianHeatPairTotal (value : BurnolL2) scale‖ ≤
      2 *
        (‖burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value‖ *
            scale ^ (-(1 / 2 : ℝ)) +
          (Real.exp (-1) / Real.pi) * scale⁻¹ *
            burnolPhysicalHeatTailMoment value) := by
  let radius := burnolUnscaledCommonGapRadius
  let coefficient := burnolConstantGapCoefficient radius value
  let raw : ℝ → ℂ := fun x =>
    (value : BurnolL2) x * burnolGaussianRaw scale x
  have rawIntegrable : Integrable raw := by
    exact (L2.integrable_inner
      (burnolGaussianL2 scale positive) (value : BurnolL2)).congr (by
        filter_upwards [burnolGaussianL2_coeFn scale positive] with x gaussianRead
        rw [gaussianRead, RCLike.inner_apply, starRingEnd_apply,
          star_burnolGaussianRaw])
  have radiusNonnegative : 0 ≤ radius := by
    norm_num [radius, burnolUnscaledCommonGapRadius]
  have split :
      (∫ x : ℝ in Ioi 0, ‖raw x‖) =
        (∫ x : ℝ in Ioc 0 radius, ‖raw x‖) +
          ∫ x : ℝ in Ioi radius, ‖raw x‖ := by
    rw [← Ioc_union_Ioi_eq_Ioi radiusNonnegative,
      setIntegral_union]
    · exact Set.disjoint_left.2 fun x hx hxr => (not_lt_of_ge hx.2) hxr
    · exact measurableSet_Ioi
    · exact rawIntegrable.norm.integrableOn
    · exact rawIntegrable.norm.integrableOn
  have gapIntegral :
      (∫ x : ℝ in Ioc 0 radius, ‖raw x‖) ≤
        ‖coefficient‖ * scale ^ (-(1 / 2 : ℝ)) := by
    have gapRead : ∀ᵐ x ∂volume.restrict (Ioc 0 radius),
        (value : BurnolL2) x = coefficient := by
      simpa only [radius, coefficient] using
        burnolGenericPhysicalValue_ae_eq_gapCoefficient_on_Ioc value
    calc
      (∫ x : ℝ in Ioc 0 radius, ‖raw x‖) =
          ‖coefficient‖ *
            ∫ x : ℝ in Ioc 0 radius, ‖burnolGaussianRaw scale x‖ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [gapRead] with x valueRead
        simp only [raw, norm_mul, valueRead]
      _ ≤ ‖coefficient‖ *
          (∫ x : ℝ, ‖burnolGaussianRaw scale x‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg coefficient)
        exact setIntegral_le_integral
          (burnolGaussianRaw_integrable positive).norm
          (ae_of_all _ fun _ => norm_nonneg _)
      _ = ‖coefficient‖ * scale ^ (-(1 / 2 : ℝ)) := by
        rw [burnolGaussian_norm_integral positive]
  have tailIntegral :
      (∫ x : ℝ in Ioi radius, ‖raw x‖) ≤
        (Real.exp (-1) / Real.pi) * scale⁻¹ *
          burnolPhysicalHeatTailMoment value := by
    let factor := (Real.exp (-1) / Real.pi) * scale⁻¹
    have factorNonnegative : 0 ≤ factor := by
      dsimp [factor]
      positivity
    have comparisonIntegrable : IntegrableOn (fun x : ℝ =>
        factor * (‖(value : BurnolL2) x‖ * (x ^ 2)⁻¹)) (Ioi radius) :=
      (burnolPhysical_inverseSquare_integrableOn_tail value).const_mul factor
    calc
      (∫ x : ℝ in Ioi radius, ‖raw x‖) ≤
          ∫ x : ℝ in Ioi radius,
            factor * (‖(value : BurnolL2) x‖ * (x ^ 2)⁻¹) := by
        apply integral_mono_ae rawIntegrable.norm.integrableOn comparisonIntegrable
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have positiveX : 0 < x := lt_trans
          (by norm_num [radius, burnolUnscaledCommonGapRadius]) hx
        dsimp [raw, factor]
        rw [norm_mul]
        have gaussianBound := burnolGaussian_norm_le_inverse_square
          positive positiveX
        calc
          ‖(value : BurnolL2) x‖ * ‖burnolGaussianRaw scale x‖ ≤
              ‖(value : BurnolL2) x‖ *
                ((Real.exp (-1) / Real.pi) * scale⁻¹ * (x ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left gaussianBound (norm_nonneg _)
          _ = ((Real.exp (-1) / Real.pi) * scale⁻¹) *
              (‖(value : BurnolL2) x‖ * (x ^ 2)⁻¹) := by ring
      _ = (Real.exp (-1) / Real.pi) * scale⁻¹ *
          burnolPhysicalHeatTailMoment value := by
        rw [integral_const_mul]
        rfl
  rw [burnolGenericGaussianHeatPair_eq_two_mul_positivePair value positive]
  simp only [norm_mul, norm_ofNat]
  calc
    2 * ‖burnolGenericGaussianPositivePair (value : BurnolL2) scale‖ ≤
        2 * (∫ x : ℝ in Ioi 0, ‖raw x‖) := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ = 2 * ((∫ x : ℝ in Ioc 0 radius, ‖raw x‖) +
        ∫ x : ℝ in Ioi radius, ‖raw x‖) := by rw [split]
    _ ≤ 2 * (‖coefficient‖ * scale ^ (-(1 / 2 : ℝ)) +
        (Real.exp (-1) / Real.pi) * scale⁻¹ *
          burnolPhysicalHeatTailMoment value) := by gcongr
    _ = _ := rfl

theorem burnolGenericGaussianHeatPair_isBigO_atTop
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) =O[atTop]
      (fun scale : ℝ => scale ^ (-(1 / 2 : ℝ))) := by
  let coefficient :=
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value
  let tailCoefficient :=
    (Real.exp (-1) / Real.pi) * burnolPhysicalHeatTailMoment value
  let bound : ℝ := 2 * (‖coefficient‖ + tailCoefficient)
  have tailCoefficientNonnegative : 0 ≤ tailCoefficient := by
    dsimp [tailCoefficient]
    exact mul_nonneg (by positivity)
      (burnolPhysicalHeatTailMoment_nonnegative value)
  have boundNonnegative : 0 ≤ bound := by
    dsimp [bound]
    positivity
  refine IsBigO.of_bound bound ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with scale scaleAtLeastOne
  have positive : 0 < scale := lt_of_lt_of_le zero_lt_one scaleAtLeastOne
  have inverseLe : scale⁻¹ ≤ scale ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le scaleAtLeastOne (by norm_num)
  have sourceBound := burnolGenericGaussianHeatPair_norm_le value positive
  have targetNonnegative : 0 ≤ scale ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg positive.le _
  rw [Real.norm_of_nonneg targetNonnegative]
  calc
    ‖burnolGenericGaussianHeatPairTotal (value : BurnolL2) scale‖ ≤
        2 *
          (‖coefficient‖ * scale ^ (-(1 / 2 : ℝ)) +
            tailCoefficient * scale⁻¹) := by
      dsimp only [coefficient, tailCoefficient]
      convert sourceBound using 1
      ring
    _ ≤ 2 *
        (‖coefficient‖ * scale ^ (-(1 / 2 : ℝ)) +
          tailCoefficient * scale ^ (-(1 / 2 : ℝ))) := by
      gcongr
    _ = bound * scale ^ (-(1 / 2 : ℝ)) := by
      dsimp [bound]
      ring

private theorem norm_inverse_cpow_neg_half
    {scale : ℝ} (positive : 0 < scale) :
    ‖((scale⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))‖ =
      scale ^ (1 / 2 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr positive)]
  have exponent : (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) := by norm_num
  rw [exponent, Real.inv_rpow positive.le, ← Real.rpow_neg positive.le]
  congr 1
  norm_num

private theorem norm_inverse_rpow_neg_half
    {scale : ℝ} (positive : 0 < scale) :
    ‖scale⁻¹ ^ (-(1 / 2 : ℝ))‖ = scale ^ (1 / 2 : ℝ) := by
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (inv_pos.mpr positive).le _),
    Real.inv_rpow positive.le, ← Real.rpow_neg positive.le]
  congr 1
  norm_num

theorem burnolGenericGaussianHeatPair_isBigO_zero
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) =O[𝓝[>] 0]
      (fun _scale : ℝ => (1 : ℝ)) := by
  let fourierValue :
      EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius :=
    evenFaceFourier burnolUnscaledCommonGapRadius value
  obtain ⟨bound, boundAtTop⟩ :=
    (burnolGenericGaussianHeatPair_isBigO_atTop fourierValue).bound
  refine IsBigO.of_bound bound ?_
  have pulled := tendsto_inv_nhdsGT_zero.eventually boundAtTop
  filter_upwards [pulled, self_mem_nhdsWithin] with scale scaleBound positive
  have fourierIdentity := burnolGenericGaussianHeatPairTotal_fourier
    value scale⁻¹
  have inversePositive : 0 < scale⁻¹ := inv_pos.mpr positive
  have identity :
      burnolGenericGaussianHeatPairTotal (fourierValue : BurnolL2) scale⁻¹ =
        (((scale⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) *
          burnolGenericGaussianHeatPairTotal (value : BurnolL2) scale := by
    rw [show (fourierValue : BurnolL2) = fourierL2 (value : BurnolL2) by rfl]
    simpa only [inv_inv] using fourierIdentity
  have scalePowerPositive : 0 < scale ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos positive _
  have scaledBound :
      scale ^ (1 / 2 : ℝ) *
          ‖burnolGenericGaussianHeatPairTotal (value : BurnolL2) scale‖ ≤
        bound * scale ^ (1 / 2 : ℝ) := by
    calc
      scale ^ (1 / 2 : ℝ) *
          ‖burnolGenericGaussianHeatPairTotal (value : BurnolL2) scale‖ =
          ‖burnolGenericGaussianHeatPairTotal
            (fourierValue : BurnolL2) scale⁻¹‖ := by
        rw [identity, norm_mul, norm_inverse_cpow_neg_half positive]
      _ ≤ bound * ‖scale⁻¹ ^ (-(1 / 2 : ℝ))‖ := scaleBound
      _ = bound * scale ^ (1 / 2 : ℝ) := by
        rw [norm_inverse_rpow_neg_half positive]
  have scaledBound' :
      scale ^ (1 / 2 : ℝ) *
          ‖burnolGenericGaussianHeatPairTotal (value : BurnolL2) scale‖ ≤
        scale ^ (1 / 2 : ℝ) * bound := by
    simpa only [mul_comm] using scaledBound
  simpa only [norm_one, mul_one] using
    le_of_mul_le_mul_left scaledBound' scalePowerPositive

private theorem burnolGenericGaussianPositivePair_aestronglyMeasurable
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    AEStronglyMeasurable
      (burnolGenericGaussianPositivePair (value : BurnolL2)) volume := by
  have gaussianMeasurable : Measurable (fun point : ℝ × ℝ =>
      burnolGaussianRaw point.1 point.2) := by
    unfold burnolGaussianRaw
    fun_prop
  have valueAES : AEStronglyMeasurable (fun point : ℝ × ℝ =>
      (value : BurnolL2) point.2)
      (volume.prod (volume.restrict (Ioi 0))) :=
    (Lp.aestronglyMeasurable (value : BurnolL2)).restrict.comp_snd
  have jointAES : AEStronglyMeasurable (fun point : ℝ × ℝ =>
      (value : BurnolL2) point.2 * burnolGaussianRaw point.1 point.2)
      (volume.prod (volume.restrict (Ioi 0))) :=
    valueAES.mul gaussianMeasurable.aestronglyMeasurable
  change AEStronglyMeasurable (fun scale : ℝ =>
    ∫ x : ℝ in Ioi 0,
      (value : BurnolL2) x * burnolGaussianRaw scale x) volume
  exact jointAES.integral_prod_right'

private theorem burnolGenericGaussianHeatPair_aestronglyMeasurable
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    AEStronglyMeasurable
      (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) volume := by
  let positivePair : ℝ → ℂ :=
    burnolGenericGaussianPositivePair (value : BurnolL2)
  have positivePairAES : AEStronglyMeasurable positivePair volume :=
    burnolGenericGaussianPositivePair_aestronglyMeasurable value
  have indicatorAES : AEStronglyMeasurable
      ((Ioi (0 : ℝ)).indicator (fun scale => 2 * positivePair scale)) volume :=
    (positivePairAES.const_mul 2).indicator measurableSet_Ioi
  apply indicatorAES.congr
  filter_upwards with scale
  by_cases positive : 0 < scale
  · simpa [positivePair, Set.indicator, positive] using
      (burnolGenericGaussianHeatPair_eq_two_mul_positivePair value positive).symm
  · simp [Set.indicator, positive,
      burnolGenericGaussianHeatPairTotal]

private theorem burnolGenericGaussianHeatPair_locallyIntegrableOn
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    LocallyIntegrableOn
      (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) (Ioi 0) := by
  let coefficient :=
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value
  let tailCoefficient :=
    (Real.exp (-1) / Real.pi) * burnolPhysicalHeatTailMoment value
  let majorant : ℝ → ℝ := fun scale =>
    2 * (‖coefficient‖ * scale ^ (-(1 / 2 : ℝ)) +
      tailCoefficient * scale⁻¹)
  have majorantContinuous : ContinuousOn majorant (Ioi 0) := by
    have rpowContinuous : ContinuousOn
        (fun scale : ℝ => scale ^ (-(1 / 2 : ℝ))) (Ioi 0) :=
      continuousOn_id.rpow_const fun scale positive => Or.inl positive.ne'
    have invContinuous : ContinuousOn (fun scale : ℝ => scale⁻¹) (Ioi 0) :=
      continuousOn_id.inv₀ fun scale positive => positive.ne'
    exact ((rpowContinuous.const_mul ‖coefficient‖).add
      (invContinuous.const_mul tailCoefficient)).const_mul 2
  have majorantLocal : LocallyIntegrableOn majorant (Ioi 0) :=
    majorantContinuous.locallyIntegrableOn measurableSet_Ioi
  apply majorantLocal.mono
    (burnolGenericGaussianHeatPair_aestronglyMeasurable value)
  filter_upwards with scale
  have tailCoefficientNonnegative : 0 ≤ tailCoefficient := by
    dsimp [tailCoefficient]
    exact mul_nonneg (by positivity)
      (burnolPhysicalHeatTailMoment_nonnegative value)
  by_cases positive : 0 < scale
  · have majorantNonnegative : 0 ≤ majorant scale := by
      dsimp [majorant]
      positivity
    rw [Real.norm_of_nonneg majorantNonnegative]
    have sourceBound := burnolGenericGaussianHeatPair_norm_le value positive
    dsimp only [majorant, coefficient, tailCoefficient]
    convert sourceBound using 1
    ring
  · simp [burnolGenericGaussianHeatPairTotal, positive]

/-- The constant position/Fourier gaps give the full open heat-Mellin strip;
the midpoint is included and does not need a separate continuation premise. -/
theorem burnolGenericGaussianHeatPair_mellin_differentiableAt
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : ℂ) (positive : 0 < coordinate.re)
    (belowHalf : coordinate.re < 1 / 2) :
    DifferentiableAt ℂ
      (mellin (burnolGenericGaussianHeatPairTotal (value : BurnolL2)))
      coordinate := by
  exact mellin_differentiableAt_of_isBigO_rpow
    (burnolGenericGaussianHeatPair_locallyIntegrableOn value)
    (burnolGenericGaussianHeatPair_isBigO_atTop value)
    belowHalf
    (by simpa using burnolGenericGaussianHeatPair_isBigO_zero value)
    positive

def burnolPhysicalHeatMellinStrip : Set ℂ :=
  {coordinate | 0 < coordinate.re ∧ coordinate.re < 1 / 2}

theorem burnolGenericGaussianHeatPair_mellin_differentiableOn
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    DifferentiableOn ℂ
      (mellin (burnolGenericGaussianHeatPairTotal (value : BurnolL2)))
      burnolPhysicalHeatMellinStrip := by
  intro coordinate membership
  exact (burnolGenericGaussianHeatPair_mellin_differentiableAt value
    coordinate membership.1 membership.2).differentiableWithinAt

theorem burnolPhysicalHeatMellinStrip_eq_inter :
    burnolPhysicalHeatMellinStrip =
      {coordinate : ℂ | 0 < coordinate.re} ∩
        {coordinate : ℂ | coordinate.re < 1 / 2} := by
  rfl

theorem burnolPhysicalHeatMellinStrip_isOpen :
    IsOpen burnolPhysicalHeatMellinStrip := by
  rw [burnolPhysicalHeatMellinStrip_eq_inter]
  exact (isOpen_Ioi.preimage Complex.continuous_re).inter
    (isOpen_Iio.preimage Complex.continuous_re)

theorem burnolPhysicalHeatMellinStrip_convex :
    Convex ℝ burnolPhysicalHeatMellinStrip := by
  rw [burnolPhysicalHeatMellinStrip_eq_inter]
  exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt (1 / 2))

theorem burnolPhysicalHeatMellinStrip_nonempty :
    burnolPhysicalHeatMellinStrip.Nonempty := by
  refine ⟨(1 / 4 : ℂ), ?_⟩
  constructor <;> norm_num

theorem burnolPhysicalHeatMellinStrip_isConnected :
    IsConnected burnolPhysicalHeatMellinStrip :=
  burnolPhysicalHeatMellinStrip_convex.isConnected
    burnolPhysicalHeatMellinStrip_nonempty

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.burnolGenericGaussianHeatPair_mellin_differentiableOn
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.burnolPhysicalHeatMellinStrip_isConnected
