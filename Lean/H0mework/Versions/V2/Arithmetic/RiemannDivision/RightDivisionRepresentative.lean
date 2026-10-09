import H0mework.Versions.V2.Arithmetic.RiemannDivision.RightDivisionTail

/-! # Burnol right-division measurable representative -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set Filter FourierTransform
open SourceGeneratedComplexFeaturePerfectification
open scoped ENNReal InnerProductSpace

noncomputable section

theorem integral_norm_inner_L2_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (left right : Lp ℂ 2 μ) :
    (∫ x : α, ‖inner ℂ (left x) (right x)‖ ∂μ) ≤
      ‖left‖ * ‖right‖ := by
  have holder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (f := fun x : α => left x) (g := fun x : α => right x)
    Real.HolderConjugate.two_two
      (by simpa using Lp.memLp left) (by simpa using Lp.memLp right)
  have pointwise : (fun x : α => ‖inner ℂ (left x) (right x)‖) =
      fun x : α => ‖left x‖ * ‖right x‖ := by
    funext x
    simp [RCLike.inner_apply, mul_comm]
  have normRead (value : Lp ℂ 2 μ) :
      ((∫ x : α, ‖value x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹)) =
        ‖value‖ := by
    rw [Lp.norm_def,
      (Lp.memLp value).eLpNorm_eq_integral_rpow_norm
        (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
  have leftNormRead :
      ((∫ x : α, ‖left x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)) =
        ‖left‖ := by
    convert normRead left using 1
    all_goals norm_num
  have rightNormRead :
      ((∫ x : α, ‖right x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)) =
        ‖right‖ := by
    convert normRead right using 1
    all_goals norm_num
  rw [pointwise]
  rw [leftNormRead, rightNormRead] at holder
  exact holder

def burnolEvenStrongRepresentative (value : BurnolL2) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) *
    ((Lp.aestronglyMeasurable value).mk value x +
      (Lp.aestronglyMeasurable value).mk value (-x))

theorem burnolEvenStrongRepresentative_stronglyMeasurable
    (value : BurnolL2) :
    StronglyMeasurable (burnolEvenStrongRepresentative value) := by
  let representative := (Lp.aestronglyMeasurable value).mk value
  have measurable : StronglyMeasurable representative :=
    (Lp.aestronglyMeasurable value).stronglyMeasurable_mk
  unfold burnolEvenStrongRepresentative
  exact (measurable.add
    (measurable.comp_measurable continuous_neg.measurable)).const_mul
      (1 / 2 : ℂ)

@[simp] private theorem burnolEvenStrongRepresentative_neg
    (value : BurnolL2) (x : ℝ) :
    burnolEvenStrongRepresentative value (-x) =
      burnolEvenStrongRepresentative value x := by
  unfold burnolEvenStrongRepresentative
  rw [neg_neg]
  ring

theorem burnolEvenStrongRepresentative_ae_eq
    (value : BurnolL2) (even : reflectL2 value = value) :
    burnolEvenStrongRepresentative value =ᵐ[volume] value := by
  have reflected := Lp.coeFn_compMeasurePreserving value negMeasurePreserving
  change (reflectL2 value : ℝ → ℂ) =ᵐ[volume]
    (value : ℝ → ℂ) ∘ fun x : ℝ => -x at reflected
  rw [even] at reflected
  have representative := (Lp.aestronglyMeasurable value).ae_eq_mk
  have representativeNeg :=
    negMeasurePreserving.quasiMeasurePreserving.ae representative
  filter_upwards [representative, representativeNeg, reflected]
    with x direct negDirect reflection
  change value x = value (-x) at reflection
  unfold burnolEvenStrongRepresentative
  rw [← direct, ← negDirect, ← reflection]
  ring

def burnolFourierDivisionPairingKernel
    (radius : ℝ) (z : ℂ) (value : BurnolL2)
    (test : Lp ℂ 2 (volume.restrict
      (symmetricInterval radius)))
    (point : ℝ × ℝ) : ℂ :=
  inner ℂ
    ((Lp.aestronglyMeasurable test).mk test point.2)
    (Complex.exp (((1 / 2 : ℂ) - z) * (point.1 : ℂ)) *
      burnolEvenStrongRepresentative value
        (Real.exp (point.1 / 2) * point.2))

theorem burnolFourierDivisionPairingKernel_stronglyMeasurable
    (radius : ℝ) (z : ℂ) (value : BurnolL2)
    (test : Lp ℂ 2 (volume.restrict
      (symmetricInterval radius))) :
    StronglyMeasurable
      (burnolFourierDivisionPairingKernel radius z value test) := by
  have testMeasurable : StronglyMeasurable
      (fun point : ℝ × ℝ =>
        (Lp.aestronglyMeasurable test).mk test point.2) :=
    (Lp.aestronglyMeasurable test).stronglyMeasurable_mk.comp_measurable
      measurable_snd
  have orbitMapContinuous : Continuous
      (fun point : ℝ × ℝ => Real.exp (point.1 / 2) * point.2) := by
    fun_prop
  have orbitMeasurable : StronglyMeasurable
      (fun point : ℝ × ℝ => burnolEvenStrongRepresentative value
        (Real.exp (point.1 / 2) * point.2)) :=
    (burnolEvenStrongRepresentative_stronglyMeasurable value
      ).comp_measurable orbitMapContinuous.measurable
  have weightMeasurable : StronglyMeasurable
      (fun point : ℝ × ℝ =>
        Complex.exp (((1 / 2 : ℂ) - z) * (point.1 : ℂ))) := by
    fun_prop
  unfold burnolFourierDivisionPairingKernel
  exact testMeasurable.inner (weightMeasurable.mul orbitMeasurable)

theorem burnolFourierDivisionPairingKernel_section_ae
    (radius : ℝ) (z : ℂ) (value : BurnolL2)
    (even : reflectL2 value = value)
    (test : Lp ℂ 2 (volume.restrict
      (symmetricInterval radius))) (h : ℝ) :
    (fun x : ℝ =>
      burnolFourierDivisionPairingKernel radius z value test (h, x)) =ᵐ[
      (volume : Measure ℝ).restrict
        (symmetricInterval radius)]
      fun x : ℝ => inner ℂ (test x)
        (restrictToInterval radius
          (positiveMellinQuarterRightResolventWeight z h •
            burnolMultiplicativeDilation (h / 2) value) x) := by
  have scaleQmp : Measure.QuasiMeasurePreserving
      (fun x : ℝ => Real.exp (h / 2) * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp (h / 2)) (Real.exp_ne_zero _))
  have valueRead := scaleQmp.ae
    (burnolEvenStrongRepresentative_ae_eq value even)
  have restrictionRead :
      (restrictToInterval radius
        (positiveMellinQuarterRightResolventWeight z h •
          burnolMultiplicativeDilation (h / 2) value) : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).restrict
          (symmetricInterval radius)]
        (positiveMellinQuarterRightResolventWeight z h •
          burnolMultiplicativeDilation (h / 2) value : BurnolL2) :=
    LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval radius)
      (positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (h / 2) value)
  filter_upwards [(Lp.aestronglyMeasurable test).ae_eq_mk,
    ae_restrict_of_ae valueRead,
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn (h / 2) value),
    ae_restrict_of_ae
      (Lp.coeFn_smul (positiveMellinQuarterRightResolventWeight z h)
        (burnolMultiplicativeDilation (h / 2) value)),
    restrictionRead]
      with x testRead valueAt dilationRead smulRead restrictionAt
  unfold burnolFourierDivisionPairingKernel
  rw [← testRead, valueAt]
  change
    (positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (h / 2) value : BurnolL2) x =
      positiveMellinQuarterRightResolventWeight z h *
        burnolMultiplicativeDilation (h / 2) value x at smulRead
  rw [restrictionAt, smulRead, dilationRead]
  apply congrArg (inner ℂ (test x))
  exact (burnolFourierRightDivision_integrand_eq z value x h).symm

theorem burnolEvenStrongRepresentative_gapConstant
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : EvenBurnolPhysicalCarrier radius)
    (even : reflectL2 (value : BurnolL2) = (value : BurnolL2))
    (readZero :
      burnolRadiusCompletedMellinEvaluator radius positive coordinate value = 0)
    {x : ℝ} (positiveX : 0 < x) (bounded : x ≤ radius) :
    burnolFourierRightDivisionRaw (coordinate.value / 2)
        (burnolEvenStrongRepresentative (value : BurnolL2)) x =
      (2 : ℂ) * burnolConstantGapCoefficient radius value /
        (1 - coordinate.value) := by
  calc
    burnolFourierRightDivisionRaw (coordinate.value / 2)
        (burnolEvenStrongRepresentative (value : BurnolL2)) x =
      -2 * (x : ℂ) ^ (2 * (coordinate.value / 2) - 1) *
        ∫ t : ℝ in Ioi x,
          (t : ℂ) ^ (-2 * (coordinate.value / 2)) *
            burnolEvenStrongRepresentative (value : BurnolL2) t :=
      burnolFourierRightDivisionRaw_eq_tail _ _ positiveX
    _ = -2 * (x : ℂ) ^ (2 * (coordinate.value / 2) - 1) *
        ∫ t : ℝ in Ioi x,
          (t : ℂ) ^ (-2 * (coordinate.value / 2)) *
            (value : BurnolL2) t := by
      have integralRead :
          (∫ t : ℝ in Ioi x,
              (t : ℂ) ^ (-2 * (coordinate.value / 2)) *
                burnolEvenStrongRepresentative (value : BurnolL2) t) =
            ∫ t : ℝ in Ioi x,
              (t : ℂ) ^ (-2 * (coordinate.value / 2)) *
                (value : BurnolL2) t := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae
          (burnolEvenStrongRepresentative_ae_eq (value : BurnolL2) even)]
          with t read
        rw [read]
      rw [integralRead]
    _ = burnolFourierRightDivisionRaw (coordinate.value / 2)
        (value : BurnolL2) x :=
      (burnolFourierRightDivisionRaw_eq_tail _ _ positiveX).symm
    _ = _ := burnolFourierRightDivisionRaw_eq_gapConstant
      radius positive coordinate value readZero positiveX bounded

theorem burnolFourierRightDivisionRaw_evenRepresentative_even
    (z : ℂ) (value : BurnolL2) (x : ℝ) :
    burnolFourierRightDivisionRaw z (burnolEvenStrongRepresentative value) (-x) =
      burnolFourierRightDivisionRaw z
        (burnolEvenStrongRepresentative value) x := by
  unfold burnolFourierRightDivisionRaw
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h _
  change Complex.exp (((1 / 2 : ℂ) - z) * (h : ℂ)) *
      burnolEvenStrongRepresentative value (Real.exp (h / 2) * -x) =
    Complex.exp (((1 / 2 : ℂ) - z) * (h : ℂ)) *
      burnolEvenStrongRepresentative value (Real.exp (h / 2) * x)
  rw [show Real.exp (h / 2) * -x =
      -(Real.exp (h / 2) * x) by ring,
    burnolEvenStrongRepresentative_neg]

theorem burnolEvenStrongRepresentative_gapConstant_ae
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : EvenBurnolPhysicalCarrier radius)
    (even : reflectL2 (value : BurnolL2) = (value : BurnolL2))
    (readZero :
      burnolRadiusCompletedMellinEvaluator radius positive coordinate value = 0) :
    ∀ᵐ x ∂volume.restrict (symmetricInterval radius),
      burnolFourierRightDivisionRaw (coordinate.value / 2)
          (burnolEvenStrongRepresentative (value : BurnolL2)) x =
        (2 : ℂ) * burnolConstantGapCoefficient radius value /
          (1 - coordinate.value) := by
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval radius),
    ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x inside nonzero
  rcases lt_or_gt_of_ne nonzero with negativeX | positiveX
  · rw [← burnolFourierRightDivisionRaw_evenRepresentative_even
      (coordinate.value / 2) (value : BurnolL2) x]
    apply burnolEvenStrongRepresentative_gapConstant
      radius positive coordinate value even readZero (neg_pos.mpr negativeX)
    simp only [symmetricInterval, mem_Icc] at inside
    linarith
  · exact burnolEvenStrongRepresentative_gapConstant
      radius positive coordinate value even readZero positiveX inside.2

theorem burnolFourierDivisionPairingKernel_integrable
    (radius : ℝ) (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value = value)
    (test : Lp ℂ 2 (volume.restrict (symmetricInterval radius))) :
    Integrable (burnolFourierDivisionPairingKernel
      radius (coordinate.value / 2) value test)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (symmetricInterval radius))) := by
  let z := coordinate.value / 2
  let intervalMeasure := (volume : Measure ℝ).restrict (symmetricInterval radius)
  let restrictedOrbit : ℝ → Lp ℂ 2 intervalMeasure := fun h =>
    restrictToInterval radius
      (positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (h / 2) value)
  have kernelMeasurable : AEStronglyMeasurable
      (burnolFourierDivisionPairingKernel radius z value test)
      ((volume.restrict (Ioi (0 : ℝ))).prod intervalMeasure) :=
    (burnolFourierDivisionPairingKernel_stronglyMeasurable
      radius z value test).aestronglyMeasurable
  rw [integrable_prod_iff kernelMeasurable]
  constructor
  · filter_upwards with h
    have sectionRead := burnolFourierDivisionPairingKernel_section_ae
      radius z value even test h
    change (fun x : ℝ =>
      burnolFourierDivisionPairingKernel radius z value test (h, x)) =ᵐ[
        intervalMeasure]
      fun x : ℝ => inner ℂ (test x) (restrictedOrbit h x) at sectionRead
    exact (L2.integrable_inner (𝕜 := ℂ) test
      (restrictedOrbit h)).congr sectionRead.symm
  · let decay : ℝ → ℝ := fun h =>
      ‖test‖ * ‖restrictToInterval radius‖ *
        (Real.exp (-((coordinate.value / 2).re - 1 / 4) * h) * ‖value‖)
    have ratePositive : 0 < (coordinate.value / 2).re - 1 / 4 := by
      rw [Complex.div_re]
      norm_num
      linarith [coordinate.rightHalf]
    have decayIntegrable : Integrable decay
        (volume.restrict (Ioi (0 : ℝ))) := by
      have base := exp_neg_integrableOn_Ioi 0 ratePositive
      have scaled := ((base.const_mul
        (‖test‖ * ‖restrictToInterval radius‖)).mul_const ‖value‖)
      simpa only [decay, mul_assoc] using scaled
    apply Integrable.mono' decayIntegrable.norm
      kernelMeasurable.norm.integral_prod_right'
    filter_upwards with h
    have sectionRead := burnolFourierDivisionPairingKernel_section_ae
      radius z value even test h
    change (fun x : ℝ =>
      burnolFourierDivisionPairingKernel radius z value test (h, x)) =ᵐ[
        intervalMeasure]
      fun x : ℝ => inner ℂ (test x) (restrictedOrbit h x) at sectionRead
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
      Real.norm_of_nonneg (by positivity)]
    have normIntegralRead :
        (∫ x : ℝ,
          ‖burnolFourierDivisionPairingKernel radius z value test (h, x)‖
          ∂intervalMeasure) =
        ∫ x : ℝ, ‖inner ℂ (test x) (restrictedOrbit h x)‖
          ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [sectionRead] with x read
      rw [read]
    rw [normIntegralRead]
    calc
      (∫ x : ℝ, ‖inner ℂ (test x) (restrictedOrbit h x)‖
          ∂intervalMeasure) ≤ ‖test‖ * ‖restrictedOrbit h‖ :=
        integral_norm_inner_L2_le intervalMeasure test (restrictedOrbit h)
      _ ≤ ‖test‖ * ‖restrictToInterval radius‖ *
          ‖positiveMellinQuarterRightResolventWeight z h •
            burnolMultiplicativeDilation (h / 2) value‖ := by
        have restrictionBound : ‖restrictedOrbit h‖ ≤
            ‖restrictToInterval radius‖ *
              ‖positiveMellinQuarterRightResolventWeight z h •
                burnolMultiplicativeDilation (h / 2) value‖ :=
          (restrictToInterval radius).le_opNorm _
        calc
          ‖test‖ * ‖restrictedOrbit h‖ ≤
              ‖test‖ * (‖restrictToInterval radius‖ *
                ‖positiveMellinQuarterRightResolventWeight z h •
                  burnolMultiplicativeDilation (h / 2) value‖) :=
            mul_le_mul_of_nonneg_left restrictionBound (norm_nonneg _)
          _ = _ := by ring
      _ = decay h := by
        rw [norm_smul, (burnolMultiplicativeDilation (h / 2)).norm_map,
          norm_positiveMellinQuarterRightResolventWeight]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
