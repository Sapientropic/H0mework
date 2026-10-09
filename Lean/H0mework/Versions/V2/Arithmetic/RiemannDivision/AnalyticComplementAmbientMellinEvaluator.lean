import H0mework.Versions.V2.Arithmetic.RiemannDivision.AnalyticComplementDivisionState

/-! # Ambient Mellin evaluator on the generated position face -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set Filter
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal InnerProductSpace

noncomputable section

private theorem divisionJet_ambientGapCoefficient_eq
    (radius : ℝ) (positive : 0 < radius)
    (value : BurnolL2) (coefficient : ℂ)
    (gap : coefficient • intervalConstant radius =
      restrictToInterval radius value) :
    burnolAmbientGapCoefficient radius value = coefficient := by
  have normNe : (‖intervalConstant radius‖ ^ 2 : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2
      (norm_ne_zero_iff.mpr (intervalConstant_ne_zero positive))
  unfold burnolAmbientGapCoefficient
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
  change (‖intervalConstant radius‖ ^ 2 : ℂ)⁻¹ *
      inner ℂ (intervalConstant radius)
        (restrictToInterval radius value) = coefficient
  rw [← gap, inner_smul_right, inner_self_eq_norm_sq_to_K]
  rw [← mul_assoc,
    mul_comm ((‖intervalConstant radius‖ ^ 2 : ℂ)⁻¹) coefficient,
    mul_assoc]
  simp [normNe]

private theorem divisionJet_value_ae_eq_gapCoefficient_on_Ioc
    (radius : ℝ) (positive : 0 < radius)
    (value : BurnolL2) (coefficient : ℂ)
    (gap : coefficient • intervalConstant radius =
      restrictToInterval radius value) :
    ∀ᵐ x ∂volume.restrict (Ioc 0 radius), value x = coefficient := by
  have onSymmetric : ∀ᵐ x ∂volume.restrict (symmetricInterval radius),
      value x = coefficient := by
    filter_upwards [Lp.coeFn_smul coefficient (intervalConstant radius),
      intervalConstant_coeFn radius,
      LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) value]
      with x hsmul hconstant hrestrict
    calc
      value x = restrictToInterval radius value x := hrestrict.symm
      _ = (coefficient • intervalConstant radius) x := by rw [gap]
      _ = coefficient * intervalConstant radius x := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
      _ = coefficient := by rw [hconstant, mul_one]
  apply ae_restrict_of_ae_restrict_of_subset _ onSymmetric
  intro x hx
  change -radius ≤ x ∧ x ≤ radius
  exact ⟨by linarith [hx.1, positive], hx.2⟩

/-- On a vector carrying the fixed position gap, the ambient gap-plus-tail
functional is its honest full positive Mellin integral. -/
theorem burnolAmbientCompletedMellinEvaluator_eq_positive_integral_of_positionGap
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2)
    (positionGap : value ∈
      locallyConstantFace burnolUnscaledCommonGapRadius) :
    burnolAmbientCompletedMellinEvaluator coordinate value =
      ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (-coordinate.value) * value x := by
  let radius := burnolUnscaledCommonGapRadius
  have positive : 0 < radius := by
    norm_num [radius, burnolUnscaledCommonGapRadius]
  obtain ⟨coefficient, gap⟩ :=
    mem_locallyConstantFace_iff_exists.mp positionGap
  have coefficientRead :
      burnolAmbientGapCoefficient radius value = coefficient :=
    divisionJet_ambientGapCoefficient_eq radius positive value coefficient gap
  have exponent : -1 < (-coordinate.value).re := by
    simp only [neg_re]
    linarith [coordinate.belowOne]
  have powerIntegrable : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-coordinate.value)) (Ioc 0 radius) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le positive.le).mp
      (intervalIntegral.intervalIntegrable_cpow' exponent)
  have gapIntegrable : IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (-coordinate.value) * value x) (Ioc 0 radius) := by
    apply (powerIntegrable.mul_const coefficient).congr
    filter_upwards [divisionJet_value_ae_eq_gapCoefficient_on_Ioc
      radius positive value coefficient gap] with x valueRead
    rw [valueRead]
  have tailIntegrable : IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (-coordinate.value) * value x) (Ioi radius) :=
    burnolRadiusMellinWeight_integrableOn_tail radius positive
      coordinate.value coordinate.rightHalf value
  have gapIntegral :
      (∫ x : ℝ in Ioc 0 radius,
        (x : ℂ) ^ (-coordinate.value) * value x) =
      burnolRadiusMellinGapMoment radius coordinate.value * coefficient := by
    calc
      _ = ∫ x : ℝ in Ioc 0 radius,
          (x : ℂ) ^ (-coordinate.value) * coefficient := by
        apply integral_congr_ae
        filter_upwards [divisionJet_value_ae_eq_gapCoefficient_on_Ioc
          radius positive value coefficient gap] with x valueRead
        rw [valueRead]
      _ = (∫ x : ℝ in Ioc 0 radius,
          (x : ℂ) ^ (-coordinate.value)) * coefficient := by
        rw [integral_mul_const]
      _ = _ := by
        rw [← intervalIntegral.integral_of_le positive.le,
          integral_cpow (Or.inl exponent)]
        unfold burnolRadiusMellinGapMoment
        have denominatorNe : 1 - coordinate.value ≠ 0 := by
          intro zero
          have one : coordinate.value = 1 := (sub_eq_zero.mp zero).symm
          have below := coordinate.belowOne
          rw [one] at below
          norm_num at below
        rw [show -coordinate.value + 1 = 1 - coordinate.value by ring,
          Complex.ofReal_zero, zero_cpow denominatorNe, sub_zero]
  unfold burnolAmbientCompletedMellinEvaluator
    burnolRadiusAmbientCompletedMellinEvaluator
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [coefficientRead,
    burnolRadiusMellinTailEvaluator_eq_integral]
  rw [← Ioc_union_Ioi_eq_Ioi positive.le,
    setIntegral_union (by
      rw [Set.disjoint_left]
      intro x first second
      exact (not_lt_of_ge first.2) second)
      measurableSet_Ioi gapIntegrable tailIntegrable,
    gapIntegral]

private theorem divisionJet_ambientPositiveIntegral_eq_mellin
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    (∫ x : ℝ in Ioi 0,
      (x : ℂ) ^ (-coordinate.value) * value x) =
      mellin (value : ℝ → ℂ) (1 - coordinate.value) := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [smul_eq_mul]
  congr 1
  ring

/-- Contracting dilation acts on the honest ambient Mellin read by its full
Mellin character. -/
theorem burnolAmbientCompletedMellinEvaluator_dilation_of_positionGap
    (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonpositive : h ≤ 0)
    (value : BurnolL2)
    (positionGap : value ∈
      locallyConstantFace burnolUnscaledCommonGapRadius) :
    burnolAmbientCompletedMellinEvaluator coordinate
        (burnolMultiplicativeDilation h value) =
      Complex.exp
        ((coordinate.value - (1 / 2 : ℂ)) * (h : ℂ)) *
        burnolAmbientCompletedMellinEvaluator coordinate value := by
  have positive : 0 < burnolUnscaledCommonGapRadius := by
    norm_num [burnolUnscaledCommonGapRadius]
  have targetGap := burnolMultiplicativeDilation_mem_locallyConstantFace_of_nonpositive
    burnolUnscaledCommonGapRadius positive h nonpositive value positionGap
  rw [burnolAmbientCompletedMellinEvaluator_eq_positive_integral_of_positionGap
      coordinate _ targetGap,
    burnolAmbientCompletedMellinEvaluator_eq_positive_integral_of_positionGap
      coordinate value positionGap,
    divisionJet_ambientPositiveIntegral_eq_mellin,
    divisionJet_ambientPositiveIntegral_eq_mellin]
  have dilationAE := burnolMultiplicativeDilation_coeFn h value
  have mellinAE :
      mellin (burnolMultiplicativeDilation h value : ℝ → ℂ)
          (1 - coordinate.value) =
        mellin (fun x : ℝ =>
          (Real.exp (h / 2) : ℂ) * value (Real.exp h * x))
          (1 - coordinate.value) := by
    unfold mellin
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae dilationAE] with x read
    simp only [smul_eq_mul]
    rw [read]
    rfl
  rw [mellinAE]
  have scaled := mellin_comp_mul_left
    (value : ℝ → ℂ) (1 - coordinate.value) (Real.exp_pos h)
  rw [show (fun x : ℝ =>
      (Real.exp (h / 2) : ℂ) * value (Real.exp h * x)) =
    fun x : ℝ => (Real.exp (h / 2) : ℂ) •
      value (Real.exp h * x) by
        funext x
        rfl,
    mellin_const_smul, scaled]
  simp only [smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h)),
    ← Complex.ofReal_log (Real.exp_pos h).le, Real.log_exp,
    Complex.ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem divisionJet_ambientDilationExp_eq_quarterCharacter
    (w : ℂ) (shift : ℝ) :
    Complex.exp
        (((2 * w) - (1 / 2 : ℂ)) * ((-shift / 2 : ℝ) : ℂ)) =
      quarterDilationCharacter w (Real.exp shift) := by
  unfold quarterDilationCharacter
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero shift)),
    ← Complex.ofReal_log (Real.exp_pos shift).le, Real.log_exp]
  congr 1
  push_cast
  ring

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
