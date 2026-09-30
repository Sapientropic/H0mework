import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.UnitResponseIntegral

/-! The original unit tail is the actual weighted primitive source and its L² co-Poisson response. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem burnolUnitTailSlope_measurable (coordinate : BurnolCompletedMellinCoordinate) :
    Measurable (burnolUnitTailSlope coordinate) := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  intro u nonzero
  exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const u (coordinate.value - 2)
    (Or.inr nonzero))).continuousWithinAt

theorem burnolUnitTailWeight_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (u : ℝ) (positive : 0 < u) :
    HasDerivAt (burnolUnitPowerWeight coordinate) (burnolUnitTailSlope coordinate u) u := by
  have exponentNonzero : coordinate.value - 1 ≠ 0 := by
    intro zero
    have equal := sub_eq_zero.mp zero
    have below := coordinate.belowOne
    rw [equal] at below
    norm_num at below
  have derivative := (hasDerivAt_ofReal_cpow_const positive.ne' exponentNonzero).neg
  unfold burnolUnitPowerWeight burnolUnitTailSlope
  rw [neg_mul, show coordinate.value - 2 = coordinate.value - 1 - 1 by ring]
  exact derivative

def burnolReciprocalPrimitiveProfile (scale x : ℝ) : ℂ :=
  if |x|⁻¹ < scale then ((|x| : ℝ) : ℂ)⁻¹ else 0

theorem burnolUnitTailPrimitive_rawIntegral (coordinate : BurnolCompletedMellinCoordinate)
    (upper x : ℝ) :
    burnolUnitPowerWeight coordinate upper * burnolReciprocalPrimitiveProfile upper x -
      (∫ u : ℝ in Ioc 0 upper, burnolUnitTailSlope coordinate u * burnolReciprocalPrimitiveProfile u x) =
        burnolUnitPowerWeight coordinate (|x|⁻¹) * burnolReciprocalPrimitiveProfile upper x := by
  by_cases zero : x = 0
  · simp [zero, burnolReciprocalPrimitiveProfile]
  let t := |x|⁻¹
  have tPositive : 0 < t := inv_pos.mpr (abs_pos.mpr zero)
  by_cases active : t < upper
  · have functionRead : (fun u : ℝ => burnolUnitTailSlope coordinate u * burnolReciprocalPrimitiveProfile u x) =
        (Ioi t).indicator (fun u => burnolUnitTailSlope coordinate u * ((|x| : ℝ) : ℂ)⁻¹) := by
      funext u
      simp only [burnolReciprocalPrimitiveProfile, indicator_apply, mem_Ioi, mul_ite, mul_zero, t]
    have intersection : Ioi t ∩ Ioc 0 upper = Ioc t upper := by
      ext u
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, tPositive.trans h.1, h.2⟩⟩
    have integralRead : (∫ u : ℝ in Ioc 0 upper,
        burnolUnitTailSlope coordinate u * burnolReciprocalPrimitiveProfile u x) =
        (burnolUnitPowerWeight coordinate upper - burnolUnitPowerWeight coordinate t) *
          ((|x| : ℝ) : ℂ)⁻¹ := by
      rw [functionRead, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        intersection, integral_mul_const, ← intervalIntegral.integral_of_le active.le]
      have regular : ContinuousOn (burnolUnitTailSlope coordinate) (Icc t upper) :=
        (burnolUnitTailSlope_continuous coordinate).mono (fun _ inside => tPositive.trans_le inside.1)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u hu => burnolUnitTailWeight_derivative coordinate u (tPositive.trans_le (by
          simpa only [min_eq_left active.le] using hu.1)))
        (regular.intervalIntegrable_of_Icc active.le)]
    have baseRead : burnolReciprocalPrimitiveProfile upper x = ((|x| : ℝ) : ℂ)⁻¹ := if_pos active
    rw [integralRead, baseRead]
    change burnolUnitPowerWeight coordinate upper * _ -
      (burnolUnitPowerWeight coordinate upper - burnolUnitPowerWeight coordinate t) * _ =
        burnolUnitPowerWeight coordinate t * _
    ring
  · have empty : ∀ u ∈ Ioc 0 upper, burnolReciprocalPrimitiveProfile u x = 0 := by
      intro u inside
      exact if_neg (fun hu => active (hu.trans_le inside.2))
    have baseZero : burnolReciprocalPrimitiveProfile upper x = 0 := if_neg active
    rw [baseZero, mul_zero, mul_zero,
      setIntegral_eq_zero_of_forall_eq_zero (fun u inside => by rw [empty u inside, mul_zero]), sub_zero]

theorem burnolUnitTailPrimitive_source_pairing (coordinate : BurnolCompletedMellinCoordinate) (upper : ℝ)
    (positive : 0 < upper) (test : BurnolL2) :
    inner ℂ test (burnolUnitTailPrimitiveValue coordinate burnolUnitReciprocalPrimitiveL2 upper) =
      ∫ x : ℝ, inner ℂ (test x)
        (burnolUnitPowerWeight coordinate (|x|⁻¹) * burnolReciprocalPrimitiveProfile upper x) := by
  let family := fun u : ℝ => burnolUnitTailSlope coordinate u •
    burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 u
  let raw := fun point : ℝ × ℝ => burnolUnitTailSlope coordinate point.1 * burnolReciprocalPrimitiveProfile point.1 point.2
  have rawMeasurable : Measurable raw := by
    have reciprocal : Measurable (fun point : ℝ × ℝ => |point.2|⁻¹) := by fun_prop
    exact ((burnolUnitTailSlope_measurable coordinate).comp measurable_fst).mul
      (Measurable.ite (measurableSet_lt reciprocal measurable_fst) (by fun_prop) measurable_const)
  have sourceRead : ∀ᵐ u ∂volume.restrict (Ioc 0 upper), (family u : ℝ → ℂ) =ᵐ[volume]
      fun x => raw (u, x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    filter_upwards [Lp.coeFn_smul (burnolUnitTailSlope coordinate u)
      (burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 u),
      burnolSourceScaleReciprocalPrimitive_coeFn u inside.1] with x smulAt profileAt
    change (burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 u : BurnolL2) x = _
    rw [smulAt]
    change burnolUnitTailSlope coordinate u * burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 u x = _
    rw [profileAt]
    rfl
  have actual := burnolL2Bochner_pairing_raw (volume.restrict (Ioc 0 upper)) family
    (burnolUnitTailSlope_integrable coordinate burnolUnitReciprocalPrimitiveL2 upper) raw rawMeasurable sourceRead test
  have headRead : (burnolUnitPowerWeight coordinate upper •
      burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 upper : BurnolL2) =ᵐ[volume]
      fun x : ℝ => burnolUnitPowerWeight coordinate upper * burnolReciprocalPrimitiveProfile upper x := by
    filter_upwards [Lp.coeFn_smul (burnolUnitPowerWeight coordinate upper)
      (burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 upper),
      burnolSourceScaleReciprocalPrimitive_coeFn upper positive] with x smulAt profileAt
    rw [smulAt]
    change burnolUnitPowerWeight coordinate upper *
      burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 upper x = _
    rw [profileAt]
    rfl
  have headIntegrable := (L2.integrable_inner (𝕜 := ℂ) test
    (burnolUnitPowerWeight coordinate upper • burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 upper)).congr
      (headRead.mono (fun x hx => congrArg (inner ℂ (test x)) hx))
  have headPairing : inner ℂ test (burnolUnitPowerWeight coordinate upper •
      burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 upper) =
      ∫ x : ℝ, inner ℂ (test x) (burnolUnitPowerWeight coordinate upper * burnolReciprocalPrimitiveProfile upper x) := by
    rw [L2.inner_def]
    exact integral_congr_ae (headRead.mono (fun x hx => congrArg (inner ℂ (test x)) hx))
  rw [burnolUnitTailPrimitiveValue, inner_sub_right, headPairing, actual.2,
    ← integral_sub headIntegrable actual.1]
  apply integral_congr_ae
  filter_upwards with x
  rw [← inner_sub_right]
  exact congrArg (inner ℂ (test x)) (burnolUnitTailPrimitive_rawIntegral coordinate upper x)

theorem burnolUnitTailPrimitive_source_eq_tail (coordinate : BurnolCompletedMellinCoordinate) (upper : ℝ)
    (positive : 0 < upper) :
    burnolUnitTailPrimitiveValue coordinate burnolUnitReciprocalPrimitiveL2 upper =
      burnolRadiusNormalizedUnitTail coordinate upper⁻¹ (inv_pos.mpr positive) := by
  apply ext_inner_left ℂ
  intro test
  rw [burnolUnitTailPrimitive_source_pairing coordinate upper positive, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolRadiusUnitTail_coeFn coordinate upper⁻¹ (inv_pos.mpr positive)] with x tailAt
  rw [tailAt]
  apply congrArg (inner ℂ (test x))
  by_cases zero : x = 0
  · simp only [zero, abs_zero, inv_zero, burnolReciprocalPrimitiveProfile, Complex.ofReal_zero, if_pos positive, mul_zero]
    rw [if_neg (not_lt.mpr (inv_pos.mpr positive).le)]
  · have condition : upper⁻¹ < |x| ↔ |x|⁻¹ < upper := by
      simpa only [inv_inv] using (inv_lt_inv₀ (abs_pos.mpr zero) (inv_pos.mpr positive)).symm
    simp only [burnolReciprocalPrimitiveProfile, condition]
    split_ifs
    · exact burnolUnitPowerWeight_reciprocal coordinate zero
    · exact mul_zero _

def burnolUnitTailResponse (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) : BurnolL2 :=
  burnolUnitTailPrimitiveValue coordinate burnolUnitCountingPrimitiveL2 radius⁻¹

theorem burnolUnitTailResponse_realizes (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius⁻¹ ≤ 4) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolRadiusNormalizedUnitTail coordinate radius positive) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolUnitTailResponse coordinate radius)) test := by
  have actual := burnolUnitTailPrimitive_realizes coordinate radius⁻¹ (inv_pos.mpr positive) bounded test
  rw [burnolUnitTailPrimitive_source_eq_tail coordinate radius⁻¹ (inv_pos.mpr positive)] at actual
  simpa only [inv_inv, burnolUnitTailResponse] using actual

theorem burnolOriginalUnitTail_realizes (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolNormalizedFirstSourceUnitTail coordinate) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolUnitTailResponse coordinate 4)) test :=
  burnolUnitTailResponse_realizes coordinate 4 (by norm_num) (by norm_num) test

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
