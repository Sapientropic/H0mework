import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.StepCount
import H0mework.Versions.Y.Arithmetic.RemainderSource.BochnerPairing

/-! Weighted steps generate source and Pa wave together; the original remainder action commutes with their integral. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem burnolReciprocalStepRaw_weightedIntegral (lower upper x : ℝ) (f f' : ℝ → ℂ)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) :
    f upper * burnolReciprocalStepSourceRaw lower upper x -
      (∫ u : ℝ in Ioc lower upper, f' u * burnolReciprocalStepSourceRaw lower u x) =
        f (|x|⁻¹) * burnolReciprocalStepSourceRaw lower upper x := by
  let t := |x|⁻¹
  by_cases active : lower ≤ t ∧ t < upper
  · have tailRead : (∫ u : ℝ in Ioc lower upper, f' u * burnolReciprocalStepSourceRaw lower u x) =
        (f upper - f t) * ((|x| : ℝ) : ℂ)⁻¹ := by
      have integrand : (fun u : ℝ => f' u * burnolReciprocalStepSourceRaw lower u x) =
          (Ioi t).indicator (fun u => f' u * ((|x| : ℝ) : ℂ)⁻¹) := by
        funext u
        simp only [burnolReciprocalStepSourceRaw, active.1, true_and,
          indicator_apply, mem_Ioi, mul_ite, mul_zero, t]
      rw [integrand, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
      have intersection : Ioi t ∩ Ioc lower upper = Ioc t upper := by
        ext u
        simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
        constructor
        · rintro ⟨ht, _, hb⟩
          exact ⟨ht, hb⟩
        · rintro ⟨ht, hb⟩
          exact ⟨ht, active.1.trans_lt ht, hb⟩
      rw [intersection, integral_mul_const, ← intervalIntegral.integral_of_le active.2.le]
      have intervalRead : ∫ u : ℝ in t..upper, f' u = f upper - f t :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun u hu => derivative u (Icc_subset_Icc active.1 le_rfl (by
            simpa only [uIcc_of_le active.2.le] using hu)))
          ((regular.mono (Icc_subset_Icc active.1 le_rfl)).intervalIntegrable_of_Icc active.2.le)
      rw [intervalRead]
    rw [tailRead, burnolReciprocalStepSourceRaw, if_pos active]
    ring
  · have noRead : ∀ u ∈ Ioc lower upper, burnolReciprocalStepSourceRaw lower u x = 0 := by
      intro u inside
      have excluded : ¬ (lower ≤ t ∧ t < u) := fun hu => active ⟨hu.1, hu.2.trans_le inside.2⟩
      exact if_neg excluded
    rw [burnolReciprocalStepSourceRaw, if_neg active, mul_zero, mul_zero]
    rw [setIntegral_eq_zero_of_forall_eq_zero (fun u hu => by rw [noRead u hu, mul_zero]), sub_zero]

def burnolWeightedReciprocalStepSource (lower upper : ℝ) (f f' : ℝ → ℂ) : BurnolL2 :=
  f upper • burnolReciprocalStepNativeSource lower upper -
    ∫ u : ℝ in Ioc lower upper, f' u • burnolReciprocalStepNativeSource lower u

def burnolWeightedReciprocalStepWave (lower upper : ℝ) (f f' : ℝ → ℂ) : BurnolL2 :=
  f upper • burnolReciprocalStepNativeWave lower upper -
    ∫ u : ℝ in Ioc lower upper, f' u • burnolReciprocalStepNativeWave lower u

private theorem burnolReciprocalStepSource_rawRead (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) : (burnolReciprocalStepNativeSource lower upper : ℝ → ℂ) =ᵐ[volume]
      burnolReciprocalStepSourceRaw lower upper := by
  rw [burnolReciprocalStepNativeSource_eq lower upper lowerPositive ordered]
  exact (burnolReciprocalStepSource_memLp lower upper lowerPositive ordered).coeFn_toLp

private theorem weightedStepSource_integrable (lower upper : ℝ) (f' : ℝ → ℂ)
    (lowerPositive : 0 < lower) (regular : ContinuousOn f' (Icc lower upper)) :
    IntegrableOn (fun u => f' u • burnolReciprocalStepNativeSource lower u) (Ioc lower upper) := by
  have sourceContinuous : ContinuousOn (burnolReciprocalStepNativeSource lower) (Icc lower upper) :=
    ((burnolSourceScalePrimitive_continuous burnolUnitReciprocalPrimitiveL2).mono
      (fun _ inside => lowerPositive.trans_le inside.1)).sub continuousOn_const
  exact (regular.smul sourceContinuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem weightedStepSource_rawMeasurable (lower : ℝ) (f' : ℝ → ℂ)
    (measured : Measurable f') : Measurable (fun point : ℝ × ℝ =>
      f' point.1 * burnolReciprocalStepSourceRaw lower point.1 point.2) := by
  have reciprocal : Measurable (fun point : ℝ × ℝ => |point.2|⁻¹) := by fun_prop
  have condition : MeasurableSet {point : ℝ × ℝ | lower ≤ |point.2|⁻¹ ∧ |point.2|⁻¹ < point.1} :=
    (measurableSet_le measurable_const reciprocal).inter (measurableSet_lt reciprocal measurable_fst)
  exact (measured.comp measurable_fst).mul (Measurable.ite condition (by fun_prop) measurable_const)

theorem burnolWeightedReciprocalStepSource_pairing (lower upper : ℝ) (f f' : ℝ → ℂ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') (test : BurnolL2) :
    inner ℂ test (burnolWeightedReciprocalStepSource lower upper f f') =
      ∫ x : ℝ, inner ℂ (test x)
        (f (|x|⁻¹) * burnolReciprocalStepSourceRaw lower upper x) := by
  let family := fun u : ℝ => f' u • burnolReciprocalStepNativeSource lower u
  let raw := fun point : ℝ × ℝ => f' point.1 * burnolReciprocalStepSourceRaw lower point.1 point.2
  have familyRead : ∀ᵐ u ∂volume.restrict (Ioc lower upper),
      (family u : ℝ → ℂ) =ᵐ[volume] fun x => raw (u, x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    filter_upwards [Lp.coeFn_smul (f' u) (burnolReciprocalStepNativeSource lower u),
      burnolReciprocalStepSource_rawRead lower u lowerPositive inside.1.le] with x smulAt sourceAt
    change (f' u • burnolReciprocalStepNativeSource lower u : BurnolL2) x = _
    rw [smulAt]
    change f' u * burnolReciprocalStepNativeSource lower u x = _
    rw [sourceAt]
  have actual := burnolL2Bochner_pairing_raw (volume.restrict (Ioc lower upper)) family
    (weightedStepSource_integrable lower upper f' lowerPositive regular) raw
    (weightedStepSource_rawMeasurable lower f' measured) familyRead test
  have headRead : (f upper • burnolReciprocalStepNativeSource lower upper : BurnolL2) =ᵐ[volume]
      fun x : ℝ => f upper * burnolReciprocalStepSourceRaw lower upper x := by
    filter_upwards [Lp.coeFn_smul (f upper) (burnolReciprocalStepNativeSource lower upper),
      burnolReciprocalStepSource_rawRead lower upper lowerPositive ordered] with x smulAt sourceAt
    rw [smulAt]
    change f upper * burnolReciprocalStepNativeSource lower upper x = _
    rw [sourceAt]
  have headIntegrable := (L2.integrable_inner (𝕜 := ℂ) test
    (f upper • burnolReciprocalStepNativeSource lower upper)).congr
      (headRead.mono (fun x hx => congrArg (inner ℂ (test x)) hx))
  have headPairing : inner ℂ test (f upper • burnolReciprocalStepNativeSource lower upper) =
      ∫ x : ℝ, inner ℂ (test x) (f upper * burnolReciprocalStepSourceRaw lower upper x) := by
    rw [L2.inner_def]
    exact integral_congr_ae (headRead.mono (fun x hx => congrArg (inner ℂ (test x)) hx))
  rw [burnolWeightedReciprocalStepSource, inner_sub_right, headPairing, actual.2,
    ← integral_sub headIntegrable actual.1]
  apply integral_congr_ae
  filter_upwards with x
  rw [← inner_sub_right]
  exact congrArg (inner ℂ (test x))
    (burnolReciprocalStepRaw_weightedIntegral lower upper x f f' derivative regular)

theorem burnolWeightedReciprocalStepWave_inPa (lower upper : ℝ) (f f' : ℝ → ℂ)
    (lowerIn : lower ∈ Icc (1 / 4 : ℝ) 4) (upperIn : upper ∈ Icc (1 / 4 : ℝ) 4)
    (regular : ContinuousOn f' (Icc lower upper)) :
    burnolWeightedReciprocalStepWave lower upper f f' ∈ burnolOriginalPaInL2 := by
  have continuous : ContinuousOn (burnolReciprocalStepNativeWave lower) (Icc lower upper) :=
    ((burnolSourceScalePrimitive_continuous burnolUnitCountingPrimitiveL2).mono
      (fun _ inside => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
        (lowerIn.1.trans inside.1))).sub continuousOn_const
  have integralIn : (∫ u : ℝ in Ioc lower upper, f' u • burnolReciprocalStepNativeWave lower u) ∈
      burnolOriginalPaInL2 := by
    apply integral_mem_closedSubmodule ⟨burnolOriginalPaInL2, burnolOriginalPaInL2_closed⟩
      (volume.restrict (Ioc lower upper)) _
      ((regular.smul continuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    exact burnolOriginalPaInL2.smul_mem _ (burnolReciprocalStepNativeWave_closedPa lower u lowerIn
      ⟨lowerIn.1.trans inside.1.le, inside.2.trans upperIn.2⟩)
  exact burnolOriginalPaInL2.sub_mem
    (burnolOriginalPaInL2.smul_mem _ (burnolReciprocalStepNativeWave_closedPa lower upper lowerIn upperIn)) integralIn

theorem burnolWeightedReciprocalStepSource_realizes (lower upper : ℝ) (f f' : ℝ → ℂ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperBound : upper ≤ 4)
    (regular : ContinuousOn f' (Icc lower upper)) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolWeightedReciprocalStepSource lower upper f f') test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolWeightedReciprocalStepWave lower upper f f')) test := by
  have baseRead (u : ℝ) (orderedU : lower ≤ u) (upperU : u ≤ 4) (ψ : SchwartzMap ℝ ℂ) :
      burnolRemainderSourceRead (burnolReciprocalStepNativeSource lower u) ψ =
        (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolReciprocalStepNativeWave lower u)) ψ := by
    rw [burnolReciprocalStepNativeSource_eq lower u lowerPositive orderedU,
      burnolReciprocalStepNativeWave_eq lower u lowerPositive orderedU]
    exact burnolReciprocalStepSource_realizes lower u lowerPositive orderedU upperU ψ
  have valueContinuous : ContinuousOn (burnolReciprocalStepNativeWave lower) (Icc lower upper) :=
    ((burnolSourceScalePrimitive_continuous burnolUnitCountingPrimitiveL2).mono
      (fun _ inside => lowerPositive.trans_le inside.1)).sub continuousOn_const
  have familyRead : ∀ᵐ u ∂volume.restrict (Ioc lower upper), ∀ ψ : SchwartzMap ℝ ℂ,
      burnolRemainderSourceRead (f' u • burnolReciprocalStepNativeSource lower u) ψ =
        (Lp.toTemperedDistributionCLM ℂ volume 2 (f' u • burnolReciprocalStepNativeWave lower u)) ψ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    intro ψ
    rw [← burnolRemainderSourceReadCLM_apply, map_smul,
      burnolRemainderSourceReadCLM_apply, baseRead u inside.1.le (inside.2.trans upperBound)]
    simp only [map_smul, smul_apply, smul_eq_mul]
  have integralRead := burnolRemainderSourceRead_bochner (volume.restrict (Ioc lower upper))
    (fun u => f' u • burnolReciprocalStepNativeSource lower u)
    (fun u => f' u • burnolReciprocalStepNativeWave lower u)
    (weightedStepSource_integrable lower upper f' lowerPositive regular)
    ((regular.smul valueContinuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self) familyRead test
  rw [burnolWeightedReciprocalStepSource, ← burnolRemainderSourceReadCLM_apply, map_sub, map_smul,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    baseRead upper ordered upperBound, integralRead]
  simp only [burnolWeightedReciprocalStepWave, map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
