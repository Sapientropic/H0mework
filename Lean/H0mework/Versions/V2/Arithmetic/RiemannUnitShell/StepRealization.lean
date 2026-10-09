import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.L2

/-! The same counted source generates its co-Poisson, Tate and physical faces. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem burnolReciprocalStepSource_reciprocalMean (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)⁻¹ * burnolReciprocalStepSourceRaw lower upper x) = (upper - lower : ℂ) := by
  have upperPositive := lowerPositive.trans_le ordered
  have intervalOrder : upper⁻¹ ≤ lower⁻¹ := (inv_le_inv₀ upperPositive lowerPositive).mpr ordered
  have inversePositive : 0 < upper⁻¹ := inv_pos.mpr upperPositive
  have read : (fun x : ℝ => (Ioi (0 : ℝ)).indicator
      (fun x => (x : ℂ)⁻¹ * burnolReciprocalStepSourceRaw lower upper x) x) =
      (Ioc upper⁻¹ lower⁻¹).indicator (fun x : ℝ => (x : ℂ) ^ (-2 : ℂ)) := by
    funext x
    by_cases positive : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from positive)]
      have incidence : lower ≤ x⁻¹ ∧ x⁻¹ < upper ↔ x ∈ Ioc upper⁻¹ lower⁻¹ := by
        rw [mem_Ioc]
        have first : lower ≤ x⁻¹ ↔ x ≤ lower⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div, le_div_iff₀ positive, le_div_iff₀ lowerPositive]
          constructor <;> intro h <;> nlinarith
        have second : x⁻¹ < upper ↔ upper⁻¹ < x := by
          rw [inv_eq_one_div, inv_eq_one_div, div_lt_iff₀ positive, div_lt_iff₀ upperPositive]
          constructor <;> intro h <;> nlinarith
        rw [first, second, and_comm]
      unfold burnolReciprocalStepSourceRaw
      rw [abs_of_pos positive]
      simp only [incidence, indicator_apply]
      split_ifs
      · simp only [Complex.cpow_neg, Complex.cpow_ofNat, pow_two, mul_inv_rev]
      · exact mul_zero _
    · have outside : x ∉ Ioc upper⁻¹ lower⁻¹ := by
        intro belongs
        exact positive (inversePositive.trans belongs.1)
      rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from positive), indicator_of_notMem outside]
  rw [← integral_indicator measurableSet_Ioi, read, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le intervalOrder]
  have zeroOutside : (0 : ℝ) ∉ uIcc upper⁻¹ lower⁻¹ := by
    rw [uIcc_of_le intervalOrder]
    intro inside
    exact not_le_of_gt inversePositive inside.1
  rw [integral_cpow (Or.inr ⟨by norm_num, zeroOutside⟩)]
  norm_num [Complex.cpow_neg_one, Complex.ofReal_inv]
  ring

theorem burnolReciprocalStepSource_realizes (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) (upperBound : upper ≤ 4) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolReciprocalStepSourceL2 lower upper lowerPositive ordered) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolReciprocalStepWaveL2 lower upper lowerPositive ordered)) test := by
  have quarterBound : (1 / 4 : ℝ) ≤ upper⁻¹ := by
    have positive := lowerPositive.trans_le ordered
    exact (by norm_num : (1 / 4 : ℝ) = (4 : ℝ)⁻¹) ▸
      (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) positive).mpr upperBound
  have rawGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → burnolReciprocalStepSourceRaw lower upper x = 0 := by
    intro x small
    exact burnolReciprocalStepSource_innerGap lower upper lowerPositive ordered (small.trans quarterBound)
  have even : ∀ x : ℝ, burnolReciprocalStepSourceRaw lower upper (-x) = burnolReciprocalStepSourceRaw lower upper x := by
    intro x
    simp only [burnolReciprocalStepSourceRaw, abs_neg]
  have sourceRep : (burnolReciprocalStepSourceL2 lower upper lowerPositive ordered : ℝ → ℂ) =ᵐ[volume]
      burnolReciprocalStepSourceRaw lower upper :=
    (burnolReciprocalStepSource_memLp lower upper lowerPositive ordered).coeFn_toLp
  rw [burnolRemainderSourceRead_innerGap_forward
    (burnolReciprocalStepSourceL2 lower upper lowerPositive ordered) (burnolReciprocalStepSourceRaw lower upper)
    (burnolReciprocalStepSource_measurable lower upper) sourceRep rawGap even test,
    burnolReciprocalStepSource_reciprocalMean lower upper lowerPositive ordered]
  simp_rw [← burnolReciprocalStepWave_coSum lower upper _ lowerPositive]
  rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(burnolReciprocalStepWave_memLp lower upper lowerPositive ordered).coeFn_toLp] with x hx
  have read : burnolReciprocalStepWaveL2 lower upper lowerPositive ordered x = burnolReciprocalStepWaveRaw lower upper x := hx
  rw [read]
  rfl

theorem burnolRemainderRealization_fourier (source value : BurnolL2)
    (realizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) test) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolTateReciprocalL2 source) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierL2 value)) test := by
  rw [burnolRemainderSourceRead_fourier, realizes]
  exact congrArg (fun distribution : TemperedDistribution ℝ ℂ => distribution test)
    (Lp.fourier_toTemperedDistribution_eq value)

theorem burnolRemainderRealization_positionGap (source value : BurnolL2)
    (even : reflectL2 source = source)
    (gap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0)
    (realizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) test) :
    value ∈ locallyConstantFace (1 / 4 : ℝ) := by
  have rawRealizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test =
      ∫ x : ℝ, test x * value x := by
    intro test
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply,
      smul_eq_mul] using realizes test
  obtain ⟨raw, _, rawGap, valueRep⟩ :=
    burnolRemainderSourceRead_realization_ae source value even gap rawRealizes
  let coefficient := -(∫ x : ℝ in Ioi 0, (x : ℂ)⁻¹ * raw x)
  refine mem_locallyConstantFace_iff_exists.mpr ⟨coefficient, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul coefficient (intervalConstant (1 / 4 : ℝ)),
    intervalConstant_coeFn (1 / 4 : ℝ),
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (1 / 4 : ℝ)) value,
    ae_restrict_of_ae valueRep,
    ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))]
      with x hsmul hconstant hrestrict hvalue inside
  have restriction : restrictToInterval (1 / 4) value x = value x := hrestrict
  rw [hsmul]
  change coefficient * intervalConstant (1 / 4) x = _
  rw [hconstant, mul_one, restriction, hvalue,
    burnolInnerGapForward_innerGap raw rawGap (abs_le.mpr inside), zero_sub]

theorem burnolReflectL2_eq_of_even_raw (value : BurnolL2) (raw : ℝ → ℂ)
    (represents : (value : ℝ → ℂ) =ᵐ[volume] raw)
    (even : ∀ x, raw (-x) = raw x) : reflectL2 value = value := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving value negMeasurePreserving,
    represents, negMeasurePreserving.quasiMeasurePreserving.ae represents] with x href hvalue hraw
  have reflected : reflectL2 value x = value (-x) := href
  rw [reflected, hvalue, hraw, even]

theorem burnolReciprocalStepSource_tate_raw (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) :
    (burnolTateReciprocalL2 (burnolReciprocalStepSourceL2 lower upper lowerPositive ordered) : ℝ → ℂ) =ᵐ[volume]
      fun x => if lower ≤ |x| ∧ |x| < upper then (1 : ℂ) else 0 := by
  let source := burnolReciprocalStepSourceL2 lower upper lowerPositive ordered
  have sourceRep : (source : ℝ → ℂ) =ᵐ[volume] burnolReciprocalStepSourceRaw lower upper :=
    (burnolReciprocalStepSource_memLp lower upper lowerPositive ordered).coeFn_toLp
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp source)
    (burnolReciprocalStepSource_memLp lower upper lowerPositive ordered) sourceRep
  filter_upwards [burnolTateReciprocalL2_coeFn source, pulled] with x hread hraw
  rw [hread, hraw]
  unfold burnolTateReciprocalRaw burnolReciprocalStepSourceRaw
  simp only [abs_inv, inv_inv, Complex.ofReal_inv]
  split_ifs with active
  · have positive : 0 < |x| := lowerPositive.trans_le active.1
    simp [Complex.ofReal_ne_zero.mpr positive.ne']
  · exact mul_zero _

theorem burnolReciprocalStepWave_physical (lower upper : ℝ) (lowerStrict : (1 / 4 : ℝ) < lower)
    (ordered : lower ≤ upper) (upperBound : upper ≤ 4) :
    burnolReciprocalStepWaveL2 lower upper (lt_trans (by norm_num) lowerStrict) ordered ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  have lowerPositive : 0 < lower := lt_trans (by norm_num) lowerStrict
  let source := burnolReciprocalStepSourceL2 lower upper lowerPositive ordered
  let value := burnolReciprocalStepWaveL2 lower upper lowerPositive ordered
  have sourceRep : (source : ℝ → ℂ) =ᵐ[volume] burnolReciprocalStepSourceRaw lower upper :=
    (burnolReciprocalStepSource_memLp lower upper lowerPositive ordered).coeFn_toLp
  have valueRep : (value : ℝ → ℂ) =ᵐ[volume] burnolReciprocalStepWaveRaw lower upper :=
    (burnolReciprocalStepWave_memLp lower upper lowerPositive ordered).coeFn_toLp
  have sourceEven : reflectL2 source = source := burnolReflectL2_eq_of_even_raw source _ sourceRep
    (fun x => by simp only [burnolReciprocalStepSourceRaw, abs_neg])
  have valueEven : reflectL2 value = value := burnolReflectL2_eq_of_even_raw value _ valueRep
    (fun x => by simp only [burnolReciprocalStepWaveRaw, burnolReciprocalStepWaveReal, neg_eq_zero, burnolReciprocalStepChannels, abs_neg])
  have quarterBound : (1 / 4 : ℝ) ≤ upper⁻¹ := by
    have upperPositive := lowerPositive.trans_le ordered
    exact (by norm_num : (1 / 4 : ℝ) = (4 : ℝ)⁻¹) ▸
      (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) upperPositive).mpr upperBound
  have sourceGap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae sourceRep,
      ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))] with x hx inside
    rw [hx]
    exact burnolReciprocalStepSource_innerGap lower upper lowerPositive ordered
      ((abs_le.mpr inside).trans quarterBound)
  have dualRep := burnolReciprocalStepSource_tate_raw lower upper lowerPositive ordered
  have dualEven : reflectL2 (burnolTateReciprocalL2 source) = burnolTateReciprocalL2 source :=
    burnolReflectL2_eq_of_even_raw _ _ dualRep (fun x => by simp only [abs_neg])
  have dualGap : (burnolTateReciprocalL2 source : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae dualRep,
      ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))] with x hx inside
    rw [hx]
    have excluded : ¬ (lower ≤ |x| ∧ |x| < upper) := by
      intro active
      linarith [abs_le.mpr inside, active.1]
    exact if_neg excluded
  have realizes := burnolReciprocalStepSource_realizes lower upper lowerPositive ordered upperBound
  exact ⟨⟨burnolRemainderRealization_positionGap source value sourceEven sourceGap realizes,
    burnolRemainderRealization_positionGap _ _ dualEven dualGap (burnolRemainderRealization_fourier source value realizes)⟩,
    mem_evenL2ClosedFace_iff.mpr valueEven⟩

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
