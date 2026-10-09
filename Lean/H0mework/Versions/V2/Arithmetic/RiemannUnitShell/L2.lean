import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.Count

/-! The counted source and its wave are literal square-integrable functions. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ContDiff
noncomputable section

private theorem reciprocalSquareTail_integrable (radius : ℝ) (positive : 0 < radius) :
    Integrable (fun x : ℝ => if radius < |x| then |x| ^ (-2 : ℝ) else 0) := by
  let tail : ℝ → ℝ := (Ioi radius).indicator (fun x => x ^ (-2 : ℝ))
  have tailIntegrable : Integrable tail :=
    ((integrableOn_Ioi_rpow_iff positive).mpr (by norm_num : (-2 : ℝ) < -1)
      ).integrable_indicator measurableSet_Ioi
  have reflected := tailIntegrable.comp_neg
  apply (tailIntegrable.add reflected).congr
  filter_upwards with x
  change tail x + tail (-x) = _
  unfold tail
  by_cases nonnegative : 0 ≤ x
  · have outside : -x ∉ Ioi radius := by simp only [mem_Ioi]; linarith
    rw [indicator_of_notMem outside, add_zero, abs_of_nonneg nonnegative]
    simp only [indicator_apply, mem_Ioi]
  · have outside : x ∉ Ioi radius := by simp only [mem_Ioi]; linarith
    rw [indicator_of_notMem outside, zero_add, abs_of_neg (lt_of_not_ge nonnegative)]
    simp only [indicator_apply, mem_Ioi]

theorem burnolReciprocalStepWave_memLp (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) : MemLp (burnolReciprocalStepWaveRaw lower upper) 2 volume := by
  have upperPositive : 0 < upper := lowerPositive.trans_le ordered
  let radius := upper⁻¹
  have radiusPositive : 0 < radius := inv_pos.mpr upperPositive
  have near : Integrable ((symmetricInterval radius).indicator (fun _ : ℝ => (upper - lower) ^ 2)) :=
    (continuous_const.continuousOn.integrableOn_compact
      (show IsCompact (symmetricInterval radius) from isCompact_Icc)).integrable_indicator
        (measurableSet_symmetricInterval radius)
  have tail := reciprocalSquareTail_integrable radius radiusPositive
  have envelope : Integrable (fun x : ℝ => if radius < |x| then |x| ^ (-2 : ℝ) else (upper - lower) ^ 2) := by
    apply (near.add tail).congr
    filter_upwards with x
    simp only [Pi.add_apply]
    by_cases outside : radius < |x|
    · have notInside : x ∉ symmetricInterval radius := fun hx => not_le_of_gt outside (abs_le.mpr hx)
      rw [indicator_of_notMem notInside, if_pos outside, zero_add, if_pos outside]
    · have inside : x ∈ symmetricInterval radius := abs_le.mp (le_of_not_gt outside)
      rw [indicator_of_mem inside, if_neg outside, add_zero, if_neg outside]
  apply (memLp_two_iff_integrable_sq_norm (burnolReciprocalStepWave_measurable lower upper).aestronglyMeasurable).mpr
  apply envelope.mono'
  · exact ((burnolReciprocalStepWave_measurable lower upper).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases outside : radius < |x|
    · rw [if_pos outside]
      have xPositive : 0 < |x| := radiusPositive.trans outside
      have bound := burnolReciprocalStepWave_bound lower upper x lowerPositive ordered (abs_pos.mp xPositive)
      rw [Real.rpow_neg (abs_nonneg x), Real.rpow_two, ← inv_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) bound 2
    · rw [if_neg outside, burnolReciprocalStepWave_small lower upper x lowerPositive ordered (le_of_not_gt outside),
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      nlinarith

theorem burnolReciprocalStepSource_measurable (lower upper : ℝ) :
    Measurable (burnolReciprocalStepSourceRaw lower upper) := by
  have reciprocalMeasurable : Measurable (fun x : ℝ => |x|⁻¹) := by fun_prop
  have scalarMeasurable : Measurable (fun x : ℝ => ((|x| : ℝ) : ℂ)⁻¹) := by fun_prop
  have event : MeasurableSet {x : ℝ | lower ≤ |x|⁻¹ ∧ |x|⁻¹ < upper} :=
    (measurableSet_le measurable_const reciprocalMeasurable).inter
      (measurableSet_lt reciprocalMeasurable measurable_const)
  exact Measurable.ite event scalarMeasurable measurable_const

theorem burnolReciprocalStepSource_innerGap (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) {x : ℝ} (small : |x| ≤ upper⁻¹) :
    burnolReciprocalStepSourceRaw lower upper x = 0 := by
  have upperPositive := lowerPositive.trans_le ordered
  have excluded : ¬ (lower ≤ |x|⁻¹ ∧ |x|⁻¹ < upper) := by
    intro active
    have positive : 0 < |x| := inv_pos.mp (lowerPositive.trans_le active.1)
    have upperStrict := active.2
    rw [inv_eq_one_div, div_lt_iff₀ positive] at upperStrict
    rw [inv_eq_one_div, le_div_iff₀ upperPositive] at small
    nlinarith
  exact if_neg excluded

theorem burnolReciprocalStepSource_memLp (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) : MemLp (burnolReciprocalStepSourceRaw lower upper) 2 volume := by
  have upperPositive := lowerPositive.trans_le ordered
  have bounded : MemLp ((symmetricInterval lower⁻¹).indicator (fun _ : ℝ => upper)) 2 volume :=
    memLp_indicator_const 2 (measurableSet_symmetricInterval lower⁻¹) upper
      (Or.inr (isCompact_Icc.measure_lt_top.ne))
  apply bounded.mono' (burnolReciprocalStepSource_measurable lower upper).aestronglyMeasurable
  filter_upwards with x
  by_cases active : lower ≤ |x|⁻¹ ∧ |x|⁻¹ < upper
  · have positive : 0 < |x| := inv_pos.mp (lowerPositive.trans_le active.1)
    have small : |x| ≤ lower⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ lowerPositive]
      have sourceLower := active.1
      rw [inv_eq_one_div, le_div_iff₀ positive] at sourceLower
      nlinarith
    rw [indicator_of_mem (show x ∈ symmetricInterval lower⁻¹ from abs_le.mp small)]
    unfold burnolReciprocalStepSourceRaw
    rw [if_pos active, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (abs_nonneg x)]
    exact active.2.le
  · unfold burnolReciprocalStepSourceRaw
    rw [if_neg active, norm_zero]
    exact indicator_nonneg (fun _ _ => upperPositive.le) x

def burnolReciprocalStepSourceL2 (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) : BurnolL2 :=
  (burnolReciprocalStepSource_memLp lower upper lowerPositive ordered).toLp (burnolReciprocalStepSourceRaw lower upper)

def burnolReciprocalStepWaveL2 (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) : BurnolL2 :=
  (burnolReciprocalStepWave_memLp lower upper lowerPositive ordered).toLp (burnolReciprocalStepWaveRaw lower upper)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
