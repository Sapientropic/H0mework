import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.UnitShellPrimitive

/-! The original reciprocal step wave extends to both annulus endpoints through its actual dilation family. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

private theorem burnolUnitReciprocalPrimitive_scale (scale x : ℝ) (positive : 0 < scale)
    (nonzero : x ≠ 0) :
    (scale : ℂ) * burnolUnitReciprocalPrimitiveRaw (scale * x) =
      if |x|⁻¹ < scale then ((|x| : ℝ) : ℂ)⁻¹ else 0 := by
  have absPositive := abs_pos.mpr nonzero
  have incidence : 1 < |scale * x| ↔ |x|⁻¹ < scale := by
    rw [abs_mul, abs_of_pos positive, inv_eq_one_div, div_lt_iff₀ absPositive]
  unfold burnolUnitReciprocalPrimitiveRaw
  simp only [incidence]
  split_ifs
  · rw [abs_mul, abs_of_pos positive, Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne', Complex.ofReal_ne_zero.mpr absPositive.ne']
  · exact mul_zero _

theorem burnolSourceScaleReciprocalPrimitive_coeFn (scale : ℝ) (positive : 0 < scale) :
    (burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 scale : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => if |x|⁻¹ < scale then ((|x| : ℝ) : ℂ)⁻¹ else 0 := by
  filter_upwards [burnolSourceScalePrimitive_coeFn burnolUnitReciprocalPrimitiveL2
    burnolUnitReciprocalPrimitiveRaw burnolUnitReciprocalPrimitive_coeFn scale positive] with x actual
  rw [actual]
  by_cases zero : x = 0
  · simp [zero, burnolUnitReciprocalPrimitiveRaw]
  · exact burnolUnitReciprocalPrimitive_scale scale x positive zero

theorem burnolUnitReciprocalPrimitive_difference (lower upper x : ℝ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) :
    (upper : ℂ) * burnolUnitReciprocalPrimitiveRaw (upper * x) -
      (lower : ℂ) * burnolUnitReciprocalPrimitiveRaw (lower * x) =
        burnolReciprocalStepSourceRaw lower upper x := by
  by_cases zero : x = 0
  · simp [zero, burnolUnitReciprocalPrimitiveRaw, burnolReciprocalStepSourceRaw, lowerPositive.not_ge]
  rw [burnolUnitReciprocalPrimitive_scale upper x (lowerPositive.trans_le ordered) zero,
    burnolUnitReciprocalPrimitive_scale lower x lowerPositive zero]
  unfold burnolReciprocalStepSourceRaw
  by_cases high : |x|⁻¹ < upper
  · by_cases low : |x|⁻¹ < lower
    · simp [high, low, not_le_of_gt low]
    · simp [high, low, le_of_not_gt low]
  · have low : ¬ |x|⁻¹ < lower := fun h => high (h.trans_le ordered)
    simp [high, low]

theorem burnolUnitCountingPrimitive_difference (lower upper x : ℝ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) :
    (upper : ℂ) * burnolUnitCountingPrimitiveRaw (upper * x) -
      (lower : ℂ) * burnolUnitCountingPrimitiveRaw (lower * x) =
        burnolReciprocalStepWaveRaw lower upper x := by
  by_cases zero : x = 0
  · simp [zero, burnolUnitCountingPrimitiveRaw, burnolReciprocalStepWaveRaw, burnolReciprocalStepWaveReal]
    ring
  have upperPositive := lowerPositive.trans_le ordered
  have lowerNonzero := mul_ne_zero lowerPositive.ne' zero
  have upperNonzero := mul_ne_zero upperPositive.ne' zero
  have ceilOrder : ⌈lower * |x|⌉₊ ≤ ⌈upper * |x|⌉₊ :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right ordered (abs_nonneg x))
  simp only [burnolUnitCountingPrimitiveRaw, if_neg lowerNonzero, if_neg upperNonzero,
    burnolReciprocalStepWaveRaw, burnolReciprocalStepWaveReal, if_neg zero,
    burnolReciprocalStepChannels, Nat.card_Ico, Nat.cast_sub ceilOrder,
    abs_mul, abs_of_pos lowerPositive, abs_of_pos upperPositive]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr lowerPositive.ne',
    Complex.ofReal_ne_zero.mpr upperPositive.ne', Complex.ofReal_ne_zero.mpr (abs_pos.mpr zero).ne']
  ring

def burnolReciprocalStepNativeSource (lower upper : ℝ) : BurnolL2 :=
  burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 upper - burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 lower

def burnolReciprocalStepNativeWave (lower upper : ℝ) : BurnolL2 :=
  burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 upper - burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 lower

theorem burnolReciprocalStepNativeSource_eq (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) :
    burnolReciprocalStepNativeSource lower upper =
      burnolReciprocalStepSourceL2 lower upper lowerPositive ordered := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 upper)
    (burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 lower),
    burnolSourceScalePrimitive_coeFn burnolUnitReciprocalPrimitiveL2 burnolUnitReciprocalPrimitiveRaw
      burnolUnitReciprocalPrimitive_coeFn upper (lowerPositive.trans_le ordered),
    burnolSourceScalePrimitive_coeFn burnolUnitReciprocalPrimitiveL2 burnolUnitReciprocalPrimitiveRaw
      burnolUnitReciprocalPrimitive_coeFn lower lowerPositive,
    (burnolReciprocalStepSource_memLp lower upper lowerPositive ordered).coeFn_toLp]
      with x differenceAt upperAt lowerAt stepAt
  change (burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 upper -
    burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 lower : BurnolL2) x = _
  rw [differenceAt]
  change burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 upper x -
    burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 lower x = _
  rw [upperAt, lowerAt]
  exact (burnolUnitReciprocalPrimitive_difference lower upper x lowerPositive ordered).trans stepAt.symm

theorem burnolReciprocalStepNativeWave_eq (lower upper : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) :
    burnolReciprocalStepNativeWave lower upper =
      burnolReciprocalStepWaveL2 lower upper lowerPositive ordered := by
  have unitRead : (burnolUnitCountingPrimitiveL2 : ℝ → ℂ) =ᵐ[volume] burnolUnitCountingPrimitiveRaw :=
    burnolUnitCountingPrimitive_memLp.coeFn_toLp
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 upper)
    (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 lower),
    burnolSourceScalePrimitive_coeFn burnolUnitCountingPrimitiveL2 burnolUnitCountingPrimitiveRaw
      unitRead upper (lowerPositive.trans_le ordered),
    burnolSourceScalePrimitive_coeFn burnolUnitCountingPrimitiveL2 burnolUnitCountingPrimitiveRaw unitRead lower lowerPositive,
    (burnolReciprocalStepWave_memLp lower upper lowerPositive ordered).coeFn_toLp]
      with x differenceAt upperAt lowerAt stepAt
  change (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 upper -
    burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 lower : BurnolL2) x = _
  rw [differenceAt]
  change burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 upper x -
    burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 lower x = _
  rw [upperAt, lowerAt]
  exact (burnolUnitCountingPrimitive_difference lower upper x lowerPositive ordered).trans stepAt.symm

/-- Only the original Pa inclusion into its original ambient L². -/
def burnolOriginalPaInL2 : Submodule ℂ BurnolL2 :=
  burnolCompactCoPoissonClosedRange.toSubmodule.map
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtype

theorem burnolOriginalPaInL2_closed : IsClosed (burnolOriginalPaInL2 : Set BurnolL2) := by
  change IsClosed ((fun value : BurnolPaAmbientCarrier => (value : BurnolL2)) ''
    (burnolCompactCoPoissonClosedRange : Set BurnolPaAmbientCarrier))
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isClosedMap_subtype_val _
    burnolCompactCoPoissonClosedRange.isClosed

private theorem burnolReciprocalStepNativeWave_openPa (lower upper : ℝ)
    (lowerStrict : (1 / 4 : ℝ) < lower) (ordered : lower ≤ upper) (upperStrict : upper < 4) :
    burnolReciprocalStepNativeWave lower upper ∈ burnolOriginalPaInL2 := by
  refine Submodule.mem_map.mpr ⟨burnolReciprocalStepPhysicalState lower upper lowerStrict ordered upperStrict.le,
    burnolReciprocalStepWave_memPa lower upper lowerStrict ordered upperStrict, ?_⟩
  exact (burnolReciprocalStepNativeWave_eq lower upper (lt_trans (by norm_num) lowerStrict) ordered).symm

theorem burnolReciprocalStepNativeWave_closedPa (lower upper : ℝ)
    (lowerIn : lower ∈ Icc (1 / 4 : ℝ) 4) (upperIn : upper ∈ Icc (1 / 4 : ℝ) 4) :
    burnolReciprocalStepNativeWave lower upper ∈ burnolOriginalPaInL2 := by
  have interior : MapsTo (burnolReciprocalStepNativeWave 1) (Ioo (1 / 4 : ℝ) 4)
      (burnolOriginalPaInL2 : Set BurnolL2) := by
    intro t inside
    by_cases forward : 1 ≤ t
    · exact burnolReciprocalStepNativeWave_openPa 1 t (by norm_num) forward inside.2
    · have backward := burnolReciprocalStepNativeWave_openPa t 1 inside.1 (le_of_not_ge forward) (by norm_num)
      have reversed : burnolReciprocalStepNativeWave 1 t = -burnolReciprocalStepNativeWave t 1 := by
        unfold burnolReciprocalStepNativeWave
        abel
      rw [reversed]
      exact burnolOriginalPaInL2.neg_mem backward
  have continuous : ContinuousOn (burnolReciprocalStepNativeWave 1) (closure (Ioo (1 / 4 : ℝ) 4)) := by
    rw [closure_Ioo (by norm_num : (1 / 4 : ℝ) ≠ 4)]
    exact ((burnolSourceScalePrimitive_continuous burnolUnitCountingPrimitiveL2).mono
      (fun _ inside => lt_of_lt_of_le (by norm_num) inside.1)).sub continuousOn_const
  have boundary := interior.closure_of_continuousOn continuous
  rw [closure_Ioo (by norm_num : (1 / 4 : ℝ) ≠ 4), burnolOriginalPaInL2_closed.closure_eq] at boundary
  have difference : burnolReciprocalStepNativeWave lower upper =
      burnolReciprocalStepNativeWave 1 upper - burnolReciprocalStepNativeWave 1 lower := by
    unfold burnolReciprocalStepNativeWave
    abel
  rw [difference]
  exact burnolOriginalPaInL2.sub_mem (boundary upperIn) (boundary lowerIn)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
