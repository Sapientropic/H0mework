import H0mework.Versions.V2.Arithmetic.MellinProjection.GapTailDilation

/-! The difference of two actual gap-tail kernels is a compact, zero-mass window source. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace
noncomputable section

def burnolGapTailFiniteWindowRaw (lower upper : ℝ)
    (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star (burnolRadiusMellinGapMoment lower coordinate.value) * burnolGapRieszRaw lower x -
    star (burnolRadiusMellinGapMoment upper coordinate.value) * burnolGapRieszRaw upper x +
    (Ioc lower upper).indicator (fun t : ℝ => (t : ℂ) ^ (-star coordinate.value)) x

theorem burnolGapTailFiniteWindowRaw_zero_outside
    {lower upper : ℝ} (positive : 0 < lower) (ordered : lower ≤ upper)
    (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (outside : x ∉ symmetricInterval upper) :
    burnolGapTailFiniteWindowRaw lower upper coordinate x = 0 := by
  have lowerOutside : x ∉ symmetricInterval lower := by
    intro inside
    apply outside
    exact ⟨by linarith [inside.1], inside.2.trans ordered⟩
  have annulusOutside : x ∉ Ioc lower upper := by
    intro inside
    apply outside
    exact ⟨by linarith [inside.1, positive.trans_le ordered], inside.2⟩
  simp only [burnolGapTailFiniteWindowRaw, burnolGapRieszRaw,
    Set.indicator_of_notMem outside, Set.indicator_of_notMem lowerOutside,
    Set.indicator_of_notMem annulusOutside, mul_zero, sub_zero, add_zero]

theorem burnolGapTailFiniteWindowRaw_compactSupport
    {lower upper : ℝ} (positive : 0 < lower) (ordered : lower ≤ upper)
    (coordinate : BurnolCompletedMellinCoordinate) :
    HasCompactSupport (burnolGapTailFiniteWindowRaw lower upper coordinate) :=
  HasCompactSupport.intro isCompact_Icc
    (fun _ outside => burnolGapTailFiniteWindowRaw_zero_outside positive ordered coordinate outside)

theorem burnolGapTailFiniteWindow_ae_source
    {lower upper : ℝ} (positive : 0 < lower) (ordered : lower ≤ upper)
    (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolRadiusAmbientCompletedMellinKernelFormula lower positive coordinate -
        burnolRadiusAmbientCompletedMellinKernelFormula upper (positive.trans_le ordered) coordinate :
      BurnolL2) =ᵐ[volume] burnolGapTailFiniteWindowRaw lower upper coordinate := by
  let A := star (burnolRadiusMellinGapMoment lower coordinate.value) •
    burnolAmbientGapRieszVector lower
  let B := star (burnolRadiusMellinGapMoment upper coordinate.value) •
    burnolAmbientGapRieszVector upper
  let U := burnolRadiusMellinTailKernelL2 lower positive coordinate.value coordinate.rightHalf
  let V := burnolRadiusMellinTailKernelL2 upper (positive.trans_le ordered)
    coordinate.value coordinate.rightHalf
  change ((A + U - (B + V) : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (A + U) (B + V), Lp.coeFn_add A U, Lp.coeFn_add B V,
    Lp.coeFn_smul (star (burnolRadiusMellinGapMoment lower coordinate.value))
      (burnolAmbientGapRieszVector lower),
    Lp.coeFn_smul (star (burnolRadiusMellinGapMoment upper coordinate.value))
      (burnolAmbientGapRieszVector upper), burnolGapRiesz_ae_raw lower, burnolGapRiesz_ae_raw upper,
    MemLp.coeFn_toLp (burnolRadiusMellinTailKernelRaw_memLp positive
      coordinate.value coordinate.rightHalf),
    MemLp.coeFn_toLp (burnolRadiusMellinTailKernelRaw_memLp (positive.trans_le ordered)
      coordinate.value coordinate.rightHalf)] with x subRead aRead bRead
      lowerScalar upperScalar lowerGap upperGap lowerTail upperTail
  change U x = burnolRadiusMellinTailKernelRaw lower coordinate.value x at lowerTail
  change V x = burnolRadiusMellinTailKernelRaw upper coordinate.value x at upperTail
  change A x = _ at lowerScalar
  change B x = _ at upperScalar
  rw [subRead]
  change (A + U : BurnolL2) x - (B + V : BurnolL2) x = _
  rw [aRead, bRead]
  change A x + U x - (B x + V x) = _
  rw [lowerScalar, upperScalar, lowerTail, upperTail]
  simp only [Pi.smul_apply, smul_eq_mul, lowerGap, upperGap]
  unfold burnolGapTailFiniteWindowRaw burnolRadiusMellinTailKernelRaw
  by_cases low : lower < x
  · by_cases high : upper < x
    · simp [low, high, Set.mem_Ioc, not_le.mpr high]
    · simp [low, high, Set.mem_Ioc, le_of_not_gt high]
      ring
  · have high : ¬ upper < x := fun h => low (ordered.trans_lt h)
    simp [low, high, Set.mem_Ioc]

theorem burnolGapRieszRaw_integrable (radius : ℝ) :
    Integrable (burnolGapRieszRaw radius) := by
  unfold burnolGapRieszRaw
  apply Integrable.const_mul
  exact (integrableOn_const (C := (1 : ℂ)) (s := symmetricInterval radius)
    (by exact measure_Icc_lt_top.ne)).integrable_indicator (measurableSet_symmetricInterval radius)

theorem burnolGapRieszRaw_integral {radius : ℝ} (positive : 0 < radius) :
    (∫ x : ℝ, burnolGapRieszRaw radius x) = 1 := by
  unfold burnolGapRieszRaw
  rw [integral_const_mul, integral_indicator (measurableSet_symmetricInterval radius),
    integral_const, burnolIntervalConstant_norm_sq positive]
  simp only [star_inv₀]
  rw [← starRingEnd_apply, Complex.conj_ofReal]
  simp [symmetricInterval, positive.le, sub_neg_eq_add, real_smul]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  ring

theorem burnolGapTailFiniteWindow_integrable
    {lower upper : ℝ} (_positive : 0 < lower) (ordered : lower ≤ upper)
    (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (burnolGapTailFiniteWindowRaw lower upper coordinate) := by
  have exponent : -1 < (-star coordinate.value).re := by
    simp only [neg_re, Complex.star_def, Complex.conj_re]
    linarith [coordinate.belowOne]
  have interval : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-star coordinate.value))
      (Ioc lower upper) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ordered).mp
      (intervalIntegral.intervalIntegrable_cpow' exponent)
  exact ((burnolGapRieszRaw_integrable lower).const_mul _ |>.sub
    ((burnolGapRieszRaw_integrable upper).const_mul _)).add
      (interval.integrable_indicator measurableSet_Ioc)

theorem burnolGapTailFiniteWindow_integral_zero
    {lower upper : ℝ} (positive : 0 < lower) (ordered : lower ≤ upper)
    (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ, burnolGapTailFiniteWindowRaw lower upper coordinate x) = 0 := by
  have exponent : -1 < (-star coordinate.value).re := by
    simp only [neg_re, Complex.star_def, Complex.conj_re]
    linarith [coordinate.belowOne]
  have interval : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-star coordinate.value))
      (Ioc lower upper) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ordered).mp
      (intervalIntegral.intervalIntegrable_cpow' exponent)
  have lowerI := (burnolGapRieszRaw_integrable lower).const_mul
    (star (burnolRadiusMellinGapMoment lower coordinate.value))
  have upperI := (burnolGapRieszRaw_integrable upper).const_mul
    (star (burnolRadiusMellinGapMoment upper coordinate.value))
  have sumRead := MeasureTheory.integral_add (lowerI.sub upperI)
    (interval.integrable_indicator measurableSet_Ioc)
  simp only [Pi.sub_apply] at sumRead
  unfold burnolGapTailFiniteWindowRaw
  rw [sumRead,
    integral_sub lowerI upperI,
    integral_const_mul, integral_const_mul,
    burnolGapRieszRaw_integral positive, burnolGapRieszRaw_integral (positive.trans_le ordered),
    integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le ordered,
    integral_cpow (Or.inl exponent), mul_one, mul_one]
  unfold burnolRadiusMellinGapMoment
  simp only [Complex.star_def]
  rw [map_div₀, map_div₀]
  have conjugatePower (x : ℝ) (hx : 0 < x) :
      starRingEnd ℂ ((x : ℂ) ^ (1 - coordinate.value)) =
        (x : ℂ) ^ (1 - starRingEnd ℂ coordinate.value) := by
    have conjugated := Complex.conj_cpow (x : ℂ)
      (starRingEnd ℂ (1 - coordinate.value)) (by
        rw [Complex.arg_ofReal_of_nonneg hx.le]; exact ne_of_lt Real.pi_pos)
    simpa only [Complex.conj_conj, Complex.conj_ofReal, map_sub, map_one] using conjugated.symm
  rw [conjugatePower lower positive, conjugatePower upper (positive.trans_le ordered)]
  simp only [map_sub, map_one]
  rw [show -(starRingEnd ℂ) coordinate.value + 1 =
    1 - (starRingEnd ℂ) coordinate.value by ring]
  ring

theorem burnolGapTailFiniteWindow_actualZeroExtension
    {lower upper : ℝ} (positive : 0 < lower) (ordered : lower ≤ upper)
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRadiusZeroExtension upper
        (burnolRadiusRestriction upper
          (burnolRadiusAmbientCompletedMellinKernelFormula lower positive coordinate -
            burnolRadiusAmbientCompletedMellinKernelFormula upper
              (positive.trans_le ordered) coordinate)) =
      burnolRadiusAmbientCompletedMellinKernelFormula lower positive coordinate -
        burnolRadiusAmbientCompletedMellinKernelFormula upper
          (positive.trans_le ordered) coordinate := by
  let source := burnolRadiusAmbientCompletedMellinKernelFormula lower positive coordinate -
    burnolRadiusAmbientCompletedMellinKernelFormula upper (positive.trans_le ordered) coordinate
  have restrictRead := (ae_restrict_iff' (measurableSet_symmetricInterval upper)).mp
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval upper) source)
  apply Lp.ext
  filter_upwards [burnolRadiusZeroExtension_coe (burnolRadiusRestriction upper source),
    restrictRead, burnolGapTailFiniteWindow_ae_source positive ordered coordinate]
    with x extended restricted raw
  change burnolRadiusZeroExtension upper (burnolRadiusRestriction upper source) x = source x
  rw [extended]
  by_cases inside : x ∈ symmetricInterval upper
  · rw [Set.indicator_of_mem inside]
    exact restricted inside
  · rw [Set.indicator_of_notMem inside]
    rw [show source x = burnolGapTailFiniteWindowRaw lower upper coordinate x from raw,
      burnolGapTailFiniteWindowRaw_zero_outside positive ordered coordinate inside]

theorem burnolGapTailFiniteWindow_actualFourier_read
    {lower upper : ℝ} (positive : 0 < lower) (ordered : lower ≤ upper)
    (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2
        (burnolRadiusAmbientCompletedMellinKernelFormula lower positive coordinate -
          burnolRadiusAmbientCompletedMellinKernelFormula upper
            (positive.trans_le ordered) coordinate) : ℝ → ℂ) =ᵐ[volume]
      burnolRadiusTruncatedFourierRaw upper
        (burnolRadiusRestriction upper
          (burnolRadiusAmbientCompletedMellinKernelFormula lower positive coordinate -
            burnolRadiusAmbientCompletedMellinKernelFormula upper
              (positive.trans_le ordered) coordinate)) := by
  have actual := burnolRadiusFourierL2_zeroExtension_ae_eq_raw
    (burnolRadiusRestriction upper
      (burnolRadiusAmbientCompletedMellinKernelFormula lower positive coordinate -
        burnolRadiusAmbientCompletedMellinKernelFormula upper (positive.trans_le ordered) coordinate))
  rw [burnolGapTailFiniteWindow_actualZeroExtension positive ordered coordinate] at actual
  exact actual

theorem burnolGapTailFiniteWindow_actualFourier_zero
    {lower upper : ℝ} (positive : 0 < lower) (ordered : lower ≤ upper)
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRadiusTruncatedFourierRaw upper
        (burnolRadiusRestriction upper
          (burnolRadiusAmbientCompletedMellinKernelFormula lower positive coordinate -
            burnolRadiusAmbientCompletedMellinKernelFormula upper
              (positive.trans_le ordered) coordinate)) 0 = 0 := by
  let source := burnolRadiusAmbientCompletedMellinKernelFormula lower positive coordinate -
    burnolRadiusAmbientCompletedMellinKernelFormula upper (positive.trans_le ordered) coordinate
  have restricted : (burnolRadiusRestriction upper source : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval upper)]
      burnolGapTailFiniteWindowRaw lower upper coordinate :=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval upper) source).trans
      (ae_restrict_of_ae (burnolGapTailFiniteWindow_ae_source positive ordered coordinate))
  unfold burnolRadiusTruncatedFourierRaw VectorFourier.fourierIntegral
  simp only [map_zero, neg_zero, Real.fourierChar.map_zero_eq_one, one_smul]
  rw [integral_congr_ae restricted, ← integral_indicator (measurableSet_symmetricInterval upper)]
  have same : (symmetricInterval upper).indicator
      (burnolGapTailFiniteWindowRaw lower upper coordinate) =
      burnolGapTailFiniteWindowRaw lower upper coordinate := by
    funext x
    by_cases inside : x ∈ symmetricInterval upper
    · exact Set.indicator_of_mem inside _
    · rw [Set.indicator_of_notMem inside,
        burnolGapTailFiniteWindowRaw_zero_outside positive ordered coordinate inside]
  rw [same]
  exact burnolGapTailFiniteWindow_integral_zero positive ordered coordinate

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
