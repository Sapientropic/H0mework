import H0mework.Versions.Y.Arithmetic.MellinProjection.SchwartzIBP

/-! The actual gap/tail distribution generates both endpoint masses and its tail derivative. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

theorem burnolMellinTail_tempered_apply
    (radius : ℝ) (positive : 0 < radius) (exponent : ℂ)
    (rightHalf : 1 / 2 < exponent.re) (test : SchwartzMap ℝ ℂ) :
    (burnolRadiusMellinTailKernelL2 radius positive exponent rightHalf :
        TemperedDistribution ℝ ℂ) test =
      ∫ x : ℝ in Ioi radius, (x : ℂ) ^ (-star exponent) * test x := by
  rw [Lp.toTemperedDistribution_apply, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp
    (burnolRadiusMellinTailKernelRaw_memLp positive exponent rightHalf)] with x raw
  change burnolRadiusMellinTailKernelL2 radius positive exponent rightHalf x = _ at raw
  rw [raw]
  by_cases inside : x ∈ Ioi radius
  · simp only [burnolRadiusMellinTailKernelRaw, if_pos inside,
      Set.indicator_of_mem inside, smul_eq_mul, mul_comm]
  · simp only [burnolRadiusMellinTailKernelRaw, if_neg inside,
      Set.indicator_of_notMem inside, smul_zero]

private theorem nextHalf (coordinate : BurnolCompletedMellinCoordinate) :
    1 / 2 < (coordinate.value + 1).re := by
  simp only [Complex.add_re, Complex.one_re]
  linarith [coordinate.rightHalf]

theorem burnolMellinTail_distribution_derivative
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    TemperedDistribution.derivCLM ℂ
        (burnolRadiusMellinTailKernelL2 radius positive coordinate.value coordinate.rightHalf :
          TemperedDistribution ℝ ℂ) =
      (radius : ℂ) ^ (-star coordinate.value) • TemperedDistribution.delta radius -
        star coordinate.value •
          (burnolRadiusMellinTailKernelL2 radius positive (coordinate.value + 1)
            (nextHalf coordinate) : TemperedDistribution ℝ ℂ) := by
  ext test
  rw [TemperedDistribution.derivCLM_apply_apply,
    burnolMellinTail_tempered_apply]
  simp only [sub_apply, smul_apply, TemperedDistribution.delta_apply,
    neg_apply, SchwartzMap.derivCLM_apply, smul_eq_mul]
  rw [burnolMellinTail_tempered_apply]
  simp only [mul_neg, integral_neg, star_add, star_one]
  rw [burnolMellinTail_schwartz_IBP positive coordinate test]
  ring

theorem burnolGapRiesz_tempered_apply
    (radius : ℝ) (positive : 0 < radius) (test : SchwartzMap ℝ ℂ) :
    (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ) test =
      (2 * radius : ℝ)⁻¹ • ∫ x : ℝ in (-radius)..radius, test x := by
  rw [Lp.toTemperedDistribution_apply,
    show (∫ x : ℝ, test x • burnolAmbientGapRieszVector radius x) =
      ∫ x : ℝ, test x • burnolGapRieszRaw radius x by
        apply integral_congr_ae
        filter_upwards [burnolGapRiesz_ae_raw radius] with x raw
        rw [raw]]
  unfold burnolGapRieszRaw
  rw [burnolIntervalConstant_norm_sq positive]
  have numeric : star ((2 * radius : ℝ) : ℂ)⁻¹ = ((2 * radius : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, ← starRingEnd_apply, Complex.conj_ofReal]
  rw [numeric]
  simp only [smul_eq_mul]
  have pointwise : (fun x : ℝ => test x * (((2 * radius : ℝ) : ℂ)⁻¹ *
      (symmetricInterval radius).indicator (fun _ : ℝ => (1 : ℂ)) x)) =
      fun x : ℝ => (((2 * radius : ℝ) : ℂ)⁻¹) *
        (symmetricInterval radius).indicator test x := by
    funext x
    by_cases inside : x ∈ symmetricInterval radius
    · simp [inside, mul_comm]
    · simp [inside]
  rw [pointwise, integral_const_mul, integral_indicator (measurableSet_symmetricInterval radius)]
  rw [intervalIntegral.integral_of_le (by linarith : -radius ≤ radius)]
  rw [← integral_Icc_eq_integral_Ioc]
  simp only [symmetricInterval, Complex.real_smul, Complex.ofReal_inv]

theorem burnolGapRiesz_distribution_derivative
    (radius : ℝ) (positive : 0 < radius) :
    TemperedDistribution.derivCLM ℂ
        (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ) =
      (((2 * radius : ℝ) : ℂ)⁻¹) •
        (TemperedDistribution.delta (-radius) - TemperedDistribution.delta radius) := by
  ext test
  rw [TemperedDistribution.derivCLM_apply_apply, burnolGapRiesz_tempered_apply radius positive]
  simp only [smul_apply, sub_apply, TemperedDistribution.delta_apply,
    neg_apply, SchwartzMap.derivCLM_apply, smul_eq_mul]
  rw [intervalIntegral.integral_neg]
  have source := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => test.hasDerivAt x)
    ((SchwartzMap.derivCLM ℂ ℂ test).continuous.intervalIntegrable (-radius) radius)
  rw [source]
  simp only [Complex.real_smul, Complex.ofReal_inv]
  ring

theorem burnolGapTail_distribution_derivative
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    TemperedDistribution.derivCLM ℂ
        (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate :
          TemperedDistribution ℝ ℂ) =
      (star (burnolRadiusMellinGapMoment radius coordinate.value) *
          (((2 * radius : ℝ) : ℂ)⁻¹)) • TemperedDistribution.delta (-radius) +
        ((radius : ℂ) ^ (-star coordinate.value) -
          star (burnolRadiusMellinGapMoment radius coordinate.value) *
            (((2 * radius : ℝ) : ℂ)⁻¹)) • TemperedDistribution.delta radius -
        star coordinate.value •
          (burnolRadiusMellinTailKernelL2 radius positive (coordinate.value + 1)
            (nextHalf coordinate) : TemperedDistribution ℝ ℂ) := by
  have source :
      (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate :
        TemperedDistribution ℝ ℂ) =
      star (burnolRadiusMellinGapMoment radius coordinate.value) •
          (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ) +
        (burnolRadiusMellinTailKernelL2 radius positive coordinate.value coordinate.rightHalf :
          TemperedDistribution ℝ ℂ) := by
    change Lp.toTemperedDistributionCLM ℂ volume 2
      (star (burnolRadiusMellinGapMoment radius coordinate.value) •
          burnolAmbientGapRieszVector radius +
        burnolRadiusMellinTailKernelL2 radius positive coordinate.value coordinate.rightHalf) = _
    rw [map_add, map_smul]
    rfl
  rw [source, map_add, map_smul,
    burnolGapRiesz_distribution_derivative radius positive,
    burnolMellinTail_distribution_derivative radius positive coordinate]
  module

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
