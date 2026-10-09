import H0mework.Versions.V2.Arithmetic.RieszSourceKernel.Generated

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace
open OriginalRieszSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "m" => GapEuler.gapMean q

def gapState (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)

theorem gapState_read (coordinate : BurnolCompletedMellinCoordinate) :
    (gapState coordinate : ℝ → ℂ) =ᵐ[volume]
      burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) :=
  burnolEvenRaw_ae _ _ (burnolAmbientMellinKernel_ae_raw coordinate)

private theorem ambient_raw_gap (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : x ∈ symmetricInterval q) : burnolAmbientMellinKernelRaw coordinate x = m coordinate := by
  have tail : ¬ q < x := not_lt.mpr inside.2
  simp only [burnolAmbientMellinKernelRaw, burnolGapRieszRaw, indicator_of_mem inside,
    mul_one, burnolRadiusMellinTailKernelRaw, mem_Ioi, if_neg tail, add_zero]
  rw [burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)]
  simp [GapEuler.gapMean]

theorem gapState_raw_gap (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : x ∈ symmetricInterval q) :
    burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) x = m coordinate := by
  have negative : -x ∈ symmetricInterval q := ⟨by linarith [inside.2], by linarith [inside.1]⟩
  rw [burnolEvenRaw, ambient_raw_gap coordinate inside, ambient_raw_gap coordinate negative]
  ring

theorem gapState_raw_tail (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (outside : q < x) :
    burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) x =
      (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) := by
  have positiveOutside : x ∉ symmetricInterval q := fun member => not_lt_of_ge member.2 outside
  have negativeOutside : -x ∉ symmetricInterval q := by
    intro member
    linarith [member.1]
  have negativeTail : ¬ q < -x := by linarith
  simp only [burnolEvenRaw, burnolAmbientMellinKernelRaw, burnolGapRieszRaw,
    indicator_of_notMem positiveOutside, indicator_of_notMem negativeOutside, mul_zero,
    burnolRadiusMellinTailKernelRaw, mem_Ioi, if_pos outside, if_neg negativeTail, zero_add, add_zero]

theorem gapState_restriction (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (gapState coordinate) = m coordinate • intervalConstant q := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (gapState coordinate),
    ae_restrict_of_ae (s := symmetricInterval q) (gapState_read coordinate),
    ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_smul (m coordinate) (intervalConstant q), intervalConstant_coeFn q]
      with x restricted raw inside scaled constant
  change burnolQuarterRestriction (gapState coordinate) x = _ at restricted
  rw [restricted, raw, gapState_raw_gap coordinate inside, scaled]
  change m coordinate = m coordinate * intervalConstant q x
  rw [constant, mul_one]

theorem gapState_gapCoefficient (coordinate : BurnolCompletedMellinCoordinate) :
    burnolAmbientGapCoefficient q (gapState coordinate) = m coordinate := by
  have self : inner ℂ (intervalConstant q) (intervalConstant q) = ((2 * q : ℝ) : ℂ) :=
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (intervalConstant q)).trans
      (burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q))
  change ((‖intervalConstant q‖ ^ 2 : ℂ)⁻¹) *
    inner ℂ (intervalConstant q) (burnolQuarterRestriction (gapState coordinate)) = _
  rw [gapState_restriction, inner_smul_right, self,
    burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)]
  norm_num
  ring

theorem evenPart_inner_gapState (value : BurnolL2) (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ (burnolAmbientEvenPart value) (gapState coordinate) = inner ℂ value (gapState coordinate) := by
  have even : reflectL2 (gapState coordinate) = gapState coordinate := burnolAmbientEvenPart_even _
  have reflected : inner ℂ (reflectL2 value) (gapState coordinate) = inner ℂ value (gapState coordinate) := by
    conv_lhs => rw [← even]
    exact reflectL2.inner_map_map _ _
  change inner ℂ ((1 / 2 : ℂ) • (value + reflectL2 value)) (gapState coordinate) = _
  rw [inner_smul_left, inner_add_left, reflected]
  norm_num [map_ofNat]
  ring

theorem gapState_tail_pair (left right : BurnolCompletedMellinCoordinate) :
    burnolRadiusMellinTailEvaluator q (by norm_num) left.value left.rightHalf (gapState right) =
      (1 / 2 : ℂ) *
        (q : ℂ) ^ (-(left.value + star right.value - 1)) / (left.value + star right.value - 1) := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  have read : (∫ x : ℝ in Ioi q, (x : ℂ) ^ (-left.value) * gapState right x) =
      (1 / 2 : ℂ) * ∫ x : ℝ in Ioi q, (x : ℂ) ^ (-left.value - star right.value) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (s := Ioi q) (gapState_read right),
      ae_restrict_mem measurableSet_Ioi] with x raw outside
    rw [raw, gapState_raw_tail right outside]
    have nonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < q) outside))
    rw [show -left.value - star right.value = -left.value + -star right.value by ring,
      Complex.cpow_add _ _ nonzero]
    ring
  rw [read, integral_Ioi_cpow_of_lt (by
    simp only [sub_re, neg_re, Complex.star_def, Complex.conj_re]
    linarith [left.rightHalf, right.rightHalf]) (by norm_num)]
  have exponent : -left.value - star right.value + 1 = -(left.value + star right.value - 1) := by ring
  rw [exponent]
  rw [neg_div_neg_eq]
  ring

theorem gapState_inner (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (gapState left) (gapState right) =
      (1 / 2 : ℂ) * star (m left) * m right +
      (1 / 2 : ℂ) * (q : ℂ) ^ (-(left.value + star right.value - 1)) /
        (left.value + star right.value - 1) := by
  have mean : burnolRadiusMellinGapMoment q left.value = (1 / 2 : ℂ) * star (m left) := by
    simp [GapEuler.gapMean]
    ring
  change inner ℂ (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula left)) _ = _
  rw [evenPart_inner_gapState, ← burnolAmbientCompletedMellinRieszVector_eq_kernelFormula,
    burnolAmbientCompletedMellinRieszVector_readback]
  change burnolRadiusMellinGapMoment q left.value * burnolAmbientGapCoefficient q (gapState right) +
    burnolRadiusMellinTailEvaluator q (by norm_num) left.value left.rightHalf (gapState right) = _
  rw [gapState_gapCoefficient, gapState_tail_pair, mean]

theorem source_cross_parameter_ne_zero (left right : BurnolCompletedMellinCoordinate) :
    left.value + star right.value - 1 ≠ 0 := by
  intro zero
  have realPart := congrArg Complex.re zero
  simp only [sub_re, Complex.add_re, Complex.star_def, Complex.conj_re, Complex.one_re,
    Complex.zero_re] at realPart
  linarith [left.rightHalf, right.rightHalf]

private theorem quarter_star_cpow (power : ℂ) :
    star ((q : ℂ) ^ power) = (q : ℂ) ^ star power := by
  have argument : (q : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ q)]
    exact Real.pi_ne_zero.symm
  simpa only [Complex.star_def, Complex.conj_ofReal] using
    (Complex.cpow_conj (q : ℂ) power argument).symm

theorem gapState_gram (left right : BurnolCompletedMellinCoordinate) :
    (left.value + star right.value - 1) * inner ℂ (gapState left) (gapState right) =
      (1 / 2 : ℂ) * star (star left.value * m left) * (star right.value * m right) := by
  have leftPrimitive := congrArg star (GapEuler.gapMean_primitive q (by norm_num) left)
  have half : star (1 / 2 : ℂ) = 1 / 2 := by norm_num
  simp only [star_mul, star_sub, star_one, star_star, half, quarter_star_cpow,
    star_neg] at leftPrimitive
  have rightPrimitive := GapEuler.gapMean_primitive q (by norm_num) right
  have leftPower : (q : ℂ) ^ (-left.value) = 2 * ((1 - left.value) * star (m left)) := by
    linear_combination -2 * leftPrimitive
  have rightPower : (q : ℂ) ^ (-star right.value) = 2 * ((1 - star right.value) * m right) := by
    linear_combination -2 * rightPrimitive
  have power : (q : ℂ) ^ (-(left.value + star right.value - 1)) =
      (1 - left.value) * (1 - star right.value) * star (m left) * m right := by
    have quarterNe : (q : ℂ) ≠ 0 := by norm_num
    rw [show -(left.value + star right.value - 1) = 1 + -left.value + -star right.value by ring,
      Complex.cpow_add _ _ quarterNe, Complex.cpow_add _ _ quarterNe,
      Complex.cpow_one, leftPower, rightPower]
    push_cast
    ring
  have canceled (value : ℂ) :
      (left.value + star right.value - 1) * (value / (left.value + star right.value - 1)) = value := by
    rw [div_eq_mul_inv]
    calc
      _ = value * ((left.value + star right.value - 1) * (left.value + star right.value - 1)⁻¹) := by ring
      _ = value := by rw [mul_inv_cancel₀ (source_cross_parameter_ne_zero left right), mul_one]
  rw [gapState_inner, power, mul_add, canceled]
  simp only [star_mul, star_star]
  ring

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
