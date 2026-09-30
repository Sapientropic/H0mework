import H0mework.Versions.Y.Arithmetic.RieszCanonicalRaw.RieszCanonicalRaw
import H0mework.Versions.Y.Arithmetic.TruncatedFourier.DilationAction
import H0mework.Arithmetic.BurnolMellin.PairedMellinCharacter

/-! Actual normalized dilation of the same gap-plus-tail Mellin kernel. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace
noncomputable section

theorem burnolIntervalConstant_norm_sq {radius : ℝ} (positive : 0 < radius) :
    (‖intervalConstant radius‖ ^ 2 : ℂ) = (2 * radius : ℝ) := by
  have self := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (intervalConstant radius)
  change ⟪intervalConstant radius, intervalConstant radius⟫_ℂ =
    (‖intervalConstant radius‖ : ℂ) ^ 2 at self
  rw [← self, L2.inner_def]
  have actual : (fun x : ℝ => ⟪intervalConstant radius x, intervalConstant radius x⟫_ℂ) =ᵐ[
      volume.restrict (symmetricInterval radius)] fun _ => (1 : ℂ) := by
    filter_upwards [intervalConstant_coeFn radius] with x read
    rw [read]
    simp
  rw [integral_congr_ae actual, integral_const]
  simp [symmetricInterval, positive.le, sub_neg_eq_add, real_smul]
  ring

private theorem cpow_exp_real (shift : ℝ) (power : ℂ) :
    (Real.exp shift : ℂ) ^ power = Complex.exp ((shift : ℂ) * power) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero shift))]
  rw [← Complex.ofReal_log (Real.exp_pos shift).le, Real.log_exp]

private theorem realExp_cpow_halfDensity {x : ℝ} (positive : 0 < x)
    (coordinate : ℂ) (shift : ℝ) :
    (Real.exp (shift / 2) : ℂ) * ((Real.exp shift * x : ℝ) : ℂ) ^ (-star coordinate) =
      fullMellinTranslationCharacter (star coordinate) shift *
        (x : ℂ) ^ (-star coordinate) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos shift).le positive.le,
    cpow_exp_real, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  unfold fullMellinTranslationCharacter
  congr 2
  push_cast
  ring

theorem burnolRadiusMellinTail_dilation
    {radius : ℝ} (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    burnolMultiplicativeDilation shift
        (burnolRadiusMellinTailKernelL2 radius positive coordinate.value coordinate.rightHalf) =
      fullMellinTranslationCharacter (star coordinate.value) shift •
        burnolRadiusMellinTailKernelL2
          (radius * Real.exp (-shift)) (mul_pos positive (Real.exp_pos (-shift)))
          coordinate.value coordinate.rightHalf := by
  have scale : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  have movedPositive := mul_pos positive (Real.exp_pos (-shift))
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn shift
      (burnolRadiusMellinTailKernelL2 radius positive coordinate.value coordinate.rightHalf),
    scale.ae (MemLp.coeFn_toLp
      (burnolRadiusMellinTailKernelRaw_memLp positive coordinate.value coordinate.rightHalf)),
    MemLp.coeFn_toLp (burnolRadiusMellinTailKernelRaw_memLp
      movedPositive coordinate.value coordinate.rightHalf),
    Lp.coeFn_smul (fullMellinTranslationCharacter (star coordinate.value) shift)
      (burnolRadiusMellinTailKernelL2 _ movedPositive coordinate.value coordinate.rightHalf)]
      with x dilation rawSource rawTarget scalar
  rw [dilation, scalar]
  change (Real.exp (shift / 2) : ℂ) * _ = _ * _
  change burnolRadiusMellinTailKernelL2 radius positive coordinate.value coordinate.rightHalf
    (Real.exp shift * x) = _ at rawSource
  change burnolRadiusMellinTailKernelL2 _ movedPositive coordinate.value coordinate.rightHalf x =
    _ at rawTarget
  rw [rawSource, rawTarget]
  unfold burnolRadiusMellinTailKernelRaw
  have landing : Real.exp shift * x ∈ Ioi radius ↔
      x ∈ Ioi (radius * Real.exp (-shift)) := by
    simp only [Set.mem_Ioi, Real.exp_neg]
    simpa only [div_eq_mul_inv, mul_comm] using
      (div_lt_iff₀ (Real.exp_pos shift) : radius / Real.exp shift < x ↔
        radius < x * Real.exp shift).symm
  by_cases inside : x ∈ Ioi (radius * Real.exp (-shift))
  · rw [if_pos inside, if_pos (landing.mpr inside)]
    exact realExp_cpow_halfDensity (movedPositive.trans inside) coordinate.value shift
  · rw [if_neg inside, if_neg (fun h => inside (landing.mp h)), mul_zero, mul_zero]

theorem burnolAmbientGapRiesz_dilation {radius : ℝ} (positive : 0 < radius)
    (shift : ℝ) :
    burnolMultiplicativeDilation shift (burnolAmbientGapRieszVector radius) =
      (Real.exp (-shift / 2) : ℂ) •
        burnolAmbientGapRieszVector (radius * Real.exp (-shift)) := by
  have scale : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  have movedPositive := mul_pos positive (Real.exp_pos (-shift))
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn shift (burnolAmbientGapRieszVector radius),
    scale.ae (burnolGapRiesz_ae_raw radius),
    burnolGapRiesz_ae_raw (radius * Real.exp (-shift)),
    Lp.coeFn_smul (Real.exp (-shift / 2) : ℂ)
      (burnolAmbientGapRieszVector (radius * Real.exp (-shift)))]
      with x dilation rawSource rawTarget scalar
  rw [dilation, scalar]
  change (Real.exp (shift / 2) : ℂ) * _ = (Real.exp (-shift / 2) : ℂ) * _
  rw [rawSource, rawTarget]
  unfold burnolGapRieszRaw
  rw [burnolIntervalConstant_norm_sq positive, burnolIntervalConstant_norm_sq movedPositive]
  have landing : Real.exp shift * x ∈ symmetricInterval radius ↔
      x ∈ symmetricInterval (radius * Real.exp (-shift)) := by
    simp only [symmetricInterval, Set.mem_Icc, ← abs_le, abs_mul,
      abs_of_pos (Real.exp_pos shift)]
    simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm] using
      (le_div_iff₀ (Real.exp_pos shift) : |x| ≤ radius / Real.exp shift ↔
        |x| * Real.exp shift ≤ radius).symm
  by_cases inside : x ∈ symmetricInterval (radius * Real.exp (-shift))
  · rw [Set.indicator_of_mem inside, Set.indicator_of_mem (landing.mpr inside)]
    simp only [mul_one, star_inv₀]
    rw [← starRingEnd_apply, ← starRingEnd_apply, Complex.conj_ofReal, Complex.conj_ofReal]
    have half : Real.exp (-shift / 2) * Real.exp shift = Real.exp (shift / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have realNumeric : Real.exp (shift / 2) * (2 * radius)⁻¹ =
        Real.exp (-shift / 2) * (2 * (radius * Real.exp (-shift)))⁻¹ := by
      rw [Real.exp_neg]
      field_simp
      simpa only [neg_div] using half.symm
    exact_mod_cast realNumeric
  · rw [Set.indicator_of_notMem inside,
      Set.indicator_of_notMem (fun h => inside (landing.mp h))]
    simp only [mul_zero]

theorem burnolMellinGapMoment_scaled {radius : ℝ} (positive : 0 < radius)
    (coordinate : ℂ) (shift : ℝ) :
    burnolRadiusMellinGapMoment (radius * Real.exp (-shift)) coordinate =
      Complex.exp ((-shift : ℂ) * (1 - coordinate)) *
        burnolRadiusMellinGapMoment radius coordinate := by
  unfold burnolRadiusMellinGapMoment
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg positive.le (Real.exp_pos (-shift)).le,
    cpow_exp_real]
  push_cast
  ring

theorem burnolRadiusAmbientKernel_dilation
    {radius : ℝ} (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    burnolMultiplicativeDilation shift
        (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) =
      fullMellinTranslationCharacter (star coordinate.value) shift •
        burnolRadiusAmbientCompletedMellinKernelFormula
          (radius * Real.exp (-shift)) (mul_pos positive (Real.exp_pos (-shift))) coordinate := by
  unfold burnolRadiusAmbientCompletedMellinKernelFormula
  rw [map_add, map_smul, smul_add]
  apply congrArg₂ (· + ·)
  · rw [burnolAmbientGapRiesz_dilation positive, smul_smul, smul_smul,
      burnolMellinGapMoment_scaled positive]
    congr 1
    change star (burnolRadiusMellinGapMoment radius coordinate.value) *
      (Real.exp (-shift / 2) : ℂ) =
      fullMellinTranslationCharacter (star coordinate.value) shift *
        star (Complex.exp ((-shift : ℂ) * (1 - coordinate.value)) *
          burnolRadiusMellinGapMoment radius coordinate.value)
    have conjugateExp : star (Complex.exp ((-shift : ℂ) * (1 - coordinate.value))) =
        Complex.exp ((-shift : ℂ) * (1 - star coordinate.value)) := by
      rw [← starRingEnd_apply, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_sub, map_neg, map_one, Complex.conj_ofReal]
      rfl
    rw [star_mul, conjugateExp]
    unfold fullMellinTranslationCharacter
    rw [mul_left_comm, ← Complex.exp_add, Complex.ofReal_exp]
    have exponent : ((1 / 2 : ℂ) - star coordinate.value) * shift +
        (-shift : ℂ) * (1 - star coordinate.value) = (-shift / 2 : ℝ) := by
      push_cast
      ring
    rw [exponent]
  · exact burnolRadiusMellinTail_dilation positive coordinate shift

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
