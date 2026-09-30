import H0mework.Versions.Y.Arithmetic.RiemannBandResponse.PhysicalBand

/-! The actual counted-band source follows the original dilation with one uniform interior margin. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolSourceScalePrimitive_dilation (value : BurnolL2) (scale shift : ℝ) (positive : 0 < scale) :
    burnolMultiplicativeDilation shift (burnolSourceScalePrimitive value scale) =
      (Real.exp (-shift / 2) : ℂ) •
        burnolSourceScalePrimitive value (scale * Real.exp shift) := by
  have rootExp : Real.sqrt (Real.exp shift) = Real.exp (shift / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have scalar : Real.exp (-shift / 2) * Real.sqrt (scale * Real.exp shift) = Real.sqrt scale := by
    rw [Real.sqrt_mul positive.le, rootExp]
    calc
      _ = Real.sqrt scale * (Real.exp (-shift / 2) * Real.exp (shift / 2)) := by ring
      _ = _ := by rw [← Real.exp_add, show -shift / 2 + shift / 2 = 0 by ring, Real.exp_zero, mul_one]
  unfold burnolSourceScalePrimitive
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
    burnolMultiplicativeDilation_add, smul_smul,
    Real.log_mul positive.ne' (Real.exp_ne_zero _), Real.log_exp]
  change (Real.sqrt scale : ℂ) • burnolMultiplicativeDilation (shift + Real.log scale) value =
    ((Real.exp (-shift / 2) : ℂ) * (Real.sqrt (scale * Real.exp shift) : ℂ)) •
      burnolMultiplicativeDilation (Real.log scale + shift) value
  rw [← Complex.ofReal_mul, scalar, add_comm]

theorem burnolReciprocalStepNativeWave_dilation (lower upper shift : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) :
    burnolMultiplicativeDilation shift (burnolReciprocalStepNativeWave lower upper) =
      (Real.exp (-shift / 2) : ℂ) •
        burnolReciprocalStepNativeWave (lower * Real.exp shift) (upper * Real.exp shift) := by
  unfold burnolReciprocalStepNativeWave
  rw [map_sub, burnolSourceScalePrimitive_dilation _ lower shift lowerPositive,
    burnolSourceScalePrimitive_dilation _ upper shift upperPositive, smul_sub]

theorem burnolPaResponseShift_bounds (shift : ℝ) (small : |shift| ≤ Real.log 2) :
    (1 / 2 : ℝ) ≤ Real.exp shift ∧ Real.exp shift ≤ 2 := by
  obtain ⟨lower, upper⟩ := abs_le.mp small
  constructor
  · have := Real.exp_le_exp.mpr lower
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using this
  · have := Real.exp_le_exp.mpr upper
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using this

theorem burnolPaInteriorBand_dilation_mem (upper shift : ℝ) (ordered : 1 ≤ upper)
    (bounded : upper ≤ 3 / 2) (small : |shift| ≤ Real.log 2) :
    burnolMultiplicativeDilation shift (burnolReciprocalStepNativeWave 1 upper) ∈
      burnolOriginalPaInL2 := by
  have positive : 0 < upper := lt_of_lt_of_le (by norm_num) ordered
  have bounds := burnolPaResponseShift_bounds shift small
  have lower : (1 / 4 : ℝ) < Real.exp shift := by linarith
  have high : upper * Real.exp shift < 4 := by
    nlinarith [Real.exp_pos shift]
  have order : Real.exp shift ≤ upper * Real.exp shift := by
    nlinarith [Real.exp_pos shift]
  rw [burnolReciprocalStepNativeWave_dilation 1 upper shift (by norm_num) positive, one_mul]
  apply burnolOriginalPaInL2.smul_mem
  refine Submodule.mem_map.mpr ⟨burnolReciprocalStepPhysicalState
    (Real.exp shift) (upper * Real.exp shift) lower order high.le,
      burnolReciprocalStepWave_memPa _ _ lower order high, ?_⟩
  rw [burnolReciprocalStepNativeWave_eq _ _ (Real.exp_pos _) order]
  rfl
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
