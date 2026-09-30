import H0mework.Versions.Y.Arithmetic.TruncatedFourier.DilationAction

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace
noncomputable section

def burnolFixedWindowDilationOverlap
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (shift : ℝ) : BurnolUnitIntervalL2 →L[ℂ] BurnolUnitIntervalL2 :=
  (burnolRadiusRechartEquiv hf).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((burnolRadiusRestriction frequency).comp
      ((burnolMultiplicativeDilation shift).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (burnolUnitWindowEmbedding hp)))

theorem burnolFixedWindowDilationOverlap_coe
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (shift : ℝ) (state : BurnolUnitIntervalL2) :
    (burnolFixedWindowDilationOverlap hp hf shift state : ℝ → ℂ) =ᵐ[
        volume.restrict (symmetricInterval 1)]
      fun x : ℝ => (Real.sqrt frequency : ℂ) *
        (symmetricInterval (position * Real.exp (-shift))).indicator
          (fun y : ℝ => (Real.sqrt (position * Real.exp (-shift)) : ℂ)⁻¹ *
            state ((position * Real.exp (-shift))⁻¹ * y)) (frequency * x) := by
  let moved := burnolUnitWindowEmbedding
    (mul_pos hp (Real.exp_pos (-shift))) state
  have restricted : (burnolRadiusRestriction frequency moved : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval frequency)]
      (symmetricInterval (position * Real.exp (-shift))).indicator
        (fun y : ℝ => (Real.sqrt (position * Real.exp (-shift)) : ℂ)⁻¹ *
          state ((position * Real.exp (-shift))⁻¹ * y)) :=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval frequency) moved).trans
      (ae_restrict_of_ae (burnolUnitWindowEmbedding_coe
        (mul_pos hp (Real.exp_pos (-shift))) state))
  have scaled :=
    (burnolRadiusScaleEquiv_measurePreserving hf).quasiMeasurePreserving.ae_eq
      (Measure.ae_smul_measure restricted (ENNReal.ofReal frequency⁻¹))
  have sourceEq : burnolFixedWindowDilationOverlap hp hf shift state =
      burnolRadiusRechart hf (burnolRadiusRestriction frequency moved) := by
    change (burnolRadiusRechartEquiv hf)
        (burnolRadiusRestriction frequency
          (burnolMultiplicativeDilation shift (burnolUnitWindowEmbedding hp state))) = _
    rw [burnolUnitWindowEmbedding_dilation]
    rfl
  rw [sourceEq]
  filter_upwards [burnolRadiusRechart_coe hf
    (burnolRadiusRestriction frequency moved), scaled] with x chart raw
  rw [chart]
  exact congrArg ((Real.sqrt frequency : ℂ) * ·)
    (by simpa only [burnolRadiusScaleMeasurableEquiv_apply, Function.comp_apply] using raw)

theorem burnolRadiusZeroExtension_reflect
    (radius : ℝ) (state : BurnolRadiusIntervalL2 radius) :
    reflectL2 (burnolRadiusZeroExtension radius state) =
      burnolRadiusZeroExtension radius (reflectRestricted radius state) := by
  have source := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (burnolRadiusZeroExtension_coe state)
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp
    (Lp.coeFn_compMeasurePreserving state (negMeasurePreserving_restrict radius))
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (burnolRadiusZeroExtension radius state)
    negMeasurePreserving, source,
    burnolRadiusZeroExtension_coe (reflectRestricted radius state), localRead]
      with x reflected old new reflectedLocal
  change reflectL2 (burnolRadiusZeroExtension radius state) x =
    burnolRadiusZeroExtension radius state (-x) at reflected
  rw [reflected, old, new]
  have negMembership : -x ∈ symmetricInterval radius ↔ x ∈ symmetricInterval radius := by
    simp only [symmetricInterval, Set.mem_Icc]
    constructor <;> intro pair <;> constructor <;> linarith [pair.1, pair.2]
  by_cases inside : x ∈ symmetricInterval radius
  · simp only [Set.indicator_of_mem inside,
      Set.indicator_of_mem (negMembership.mpr inside)]
    exact (reflectedLocal inside).symm
  · simp only [Set.indicator_of_notMem inside,
      Set.indicator_of_notMem (fun h => inside (negMembership.mp h))]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
