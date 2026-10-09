import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Algebra
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Approximation
import H0mework.Versions.V2.Arithmetic.RiemannUnitFourier.ActionCurrent

/-! The original counted-band resolvent is the same unit-source action plus its actual Pa current. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolPaBandResolvent_action (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) :
    (coordinate.value / 2) • burnolDirectRightResolvent (coordinate.value / 2)
      (fourierL2 (burnolReciprocalStepNativeWave 1 upper)) =
      (Real.sqrt upper : ℂ) • burnolMultiplicativeDilation (-Real.log upper)
        (burnolUnitTailResponse coordinate 1) - burnolUnitTailResponse coordinate 1 -
          fourierL2 (burnolReciprocalStepNativeWave 1 upper) := by
  have right : 1 / 4 < (coordinate.value / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  have atOne : burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 1 =
      burnolUnitCountingPrimitiveL2 := by
    simp only [burnolSourceScalePrimitive, Real.sqrt_one, Real.log_one,
      burnolMultiplicativeDilation_zero, one_smul]
  have scaleRead :
      fourierL2 (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 upper) =
        (Real.sqrt upper : ℂ) • burnolMultiplicativeDilation (-Real.log upper)
          (fourierL2 burnolUnitCountingPrimitiveL2) := by
    simp only [burnolSourceScalePrimitive, RCLike.real_smul_eq_coe_smul (K := ℂ),
      map_smul, fourierL2_burnolMultiplicativeDilation]
    rfl
  rw [burnolReciprocalStepNativeWave, atOne, map_sub, scaleRead,
    burnolDirectRightResolvent_sub _ right, burnolDirectRightResolvent_smul,
    burnolDirectRightResolvent_dilation, burnolUnitTailResponse_fourierResolvent]
  simp only [map_add, map_smul]
  module

theorem burnolPaBandResponse_character (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) (positive : 0 < upper) :
    (Real.sqrt upper : ℂ) * fullMellinTranslationCharacter coordinate.value (-Real.log upper) =
      Complex.exp (coordinate.value * (Real.log upper : ℂ)) := by
  have root : Real.sqrt upper = Real.exp (Real.log upper / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos positive]
    congr 1
    ring
  rw [root, Complex.ofReal_exp]
  unfold fullMellinTranslationCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem burnolPaBandResolvent_classResidual (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) (ordered : 1 ≤ upper) (bounded : upper < 4) :
    (coordinate.value / 2) • burnolDirectRightResolvent (coordinate.value / 2)
      (fourierL2 (burnolReciprocalStepNativeWave 1 upper)) -
      (Complex.exp (coordinate.value * (Real.log upper : ℂ)) - 1) •
        burnolUnitTailResponse coordinate 1 ∈ burnolOriginalPaInL2 := by
  have positive : 0 < upper := lt_of_lt_of_le (by norm_num) ordered
  have lower : (1 / 4 : ℝ) < Real.exp (-(-Real.log upper)) := by
    rw [neg_neg, Real.exp_log positive]
    linarith
  have upperBound : Real.exp (-(-Real.log upper)) < 4 := by
    rw [neg_neg, Real.exp_log positive]
    exact bounded
  have current := burnolUnitOne_actualCurrent_memPa coordinate (-Real.log upper) lower upperBound
  let band := burnolReciprocalStepPhysicalState 1 upper (by norm_num) ordered bounded.le
  have bandMem : band ∈ burnolCompactCoPoissonClosedRange :=
    burnolReciprocalStepWave_memPa 1 upper (by norm_num) ordered bounded
  have fourierBand : fourierL2 (burnolReciprocalStepNativeWave 1 upper) ∈
      burnolOriginalPaInL2 := by
    refine Submodule.mem_map.mpr ⟨evenFaceFourierEquiv burnolUnscaledCommonGapRadius band,
      burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange bandMem, ?_⟩
    rw [burnolReciprocalStepNativeWave_eq 1 upper (by norm_num) ordered]
    rfl
  have generated := burnolOriginalPaInL2.sub_mem
    (burnolOriginalPaInL2.smul_mem (Real.sqrt upper : ℂ) current) fourierBand
  rw [burnolPaBandResolvent_action]
  convert generated using 1
  rw [← burnolPaBandResponse_character coordinate upper positive]
  module
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
