import H0mework.Versions.Y.Arithmetic.RiemannBandResponse.ActionBand
import H0mework.Versions.Y.Arithmetic.RiemannBandResponse.Class

/-! The explicit source correction between each finite response and the unit state has actual Pa-preserving motion. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolPaBandResponseCorrection (coordinate : BurnolCompletedMellinCoordinate) (upper : ℝ) : BurnolL2 :=
  (coordinate.value / 2) • burnolDirectRightResolvent (coordinate.value / 2)
    (fourierL2 (burnolReciprocalStepNativeWave 1 upper)) -
      (Complex.exp (coordinate.value * (Real.log upper : ℂ)) - 1) •
        burnolUnitTailResponse coordinate 1

theorem burnolPaBandResponseCorrection_source (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) (positive : 0 < upper) :
    burnolPaBandResponseCorrection coordinate upper =
      (Real.sqrt upper : ℂ) •
        (burnolMultiplicativeDilation (-Real.log upper) (burnolUnitTailResponse coordinate 1) -
          fullMellinTranslationCharacter coordinate.value (-Real.log upper) •
            burnolUnitTailResponse coordinate 1) -
        fourierL2 (burnolReciprocalStepNativeWave 1 upper) := by
  unfold burnolPaBandResponseCorrection
  rw [burnolPaBandResolvent_action, ← burnolPaBandResponse_character coordinate upper positive]
  module

theorem burnolPaBandResponseCorrection_dilation_mem (coordinate : BurnolCompletedMellinCoordinate)
    (upper shift : ℝ) (ordered : 1 ≤ upper) (bounded : upper ≤ 3 / 2)
    (small : |shift| ≤ Real.log 2) :
    burnolMultiplicativeDilation shift (burnolPaBandResponseCorrection coordinate upper) ∈
      burnolOriginalPaInL2 := by
  have positive : 0 < upper := lt_of_lt_of_le (by norm_num) ordered
  have inverseSmall : |(-shift)| ≤ Real.log 2 := by simpa only [abs_neg] using small
  have bounds := burnolPaResponseShift_bounds (-shift) inverseSmall
  have ordinary := burnolUnitOne_actualCurrent_memPa coordinate shift
    (by linarith : (1 / 4 : ℝ) < Real.exp (-shift)) (by linarith : Real.exp (-shift) < 4)
  have moved : Real.exp (-(shift + -Real.log upper)) = Real.exp (-shift) * upper := by
    rw [neg_add, neg_neg, Real.exp_add, Real.exp_log positive]
  have adjusted := burnolUnitOne_actualCurrent_memPa coordinate (shift + -Real.log upper)
    (by rw [moved]; nlinarith [Real.exp_pos (-shift)])
    (by rw [moved]; nlinarith [Real.exp_pos (-shift)])
  have character :
      fullMellinTranslationCharacter coordinate.value (shift + -Real.log upper) =
        fullMellinTranslationCharacter coordinate.value (-Real.log upper) *
          fullMellinTranslationCharacter coordinate.value shift := by
    unfold fullMellinTranslationCharacter
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have movedCurrent : burnolMultiplicativeDilation shift
      (burnolMultiplicativeDilation (-Real.log upper) (burnolUnitTailResponse coordinate 1) -
        fullMellinTranslationCharacter coordinate.value (-Real.log upper) •
          burnolUnitTailResponse coordinate 1) ∈ burnolOriginalPaInL2 := by
    have generated := burnolOriginalPaInL2.sub_mem adjusted
      (burnolOriginalPaInL2.smul_mem
        (fullMellinTranslationCharacter coordinate.value (-Real.log upper)) ordinary)
    rw [map_sub, map_smul, burnolMultiplicativeDilation_add]
    convert generated using 1
    rw [character]
    module
  have fourierBand : burnolMultiplicativeDilation shift
      (fourierL2 (burnolReciprocalStepNativeWave 1 upper)) ∈ burnolOriginalPaInL2 := by
    have generated := burnolOriginalPaInL2_fourier
      (burnolPaInteriorBand_dilation_mem upper (-shift) ordered bounded inverseSmall)
    rw [fourierL2_burnolMultiplicativeDilation, neg_neg] at generated
    exact generated
  rw [burnolPaBandResponseCorrection_source coordinate upper positive, map_sub, map_smul]
  exact burnolOriginalPaInL2.sub_mem
    (burnolOriginalPaInL2.smul_mem _ movedCurrent) fourierBand

/-- The actual finite response minus its generated unit-source character component. -/
def burnolPaCombResponseCorrection (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ) : BurnolL2 :=
  (1 / 2 : ℂ) •
    (burnolDirectRightResolvent (coordinate.value / 2) (burnolPaCombApproximation n : BurnolL2) +
      fourierL2 (burnolDirectRightResolvent (coordinate.value / 2) (burnolPaCombApproximation n : BurnolL2))) -
    burnolPaCombResponseCoefficient coordinate.value n •
      (burnolUnitTailResponse coordinate 1 + fourierL2 (burnolUnitTailResponse coordinate 1))

theorem burnolPaCombResponseCorrection_source (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ) :
    burnolPaCombResponseCorrection coordinate n =
      (((n : ℂ) + 2) / coordinate.value) •
        (burnolPaBandResponseCorrection coordinate (1 + burnolPaCombSourceWidth n) +
          fourierL2 (burnolPaBandResponseCorrection coordinate (1 + burnolPaCombSourceWidth n))) := by
  have nonzero : coordinate.value ≠ 0 := by
    intro zero
    have lower := coordinate.rightHalf
    rw [zero] at lower
    norm_num at lower
  have factor : (((n : ℂ) + 2) / coordinate.value) * (coordinate.value / 2) =
      ((n : ℂ) + 2) / 2 := by field_simp
  unfold burnolPaCombResponseCorrection burnolPaBandResponseCorrection burnolPaCombResponseCoefficient
  rw [burnolPaCombApproximation_raw, burnolDirectRightResolvent_smul]
  simp only [map_sub, map_smul, smul_add, smul_sub, smul_smul]
  rw [factor]
  module

/-- One source-owned margin works for every counted band and both directions. -/
theorem burnolPaCombResponseCorrection_dilation_mem (coordinate : BurnolCompletedMellinCoordinate)
    (n : ℕ) (shift : ℝ) (small : |shift| ≤ Real.log 2) :
    burnolMultiplicativeDilation shift (burnolPaCombResponseCorrection coordinate n) ∈ burnolOriginalPaInL2 := by
  have ordered : 1 ≤ 1 + burnolPaCombSourceWidth n := by
    linarith [(burnolPaCombSourceWidth_bounds n).1]
  have bounded : 1 + burnolPaCombSourceWidth n ≤ 3 / 2 := by
    linarith [(burnolPaCombSourceWidth_bounds n).2]
  have forward := burnolPaBandResponseCorrection_dilation_mem coordinate _ shift ordered bounded small
  have inverse := burnolOriginalPaInL2_fourier
    (burnolPaBandResponseCorrection_dilation_mem coordinate _ (-shift) ordered bounded
      (by simpa only [abs_neg] using small))
  rw [fourierL2_burnolMultiplicativeDilation, neg_neg] at inverse
  rw [burnolPaCombResponseCorrection_source, map_smul, map_add]
  exact burnolOriginalPaInL2.smul_mem _
    (burnolOriginalPaInL2.add_mem forward inverse)
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
