import H0mework.Versions.V2.Arithmetic.RiemannUnitRegularity.GeneratorCounting

/-! Source cancellation puts the full unit/Fourier pair in the actual dilation
generator domain. Its velocity is its own Fourier-odd sibling, and the pair is nonzero. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolFourierOrbit_hasDerivAt (value velocity : BurnolL2)
    (generated : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) value) velocity 0) :
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) (fourierL2 value))
      (-fourierL2 velocity) 0 := by
  have base : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) value) velocity
      ((fun h : ℝ => -h) 0) := by simpa only [neg_zero] using generated
  have negation : HasDerivAt (fun h : ℝ => -h) (-1 : ℝ) (0 : ℝ) :=
    (hasDerivAt_id (0 : ℝ)).neg
  have reverse := base.scomp (0 : ℝ) negation
  have mapped := (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 reverse
  convert! mapped using 1
  · funext h
    change burnolMultiplicativeDilation (-h / 2) (fourierL2 value) =
      fourierL2 (burnolMultiplicativeDilation (-(-h) / 2) value)
    rw [fourierL2_burnolMultiplicativeDilation]
    simp only [neg_neg, neg_div]
  · simp

theorem burnolUnitFourierPair_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) :
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2)
      (burnolUnitTailResponse coordinate 1 + fourierL2 (burnolUnitTailResponse coordinate 1)))
      ((coordinate.value / 2 - 1 / 4) •
        (burnolUnitTailResponse coordinate 1 - fourierL2 (burnolUnitTailResponse coordinate 1))) 0 := by
  let H := burnolUnitCountingPrimitiveL2
  let D := burnolDirectRightResolvent (coordinate.value / 2) H
  let alpha := coordinate.value / 2 - 1 / 4
  let coefficient := (coordinate.value - 1) / 2
  have rightQuarter : 1 / 4 < (coordinate.value / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  have derivative : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) D)
      (alpha • D + H) 0 := burnolDirectRightResolventOrbit_hasDerivAt _ rightQuarter H
  have dual := burnolFourierOrbit_hasDerivAt D (alpha • D + H) derivative
  have generated := burnolCountingPrimitiveFourierPair_hasDerivAt.neg.sub ((derivative.add dual).const_smul coefficient)
  have state : burnolUnitTailResponse coordinate 1 + fourierL2 (burnolUnitTailResponse coordinate 1) =
      -(H + fourierL2 H) - coefficient • (D + fourierL2 D) := by
    rw [burnolUnitTailResponse_one_eq_fixedResolvent]
    simp only [map_sub, map_neg, map_smul]
    change -H - coefficient • D + (-fourierL2 H - coefficient • fourierL2 D) = _
    module
  have partner : burnolUnitTailResponse coordinate 1 - fourierL2 (burnolUnitTailResponse coordinate 1) =
      -(H - fourierL2 H) - coefficient • (D - fourierL2 D) := by
    rw [burnolUnitTailResponse_one_eq_fixedResolvent]
    simp only [map_sub, map_neg, map_smul]
    change -H - coefficient • D - (-fourierL2 H - coefficient • fourierL2 D) = _
    module
  convert! generated using 1
  · funext h
    simp only [state, map_sub, map_neg, map_add, map_smul, Pi.sub_apply, Pi.neg_apply,
      Pi.smul_apply, Pi.add_apply, H]
  · rw [partner]
    simp only [map_add, map_smul]
    dsimp only [alpha, coefficient]
    module

theorem burnolUnitFourierPair_nonzero (coordinate : BurnolCompletedMellinCoordinate) :
    burnolUnitTailResponse coordinate 1 + fourierL2 (burnolUnitTailResponse coordinate 1) ≠ 0 := by
  intro zero
  have derivative := burnolUnitFourierPair_hasDerivAt coordinate
  rw [zero] at derivative
  have zeroOrbit : (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) (0 : BurnolL2)) = fun _ => 0 :=
    funext (fun _ => map_zero _)
  rw [zeroOrbit] at derivative
  have velocity := derivative.unique (hasDerivAt_const (0 : ℝ) (0 : BurnolL2))
  have scalarNonzero : coordinate.value / 2 - 1 / 4 ≠ (0 : ℂ) := by
    intro equal
    have realPart := congrArg Complex.re equal
    norm_num only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.zero_re] at realPart
    linarith [coordinate.rightHalf]
  have partnerZero := (smul_eq_zero.mp velocity).resolve_left scalarNonzero
  apply burnolUnitTailResponse_one_ne_zero coordinate
  calc
    _ = (1 / 2 : ℂ) • ((burnolUnitTailResponse coordinate 1 + fourierL2 (burnolUnitTailResponse coordinate 1)) +
        (burnolUnitTailResponse coordinate 1 - fourierL2 (burnolUnitTailResponse coordinate 1))) := by module
    _ = 0 := by rw [zero, partnerZero]; simp

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
