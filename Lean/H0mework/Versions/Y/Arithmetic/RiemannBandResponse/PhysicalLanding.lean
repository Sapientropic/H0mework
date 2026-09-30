import H0mework.Versions.Y.Arithmetic.RiemannBandResponse.PhysicalBand
import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.ResolventPhysical

/-! The same zero admits every original native Pa forcing response into the original physical carrier. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolPaBandResolvent_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (upper : ℝ) (ordered : 1 ≤ upper) (bounded : upper < 4) :
    burnolDirectRightResolvent (observation.coordinate / 2)
      (fourierL2 (burnolReciprocalStepNativeWave 1 upper)) ∈
        evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  have generated := burnolPaBandResolvent_classResidual coordinate upper ordered bounded
  obtain ⟨correction, _, correctionRead⟩ := Submodule.mem_map.mp generated
  have scaled : (coordinate.value / 2) • burnolDirectRightResolvent (coordinate.value / 2)
      (fourierL2 (burnolReciprocalStepNativeWave 1 upper)) ∈
        evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
    rw [← sub_add_cancel ((coordinate.value / 2) • burnolDirectRightResolvent (coordinate.value / 2)
        (fourierL2 (burnolReciprocalStepNativeWave 1 upper)))
      ((Complex.exp (coordinate.value * (Real.log upper : ℂ)) - 1) • burnolUnitTailResponse coordinate 1),
      ← correctionRead]
    exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).add_mem correction.2
      ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).smul_mem _
        (burnolZeroOwnedUnitResponse_one_physical observation nontrivial rightHalf))
  have zNe : coordinate.value / 2 ≠ 0 := by
    intro zero
    have realPart := congrArg Complex.re zero
    rw [Complex.div_re] at realPart
    norm_num at realPart
    linarith [coordinate.rightHalf]
  exact ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.smul_mem_iff zNe).mp scaled

theorem burnolPaCombResolvent_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    burnolDirectRightResolvent (observation.coordinate / 2)
      (burnolPaCombApproximation n : BurnolL2) ∈
        evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  rw [burnolPaCombApproximation_raw, burnolDirectRightResolvent_smul]
  apply (evenBurnolClosedFace burnolUnscaledCommonGapRadius).smul_mem
  exact burnolPaBandResolvent_physical observation nontrivial rightHalf _
    (by linarith [(burnolPaCombSourceWidth_bounds n).1])
    (by linarith [(burnolPaCombSourceWidth_bounds n).2])

def burnolPaCombPhysicalResponse {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) : BurnolPaAmbientCarrier :=
  ⟨burnolDirectRightResolvent (observation.coordinate / 2) (burnolPaCombApproximation n : BurnolL2),
    burnolPaCombResolvent_physical observation nontrivial rightHalf n⟩

theorem burnolPaCombPhysicalResponse_scaledQ {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    (observation.coordinate / 2) •
        burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
          (burnolPaCombPhysicalResponse observation nontrivial rightHalf n) =
      (((n : ℂ) + 2) * (Complex.exp (observation.coordinate *
        (Real.log (1 + burnolPaCombSourceWidth n) : ℂ)) - 1)) •
        burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
          (burnolZeroOwnedUnitOneState observation nontrivial rightHalf) := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  have band := burnolPaBandResolvent_classResidual coordinate (1 + burnolPaCombSourceWidth n)
    (by linarith [(burnolPaCombSourceWidth_bounds n).1])
    (by linarith [(burnolPaCombSourceWidth_bounds n).2])
  have scaled := burnolOriginalPaInL2.smul_mem ((n : ℂ) + 2) band
  change ((n : ℂ) + 2) • ((observation.coordinate / 2) •
    burnolDirectRightResolvent (observation.coordinate / 2)
      (fourierL2 (burnolReciprocalStepNativeWave 1 (1 + burnolPaCombSourceWidth n))) -
    (Complex.exp (observation.coordinate * (Real.log (1 + burnolPaCombSourceWidth n) : ℂ)) - 1) •
      burnolUnitTailResponse coordinate 1) ∈ burnolOriginalPaInL2 at scaled
  have raw : (observation.coordinate / 2) •
      burnolDirectRightResolvent (observation.coordinate / 2) (burnolPaCombApproximation n : BurnolL2) -
      (((n : ℂ) + 2) * (Complex.exp (observation.coordinate *
        (Real.log (1 + burnolPaCombSourceWidth n) : ℂ)) - 1)) •
          burnolUnitTailResponse coordinate 1 ∈ burnolOriginalPaInL2 := by
    rw [burnolPaCombApproximation_raw, burnolDirectRightResolvent_smul]
    convert scaled using 1
    module
  obtain ⟨correction, correctionIn, correctionRead⟩ := Submodule.mem_map.mp raw
  have physical : correction =
      (observation.coordinate / 2) • burnolPaCombPhysicalResponse observation nontrivial rightHalf n -
        (((n : ℂ) + 2) * (Complex.exp (observation.coordinate *
          (Real.log (1 + burnolPaCombSourceWidth n) : ℂ)) - 1)) •
            burnolZeroOwnedUnitOneState observation nontrivial rightHalf :=
    Subtype.ext correctionRead
  have killed := Submodule.starProjection_orthogonal_apply_eq_zero correctionIn
  rw [physical, map_sub, map_smul, map_smul] at killed
  exact sub_eq_zero.mp killed
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
