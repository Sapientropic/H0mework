import H0mework.Versions.Y.Arithmetic.RiemannBandResponse.Correction

/-! The generated correction action transports the original Pa-projection current to the first actual finite response. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem ambient_mem_of_raw (value : BurnolPaAmbientCarrier)
    (belongs : (value : BurnolL2) ∈ burnolOriginalPaInL2) :
    value ∈ burnolCompactCoPoissonClosedRange := by
  obtain ⟨point, pointIn, same⟩ := Submodule.mem_map.mp belongs
  have samePoint : point = value := Subtype.ext same
  exact samePoint ▸ pointIn

theorem burnolPaCombResponseCorrection_paired_mem {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (n : ℕ) (shift : ℝ) (small : |shift| ≤ Real.log 2) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let whole := one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one
    burnolPairedAmbientCompression shift
      (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n -
        burnolPaCombResponseCoefficient observation.coordinate n • whole) ∈
          burnolCompactCoPoissonClosedRange := by
  dsimp only
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let whole := one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one
  let correction := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n -
    burnolPaCombResponseCoefficient observation.coordinate n • whole
  have positive := burnolPaCombResponseCorrection_dilation_mem coordinate n shift small
  have negative := burnolPaCombResponseCorrection_dilation_mem coordinate n (-shift)
    (by simpa only [abs_neg] using small)
  have paired : pairedBurnolMultiplicativeDilation shift (correction : BurnolL2) ∈
      burnolOriginalPaInL2 := by
    unfold pairedBurnolMultiplicativeDilation
    simp only [smul_apply, add_apply, ContinuousLinearEquiv.coe_coe]
    exact burnolOriginalPaInL2.smul_mem (1 / 2 : ℂ)
      (burnolOriginalPaInL2.add_mem positive negative)
  obtain ⟨point, pointIn, pointRead⟩ := Submodule.mem_map.mp paired
  have physical := congrArg burnolEvenAmbientProjection pointRead
  change burnolEvenAmbientProjection (point : BurnolL2) =
    burnolEvenAmbientProjection (pairedBurnolMultiplicativeDilation shift (correction : BurnolL2)) at physical
  simp only [burnolEvenAmbientProjection,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at physical
  have actionRead : burnolEvenAmbientProjection
      (pairedBurnolMultiplicativeDilation shift (correction : BurnolL2)) =
        burnolPairedAmbientCompression shift correction := by
    unfold pairedBurnolMultiplicativeDilation burnolPairedAmbientCompression
    simp only [smul_apply, add_apply, map_smul, map_add]
    rfl
  change point = burnolEvenAmbientProjection
    (pairedBurnolMultiplicativeDilation shift (correction : BurnolL2)) at physical
  rw [actionRead] at physical
  exact physical ▸ pointIn

theorem burnolPaCombProjectedSource_action {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (n : ℕ) (shift : ℝ) (small : |shift| ≤ Real.log 2) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let whole := one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolPairedAmbientCompression shift
        (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
          (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n))) =
      burnolPaCombResponseCoefficient observation.coordinate n •
        burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
          (burnolPairedAmbientCompression shift
            (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection whole)) := by
  dsimp only
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let whole := one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one
  let correction := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n -
    burnolPaCombResponseCoefficient observation.coordinate n • whole
  have atZero := burnolPaCombResponseCorrection_dilation_mem coordinate n 0
    (by simpa only [abs_zero] using (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  rw [burnolMultiplicativeDilation_zero] at atZero
  have sourceIn : correction ∈ burnolCompactCoPoissonClosedRange :=
    ambient_mem_of_raw correction atZero
  have projection := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_eq_self_iff.mpr sourceIn
  change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
    (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n -
      burnolPaCombResponseCoefficient observation.coordinate n • whole) = correction at projection
  rw [map_sub, map_smul] at projection
  have moved := burnolPaCombResponseCorrection_paired_mem observation nontrivial rightHalf n shift small
  change burnolPairedAmbientCompression shift correction ∈ burnolCompactCoPoissonClosedRange at moved
  have killed := Submodule.starProjection_orthogonal_apply_eq_zero moved
  rw [← projection, map_sub, map_smul, map_sub, map_smul] at killed
  exact sub_eq_zero.mp killed

theorem burnolPaCombProjectedSource_diagonal {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (n : ℕ) (shift : ℝ) (small : |shift| ≤ Real.log 2) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let whole := one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one
    let response := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n
    let coefficient := burnolPaCombResponseCoefficient observation.coordinate n
    inner ℂ
        (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection response)
        (burnolPairedAmbientCompression shift
          (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection response)) =
      (star coefficient * coefficient) *
        inner ℂ
          (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier)
          (burnolPairedAmbientCompression shift
            (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection whole)) := by
  dsimp only
  let state := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
  let Q := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  have read (value : BurnolPaAmbientCarrier) :
      inner ℂ (state : BurnolPaAmbientCarrier) (Q value) =
        inner ℂ (state : BurnolPaAmbientCarrier) value :=
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left state value
  rw [burnolPaCombPairedPhysicalResponse_Q observation nontrivial rightHalf n,
    inner_smul_left (𝕜 := ℂ) (E := BurnolPaAmbientCarrier)]
  change _ * inner ℂ (state : BurnolPaAmbientCarrier) _ = _
  rw [← read, burnolPaCombProjectedSource_action observation nontrivial rightHalf n shift small,
    inner_smul_right (𝕜 := ℂ) (E := BurnolPaAmbientCarrier), read]
  dsimp only [state]
  simp only [starRingEnd_apply]
  ring

/-- The original projected unit-source action is read from the same first finite response. -/
theorem burnolUnitPaProjectedSource_head {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (small : |shift| ≤ Real.log 2) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let whole := one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolPairedAmbientCompression shift
        (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection whole)) =
      (burnolPaCombResponseCoefficient observation.coordinate 0)⁻¹ •
        burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
          (burnolPairedAmbientCompression shift
            (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
              (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0))) := by
  dsimp only
  have generated := congrArg (fun value : BurnolPaAmbientCarrier =>
      (burnolPaCombResponseCoefficient observation.coordinate 0)⁻¹ • value)
    (burnolPaCombProjectedSource_action observation nontrivial rightHalf 0 shift small)
  rw [inv_smul_smul₀ (burnolPaCombResponseCoefficient_ne_zero observation.coordinate
    (lt_trans (by norm_num) rightHalf) 0)] at generated
  exact generated.symm
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
