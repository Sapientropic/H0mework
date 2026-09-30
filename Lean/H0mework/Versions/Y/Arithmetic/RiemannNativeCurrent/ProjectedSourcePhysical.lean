import H0mework.Versions.Y.Arithmetic.RiemannSourceGreen.ProjectedSourceClosedRange
import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.ResolventPhysical
import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.FourierPhysical

/-! The same zero generates physical division and the exact original unit-class read for every Pa input. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolPaResolvent_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (p : BurnolPaAmbientCarrier) (inPa : p ∈ burnolCompactCoPoissonClosedRange) :
    burnolDirectRightResolvent (observation.coordinate / 2) (p : BurnolL2) ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  obtain ⟨correction, _, same⟩ := Submodule.mem_map.mp (burnolPaResolvent_source_correction coordinate p inPa)
  change burnolDirectRightResolvent (coordinate.value / 2) (p : BurnolL2) ∈ _
  rw [sub_eq_iff_eq_add.mp same.symm]
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).add_mem correction.2
    ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).smul_mem _
      (burnolZeroOwnedUnitTailResponse_physical observation nontrivial rightHalf))

def burnolPaResolventPhysicalResponse {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (p : BurnolPaAmbientCarrier) (inPa : p ∈ burnolCompactCoPoissonClosedRange) :
    BurnolPaAmbientCarrier :=
  ⟨burnolDirectRightResolvent (observation.coordinate / 2) (p : BurnolL2),
    burnolPaResolvent_physical observation nontrivial rightHalf p inPa⟩

theorem burnolPaResolventPhysicalResponse_Q {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (p : BurnolPaAmbientCarrier) (inPa : p ∈ burnolCompactCoPoissonClosedRange) :
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolPaResolventPhysicalResponse observation nontrivial rightHalf p inPa) =
    burnolPaResolventSourceCoefficient (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) p •
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
        (burnolZeroOwnedUnitTailState observation nontrivial rightHalf) := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  obtain ⟨c, hc, same⟩ := Submodule.mem_map.mp (burnolPaResolvent_source_correction coordinate p inPa)
  have physical :
      burnolPaResolventPhysicalResponse observation nontrivial rightHalf p inPa =
      c + burnolPaResolventSourceCoefficient coordinate p • burnolZeroOwnedUnitTailState observation nontrivial rightHalf :=
    Subtype.ext (sub_eq_iff_eq_add.mp same.symm)
  rw [physical, map_add, map_smul, Submodule.starProjection_orthogonal_apply_eq_zero hc, zero_add]

theorem burnolPaResolventPhysicalResponse_pairedQ {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (p : BurnolPaAmbientCarrier) (inPa : p ∈ burnolCompactCoPoissonClosedRange) :
    let response := burnolPaResolventPhysicalResponse observation nontrivial rightHalf p inPa
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      ((1 / 2 : ℂ) • (response + evenFaceFourierEquiv burnolUnscaledCommonGapRadius response)) =
    (burnolPaResolventSourceCoefficient (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) p / 2) •
      (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) := by
  let Q := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  have covariance (value : BurnolPaAmbientCarrier) : Q (F value) = F (Q value) :=
    (congrArg (fun result : SourceGeneratedHilbertCokernel.OrthogonalResidual
      burnolCompactCoPoissonLanding => (result : BurnolPaAmbientCarrier))
      (burnolCompactCoPoissonActionSquare.orthogonalAction_residual value)).symm
  dsimp only
  change Q ((1 / 2 : ℂ) • (_ + F _)) = _ • Q (_ + F _)
  rw [map_smul, map_add, covariance, burnolPaResolventPhysicalResponse_Q, map_smul]
  rw [map_add, covariance]
  module

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
