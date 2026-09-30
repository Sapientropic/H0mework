import H0mework.Versions.Y.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Y.Arithmetic.RiemannBandResponse.Class

/-! The original projected head directly consumes the full Pa source-generated response law. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolPaHeadResolvent_pairedQ {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    let response := burnolPaResolventPhysicalResponse observation nontrivial rightHalf p
      (Submodule.starProjection_apply_mem _ _)
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      ((1 / 2 : ℂ) • (response + evenFaceFourierEquiv burnolUnscaledCommonGapRadius response)) =
    (burnolPaResolventSourceCoefficient (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) p / 2) •
      (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) :=
  burnolPaResolventPhysicalResponse_pairedQ observation nontrivial rightHalf _ _

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
