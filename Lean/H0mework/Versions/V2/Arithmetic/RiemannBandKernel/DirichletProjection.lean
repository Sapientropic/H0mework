import H0mework.Versions.V2.Arithmetic.RiemannBandKernel.DirichletResponse

/-! The original infinite Pa projection reads the same response through its explicit Dirichlet kernel. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolPaFourierBandProbe_response_normalEquation {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (a b : ℝ) (aStrict : (1 / 4 : ℝ) < a) (ordered : a ≤ b) (bounded : b < 4) (n : ℕ) :
    inner ℂ (burnolPaFourierBandProbe a b aStrict ordered bounded)
      (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
        (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n)) =
      ∫ x : ℝ, star (burnolPaFourierBandProbeRaw a b x) *
        burnolPaCombResponseDirichletRaw observation.coordinate n x := by
  rw [burnolPaFourierBandProbe_projection_response_inner, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolPaFourierBandProbe_coeFn a b aStrict ordered bounded,
    burnolPaCombResolvent_coeFn (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) n]
    with x probeAt responseAt
  change burnolDirectRightResolvent (observation.coordinate / 2)
      (burnolPaCombApproximation n : BurnolL2) x =
    burnolPaCombResponseDirichletRaw observation.coordinate n x at responseAt
  rw [probeAt, responseAt, RCLike.inner_apply, starRingEnd_apply, mul_comm]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
