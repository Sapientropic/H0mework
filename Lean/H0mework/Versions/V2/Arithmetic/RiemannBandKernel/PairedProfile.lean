import H0mework.Versions.V2.Arithmetic.RiemannBandKernel.PairedFourier

/-! The original paired physical response has its full two-face Dirichlet profile. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology ArithmeticFunction
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolPaCombPairedDirichletRaw (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (burnolPaCombResponseDirichletRaw s n x +
    burnolPaCombFourierResponseDirichletRaw s n x)

theorem burnolPaCombPairedPhysicalResponse_coeFn {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    ((burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n : BurnolL2) : ℝ → ℂ)
      =ᵐ[volume] burnolPaCombPairedDirichletRaw observation.coordinate n := by
  let response := burnolDirectRightResolvent (observation.coordinate / 2) (burnolPaCombApproximation n : BurnolL2)
  change (((1 / 2 : ℂ) • (response + fourierL2 response) : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (response + fourierL2 response),
    Lp.coeFn_add response (fourierL2 response),
    burnolPaCombResolvent_coeFn (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) n,
    burnolPaCombFourierResolvent_coeFn observation nontrivial rightHalf n]
    with x smulAt addAt ordinaryAt fourierAt
  rw [smulAt]
  change (1 / 2 : ℂ) * (response + fourierL2 response : BurnolL2) x = _
  rw [addAt]
  change (1 / 2 : ℂ) * (response x + fourierL2 response x) = _
  change response x = burnolPaCombResponseDirichletRaw observation.coordinate n x at ordinaryAt
  rw [ordinaryAt, fourierAt]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
