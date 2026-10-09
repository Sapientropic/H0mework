import H0mework.Versions.V2.Arithmetic.MobiusSource.WindowClosedRange
import H0mework.Versions.V2.Arithmetic.RiemannDivision.AnalyticComplementExactOrderPaResidualState

/-!
# The exact-order modified-WeakFE projection consumes its actual source

The already fixed Pa projection now reads its finite Möbius source and
replays on every finite window. This is the same source occurrence, not a
supplied projection-preservation or range witness.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction BigOperators InnerProductSpace ENNReal
noncomputable section

local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "Window" => BurnolRadiusIntervalL2 4

local instance burnolReplayAmbientComplete : CompleteSpace Ambient := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The same exact-order modified-WeakFE occurrence now has an explicit finite
Möbius source and its actual co-Poisson replay on every finite window. -/
theorem burnolExactOrderPaProjection_source_replay
    {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (radius : ℝ) :
    let value := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial)
    burnolCoPoissonWindowReplay radius value =
      burnolRadiusRestriction radius (value : BurnolL2) := by
  dsimp only
  apply burnolCoPoissonWindowReplay_Pa
  exact (burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto
    (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial)).property

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
