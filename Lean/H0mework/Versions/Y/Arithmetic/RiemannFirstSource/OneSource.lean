import H0mework.Versions.Y.Arithmetic.MobiusSource.OneSource
import H0mework.Versions.Y.Arithmetic.RiemannFirstSource.FirstCell

/-! The fixed exact-order Pa projection consumes its single joint source action. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped InnerProductSpace ENNReal
noncomputable section
local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "q" => (1 / 4 : ℝ)

local instance oneSourceActionAmbientComplete : CompleteSpace Ambient := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The fixed exact-order projection directly consumes the joint source
action; no closed-range membership is submitted by its caller. -/
theorem burnolExactOrderPaPairedProjection_oneSource {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ) (nonnegative : 0 ≤ shift) (small : shift ≤ Real.log 2) :
    let state := burnolAnalyticComplementExactOrderPhysicalState observation nontrivial
    let projection := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection state
    let source := burnolMobiusSourceL2 projection
    (burnolPairedAmbientCompression shift projection : BurnolL2) =
      pairedBurnolMultiplicativeDilation shift (projection : BurnolL2) -
        (1 / 2 : ℂ) •
          (burnolPaIntervalSourceCorrection shift source +
            fourierL2 (burnolPaIntervalSourceCorrection shift
              (burnolTateReciprocalL2 source))) := by
  dsimp only
  exact burnolPaPairedProjection_oneSource shift nonnegative small _
    (Submodule.starProjection_apply_mem _ _)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
