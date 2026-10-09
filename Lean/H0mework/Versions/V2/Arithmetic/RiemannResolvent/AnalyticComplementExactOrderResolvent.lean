import H0mework.Versions.V2.Arithmetic.RiemannAnnulus.AnalyticComplementNormalizedSource
import H0mework.Versions.V2.Arithmetic.RiemannResolvent.CoordinateMatchedExactOrderResolvent
import H0mework.Versions.V2.Arithmetic.RiemannResolvent.CoordinateMatchedResolventProjectionLanding

/-!
# Exact-order resolvent at the analytic-complement source

The source is normalized at `1-rho`, while the Hilbert action runs at
`rho/2`.  This is the exact resonance dictated by the additive rechart.
The finite action boundary lands in the existing compact co-Poisson closed
range before any quotient read.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex
open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedHilbertCokernel
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState

noncomputable section

def burnolAnalyticComplementCompletionSource
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    HilbertAmbient (quarterMellinL2Feature (observation.coordinate / 2)) :=
  burnolSourceQuarterCompletionValue
    (burnolAnalyticComplementNormalizedSource observation)
    (observation.coordinate / 2)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)

theorem burnolAnalyticComplementCompletionSource_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolAnalyticComplementCompletionSource observation nontrivial ≠ 0 := by
  intro sourceZero
  have realizationZero := congrArg
    (hilbertAmbientRealization
      (quarterMellinL2Feature (observation.coordinate / 2))) sourceZero
  unfold burnolAnalyticComplementCompletionSource
    burnolSourceQuarterCompletionValue at realizationZero
  rw [hilbertAmbientRealization_source_readback, map_zero] at realizationZero
  exact burnolCoordinateNormalizedRelation_sourceEnergy_ne_zero
    (1 - observation.coordinate) (observation.coordinate / 2)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    realizationZero

/-- Divide by the source-generated full Xi order in the correctly oriented
feature completion. -/
def burnolAnalyticComplementExactOrderCompletionResolvent
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    HilbertAmbient (quarterMellinL2Feature (observation.coordinate / 2)) :=
  quarterFeatureCompletionRightResolventIterate
    (observation.coordinate / 2)
    (generatedRiemannXiZeroOrder owner observation.coordinate)
    (burnolAnalyticComplementCompletionSource observation nontrivial)

theorem burnolAnalyticComplementExactOrderCompletionResolvent_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolAnalyticComplementExactOrderCompletionResolvent
      observation nontrivial ≠ 0 := by
  apply quarterFeatureCompletionRightResolventIterate_ne_zero
  · rw [Complex.div_re]
    norm_num
    linarith
  · exact burnolAnalyticComplementCompletionSource_ne_zero
      observation nontrivial

def burnolAnalyticComplementExactOrderAdditiveState
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : BurnolL2 :=
  quarterMellinFeatureCompletionEvenAdditive (observation.coordinate / 2)
    (burnolAnalyticComplementExactOrderCompletionResolvent
      observation nontrivial)

def burnolAnalyticComplementExactOrderPhysicalState
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    BurnolPaAmbientCarrier :=
  burnolSourceFeatureCompletionPhysicalMap (observation.coordinate / 2)
    (burnolAnalyticComplementExactOrderCompletionResolvent
      observation nontrivial)

/-- Fourier is applied inside the same physical carrier, not by creating a
second source occurrence. -/
def burnolAnalyticComplementExactOrderPhysicalFourierState
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    BurnolPaAmbientCarrier :=
  evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial)

theorem burnolAnalyticComplementExactOrder_projectionPreservation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ) :
    burnolSourceFeatureCompletionPhysicalMap (observation.coordinate / 2)
        (quarterFeatureCompletionTranslation (observation.coordinate / 2) shift
          (burnolAnalyticComplementExactOrderCompletionResolvent
            observation nontrivial)) =
      burnolEvenAmbientProjection
        (burnolMultiplicativeDilation (-shift / 2)
          (burnolAnalyticComplementExactOrderAdditiveState
            observation nontrivial)) := by
  exact burnolSourceFeatureCompletionPhysicalMap_translation
    (observation.coordinate / 2) shift _

/-- The finite source boundary is generated in the established compact
co-Poisson range.  Membership is an output of the source orbit. -/
theorem burnolAnalyticComplementSourceBoundary_mem_closedRange
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ) (shiftBounded : shift ≤ Real.log 16) :
    burnolSourceQuarterBoundaryPhysicalLanding
        (burnolAnalyticComplementNormalizedSource observation)
        (observation.coordinate / 2)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        shift ∈ burnolCompactCoPoissonClosedRange := by
  exact burnolSourceQuarterBoundaryPhysicalLanding_mem_closedRange
    (burnolAnalyticComplementNormalizedSource observation)
    (burnolCoordinateNormalizedAnnulusDilationSegment
      (1 - observation.coordinate))
    (observation.coordinate / 2) _ _ shift shiftBounded

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
