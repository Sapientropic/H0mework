import H0mework.Versions.Y.Arithmetic.RiemannAnnulus.AnalyticComplementFinitePartRead
import H0mework.Versions.Y.Arithmetic.BurnolMellin.FourierSiblingOrthogonalityConsumer

/-!
# Physical Fourier read of the analytic-complement state

The actual Burnol projection and ordinary Fourier action reduce the physical
completed-Mellin read to one pairing between the source-generated exact-order
additive state and the inverse-Fourier Riesz vector.  Projection membership is
not supplied by the caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped InnerProductSpace

noncomputable section

local instance burnolAnalyticComplementAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolAnalyticComplementCompletedMellinCoordinate
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    BurnolCompletedMellinCoordinate :=
  ⟨observation.coordinate, rightHalf, observation.coordinate_re_lt_one⟩

/-- The physical read is exactly the remaining source-state pairing. -/
theorem burnolAnalyticComplementExactOrderPhysicalFourierRead_eq_pairing
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let coordinate :=
      burnolAnalyticComplementCompletedMellinCoordinate observation rightHalf
    let riesz := burnolCompletedMellinRieszVector coordinate
    burnolCompletedMellinEvaluator coordinate
        (burnolAnalyticComplementExactOrderPhysicalFourierState
          observation nontrivial) =
      inner ℂ
        ((evenFaceFourierEquiv burnolUnscaledCommonGapRadius).symm riesz :
          BurnolL2)
        (burnolAnalyticComplementExactOrderAdditiveState
          observation nontrivial) := by
  dsimp only [burnolAnalyticComplementCompletedMellinCoordinate]
  rw [← burnolCompletedMellinRieszVector_readback]
  unfold burnolAnalyticComplementExactOrderPhysicalFourierState
    burnolAnalyticComplementExactOrderPhysicalState
    burnolSourceFeatureCompletionPhysicalMap
    burnolAnalyticComplementExactOrderAdditiveState
  let fourier := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  let riesz := burnolCompletedMellinRieszVector
    ⟨observation.coordinate, rightHalf, observation.coordinate_re_lt_one⟩
  let additive := quarterMellinFeatureCompletionEvenAdditive
    (observation.coordinate / 2)
    (burnolAnalyticComplementExactOrderCompletionResolvent
      observation nontrivial)
  change inner ℂ riesz
      (fourier (burnolEvenAmbientProjection additive)) = _
  calc
    _ = inner ℂ (fourier (fourier.symm riesz))
        (fourier (burnolEvenAmbientProjection additive)) := by
      rw [fourier.apply_symm_apply]
    _ = inner ℂ (fourier.symm riesz)
        (burnolEvenAmbientProjection additive) :=
      fourier.inner_map_map _ _
    _ = inner ℂ (fourier.symm riesz : BurnolL2) additive := by
      unfold burnolEvenAmbientProjection
      exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
        |>.inner_orthogonalProjectionOnto_eq_of_mem_left
          (fourier.symm riesz) additive

/-- One source-owned package: nonzero exact completion, projection square,
finite closed-range landing, nonzero analytic finite part, and the actual
physical pairing are generated together. -/
theorem burnolAnalyticComplementExactOrder_directConsumer
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (shiftBounded : shift ≤ Real.log 16) :
    burnolAnalyticComplementExactOrderCompletionResolvent
        observation nontrivial ≠ 0 ∧
      burnolSourceFeatureCompletionPhysicalMap (observation.coordinate / 2)
          (quarterFeatureCompletionTranslation
            (observation.coordinate / 2) shift
            (burnolAnalyticComplementExactOrderCompletionResolvent
              observation nontrivial)) =
        burnolEvenAmbientProjection
          (burnolMultiplicativeDilation (-shift / 2)
            (burnolAnalyticComplementExactOrderAdditiveState
              observation nontrivial)) ∧
      burnolSourceQuarterBoundaryPhysicalLanding
          (burnolAnalyticComplementNormalizedSource observation)
          (observation.coordinate / 2)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          shift ∈ burnolCompactCoPoissonClosedRange ∧
      burnolAnalyticComplementExpectedPhysicalFourierRead owner observation ≠ 0 ∧
      burnolCompletedMellinEvaluator
          (burnolAnalyticComplementCompletedMellinCoordinate
            observation rightHalf)
          (burnolAnalyticComplementExactOrderPhysicalFourierState
            observation nontrivial) =
        inner ℂ
          ((evenFaceFourierEquiv burnolUnscaledCommonGapRadius).symm
            (burnolCompletedMellinRieszVector
              (burnolAnalyticComplementCompletedMellinCoordinate
                observation rightHalf)) : BurnolL2)
          (burnolAnalyticComplementExactOrderAdditiveState
            observation nontrivial) := by
  refine ⟨burnolAnalyticComplementExactOrderCompletionResolvent_ne_zero
      observation nontrivial rightHalf,
    burnolAnalyticComplementExactOrder_projectionPreservation
      observation nontrivial shift,
    burnolAnalyticComplementSourceBoundary_mem_closedRange
      observation nontrivial shift shiftBounded,
    burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero
      observation nontrivial, ?_⟩
  exact burnolAnalyticComplementExactOrderPhysicalFourierRead_eq_pairing
    observation nontrivial rightHalf

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
