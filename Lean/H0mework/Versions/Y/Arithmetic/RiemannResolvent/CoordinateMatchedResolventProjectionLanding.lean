import H0mework.Versions.Y.Arithmetic.RiemannResolvent.StableAnnulusResolventLanding
import H0mework.Versions.Y.Arithmetic.RiemannResolvent.CoordinateMatchedExactOrderClosedRange

/-!
# Coordinate-matched resolvent projection landing

The same normalized compact source that exposes the nonzero exact-order
bare-zeta coordinate supplies its full finite dilation segment.  Hence its
resolvent action produces projection preservation and closed-range boundary
landing without a caller-supplied `boundaryMem` premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState

noncomputable section

local instance burnolCoordinateMatchedAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolCoordinateNormalizedAnnulusDilationSegment (coordinate : ℂ) :
    BurnolCompactAnnulusDilationSegment
      (burnolCoordinateNormalizedAnnulusSource coordinate) where
  sourceAt := burnolCoordinateNormalizedAnnulusDilationSource coordinate
  sourceAt_coe :=
    burnolCoordinateNormalizedAnnulusDilationSource_coe coordinate

/-- Direct modified-WeakFE source consumer.  The selected zero generates the
normalized source, its actual feature-completion resolvent, the Burnol
projection square and the finite closed-range boundary.  The exact-order
localized scalar is simultaneously the existing nonzero bare-zeta read. -/
theorem zeroOwnedCoordinateMatchedResolventProjection_directConsumer
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift)
    (shiftBounded : shift ≤ Real.log 16) :
    let z := observation.coordinate / 2
    let positive : 0 < z.re := by
      rw [Complex.div_re]
      norm_num
      linarith
    let belowHalf : z.re < (1 / 2 : ℝ) := by
      rw [Complex.div_re]
      norm_num
      linarith [observation.coordinate_re_lt_one]
    let source := burnolCoordinateNormalizedAnnulusSource observation.coordinate
    let completionValue :=
      burnolSourceQuarterCompletionValue source z positive belowHalf
    let resolvent := quarterFeatureCompletionRightResolvent z completionValue
    quarterMellinL2Functional z
        (burnolSourceQuarterRelation source z positive belowHalf) = 0 ∧
      burnolSourceFeatureCompletionPhysicalMap z
          (quarterFeatureCompletionTranslation z shift resolvent) =
        burnolEvenAmbientProjection
          (burnolMultiplicativeDilation (-shift / 2)
            (quarterMellinFeatureCompletionEvenAdditive z resolvent)) ∧
      burnolSourceQuarterBoundaryPhysicalLanding
          source z positive belowHalf shift ∈
        burnolCompactCoPoissonClosedRange ∧
      SourceGeneratedHilbertCokernel.residual burnolCompactCoPoissonLanding
          (burnolSourceFeatureCompletionPhysicalMap z
            (quarterFeatureCompletionTranslation z shift resolvent)) =
        positiveMellinQuarterRightResolventCharacter z shift •
          SourceGeneratedHilbertCokernel.residual burnolCompactCoPoissonLanding
            (burnolSourceQuarterRightResolventPhysicalState
              source z positive belowHalf) ∧
      burnolCoordinateMatchedLocalizedSpectrum owner observation.coordinate
          observation.coordinate =
        generatedRiemannBareZeroLocalizedSpectrum owner observation.coordinate
          observation.coordinate ∧
      burnolCoordinateMatchedLocalizedSpectrum owner observation.coordinate
          observation.coordinate ≠ 0 := by
  dsimp only
  have rightQuarter' : 1 / 4 < (observation.coordinate / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact LinearMap.congr_fun
      (selectedZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
        observation nontrivial)
      (burnolCoordinateNormalizedAnnulusSource observation.coordinate).1
  · exact burnolSourceFeatureCompletionPhysicalMap_translation
      (observation.coordinate / 2) shift _
  · exact burnolSourceQuarterBoundaryPhysicalLanding_mem_closedRange
      (burnolCoordinateNormalizedAnnulusSource observation.coordinate)
      (burnolCoordinateNormalizedAnnulusDilationSegment observation.coordinate)
      (observation.coordinate / 2) _ _ shift shiftBounded
  · exact burnolSourceQuarterRightResolvent_orthogonalResidual_eigenlaw
      (burnolCoordinateNormalizedAnnulusSource observation.coordinate)
      (burnolCoordinateNormalizedAnnulusDilationSegment observation.coordinate)
      (observation.coordinate / 2) rightQuarter' _ _
      shift shiftNonnegative shiftBounded
  · exact burnolCoordinateMatchedLocalizedSpectrum_at_eq_bare
      owner observation.coordinate
  · exact burnolCoordinateMatchedLocalizedSpectrum_at_ne_zero
      observation nontrivial

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
