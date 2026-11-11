import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Landing.Iterated.Signed.ClozelBurnolPaResidualSignedJordanAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.Residual.Action.ClozelAnalyticComplementExactOrderPaJordanAction

/-! # Same-source exact-order signed Jordan action -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedHilbertCokernel
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal

noncomputable section

local instance signedPart3PaAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local instance (priority := 10000) signedPart3PaResidualRealModule :
    Module ℝ BurnolPaResidual :=
  Module.restrictScalars ℝ ℂ BurnolPaResidual

local instance (priority := 10000) signedPart3PaResidualRealNormedSpace :
    NormedSpace ℝ BurnolPaResidual :=
  NormedSpace.restrictScalars ℝ ℂ BurnolPaResidual

local instance signedPart3PaResidualComplete : CompleteSpace BurnolPaResidual := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete

/-- Exact Xi-order translation law on the full signed source interval. -/
theorem burnolAnalyticComplementExactOrderPaResidual_signed_translation_jordanAction
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ)
    (shiftLower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (shiftUpper : shift ≤ Real.log 16) :
    burnolPaResidualRead (observation.coordinate / 2)
        (quarterFeatureCompletionTranslation (observation.coordinate / 2) shift
          (burnolAnalyticComplementExactOrderCompletionResolvent
            observation nontrivial)) =
      positiveMellinQuarterRightResolventCharacter
          (observation.coordinate / 2) shift •
        burnolAnalyticComplementExactOrderPaResidualJordanCoordinate
          observation nontrivial shift := by
  have rightQuarter : 1 / 4 < (observation.coordinate / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  simpa only [burnolAnalyticComplementExactOrderCompletionResolvent,
    burnolAnalyticComplementCompletionSource,
    burnolAnalyticComplementExactOrderPaResidualJordanCoordinate] using
    burnolPaResidualRead_resolventIterate_signed_jordanAction
      (burnolAnalyticComplementNormalizedSource observation)
      (burnolAnalyticComplementSignedDilationSegment observation)
      (observation.coordinate / 2) rightQuarter
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      (generatedRiemannXiZeroOrder owner observation.coordinate)
      shift shiftLower shiftUpper

/-- Final physical spelling: the exact-order raw state is dilated first,
projected to the even Burnol carrier, and only then read in `P_a⊥`. -/
theorem burnolAnalyticComplementExactOrderPaResidual_signed_dilation_jordanAction
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ)
    (shiftLower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (shiftUpper : shift ≤ Real.log 16) :
    residual burnolCompactCoPoissonLanding
        (burnolEvenAmbientProjection
          (burnolMultiplicativeDilation (-shift / 2)
            (burnolAnalyticComplementExactOrderAdditiveState
              observation nontrivial))) =
      positiveMellinQuarterRightResolventCharacter
          (observation.coordinate / 2) shift •
        burnolAnalyticComplementExactOrderPaResidualJordanCoordinate
          observation nontrivial shift := by
  rw [← burnolAnalyticComplementExactOrder_projectionPreservation
    observation nontrivial shift]
  exact
    burnolAnalyticComplementExactOrderPaResidual_signed_translation_jordanAction
      observation nontrivial rightHalf shift shiftLower shiftUpper


end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
