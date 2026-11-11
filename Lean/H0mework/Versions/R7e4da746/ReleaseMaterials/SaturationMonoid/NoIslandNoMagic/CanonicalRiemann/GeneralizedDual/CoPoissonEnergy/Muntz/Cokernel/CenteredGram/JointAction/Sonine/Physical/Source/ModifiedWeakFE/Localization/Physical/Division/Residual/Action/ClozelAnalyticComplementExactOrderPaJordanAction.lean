import H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementExactOrderPaResidualState
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Landing.Iterated.ClozelBurnolPaResidualJordanAction

/-! # Analytic-complement exact-order Jordan action in `P_a⊥` -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex
open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedHilbertCokernel
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState

noncomputable section

local instance burnolAnalyticComplementJordanAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The Xi multiplicity selects the length of the actual residual chain. -/
def burnolAnalyticComplementExactOrderPaResidualJordanCoordinate
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ) : BurnolPaResidual :=
  burnolPaResidualJordanCoordinate
    (observation.coordinate / 2)
    (burnolAnalyticComplementCompletionSource observation nontrivial)
    (generatedRiemannXiZeroOrder owner observation.coordinate) shift

/-- Exact translation law of the `ord`-fold modified-WeakFE resolvent. -/
theorem burnolAnalyticComplementExactOrderPaResidual_translation_jordanAction
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift)
    (shiftBounded : shift ≤ Real.log 16) :
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
    burnolAnalyticComplementNormalizedSource,
    burnolAnalyticComplementExactOrderPaResidualJordanCoordinate] using
    burnolPaResidualRead_resolventIterate_jordanAction
      (burnolCoordinateNormalizedAnnulusSource (1 - observation.coordinate))
      (burnolCoordinateNormalizedAnnulusDilationSegment
        (1 - observation.coordinate))
      (observation.coordinate / 2) rightQuarter
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      (generatedRiemannXiZeroOrder owner observation.coordinate)
      shift shiftNonnegative shiftBounded

/-- At zero shift the Jordan coordinate is anchored to the already generated
nonzero exact-order position residual. -/
theorem burnolAnalyticComplementExactOrderPaResidualJordanCoordinate_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolAnalyticComplementExactOrderPaResidualJordanCoordinate
        observation nontrivial 0 =
      burnolAnalyticComplementExactOrderPaPositionResidualState
        observation nontrivial := by
  have action :=
    burnolAnalyticComplementExactOrderPaResidual_translation_jordanAction
      observation nontrivial rightHalf 0 (le_refl 0)
        (Real.log_nonneg (by norm_num))
  have translationZero :
      quarterFeatureCompletionTranslation (observation.coordinate / 2) 0
          (burnolAnalyticComplementExactOrderCompletionResolvent
            observation nontrivial) =
        burnolAnalyticComplementExactOrderCompletionResolvent
          observation nontrivial := by
    apply (hilbertAmbientRealization
      (quarterMellinL2Feature (observation.coordinate / 2))).injective
    rw [quarterFeatureCompletionTranslation_realization,
      positiveMellinQuarterEnergyTranslation_zero]
  rw [translationZero] at action
  simpa [burnolPaResidualRead,
    burnolAnalyticComplementExactOrderPaPositionResidualState,
    burnolAnalyticComplementExactOrderPhysicalState,
    positiveMellinQuarterRightResolventCharacter,
    positiveMellinQuarterRightResolventWeight] using action.symm

/-- The same law in installed multiplicative-dilation coordinates. -/
theorem burnolAnalyticComplementExactOrderPaResidual_dilation_jordanAction
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift)
    (shiftBounded : shift ≤ Real.log 16) :
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
  exact burnolAnalyticComplementExactOrderPaResidual_translation_jordanAction
    observation nontrivial rightHalf shift shiftNonnegative shiftBounded

/-- Canonical quotient spelling of the same source-generated action. -/
theorem burnolAnalyticComplementExactOrderPaCokernel_dilation_jordanAction
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift)
    (shiftBounded : shift ≤ Real.log 16) :
    quotientClass burnolCompactCoPoissonLanding
        (burnolEvenAmbientProjection
          (burnolMultiplicativeDilation (-shift / 2)
            (burnolAnalyticComplementExactOrderAdditiveState
              observation nontrivial))) =
      positiveMellinQuarterRightResolventCharacter
          (observation.coordinate / 2) shift •
        (quotientOrthogonalEquiv burnolCompactCoPoissonLanding).symm
          (burnolAnalyticComplementExactOrderPaResidualJordanCoordinate
            observation nontrivial shift) := by
  apply (quotientOrthogonalEquiv burnolCompactCoPoissonLanding).injective
  rw [quotientOrthogonalEquiv_quotientClass, map_smul]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact burnolAnalyticComplementExactOrderPaResidual_dilation_jordanAction
    observation nontrivial rightHalf shift shiftNonnegative shiftBounded

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
