import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.AnalyticComplementPaSourceRealization
import H0mework.Versions.V2.Arithmetic.RiemannResolvent.QuarterCompletionSignedBoundary
import H0mework.Versions.V2.Arithmetic.RiemannResolvent.SignedSourceOrbit

/-! The same normalized modified-WeakFE source generates both compact signed action endpoints. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped InnerProductSpace Topology
noncomputable section

local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius

local instance signedOrbitAmbientComplete : CompleteSpace Ambient := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolAnalyticSource_oneSidedCompression_eq
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ)
    (lower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (upper : shift ≤ Real.log 16) :
    evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
        (-shift / 2)
        (burnolCompactAdditivePhysicalState
          (burnolAnalyticComplementNormalizedSource observation)) =
      burnolCompactAdditivePhysicalState
        ((burnolAnalyticComplementSignedDilationSegment observation).sourceAt
          shift lower upper) := by
  let z := selectedCoPoissonMuntzParameter observation
  let source := burnolAnalyticComplementNormalizedSource observation
  let segment := burnolAnalyticComplementSignedDilationSegment observation
  let positive := selectedCoPoissonMuntzParameter_re_pos observation nontrivial
  let belowHalf := selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial
  let sourceValue := burnolSourceQuarterCompletionValue source z positive belowHalf
  have rawBase :
      quarterMellinFeatureCompletionEvenAdditive z sourceValue =
        (2 : ℂ) • (burnolCompactAdditivePhysicalState source : BurnolL2) := by
    dsimp only [sourceValue, burnolSourceQuarterCompletionValue]
    rw [quarterMellinFeatureCompletionEvenAdditive_source]
    change (2 : ℂ) • quarterMellinAdditiveEvenRechart
        (coPoissonQuarterMellinConvergentMap z positive belowHalf source.1) = _
    rw [compactQuarterMellinAdditiveEvenRechart_eq]
    rfl
  have orbit := burnolSignedSourceFeatureCompletionPhysicalMap_orbit
    source segment z positive belowHalf shift lower upper
  have weightNe :
      positiveMellinQuarterRightResolventWeight z shift ≠ 0 := by
    unfold positiveMellinQuarterRightResolventWeight
    exact Complex.exp_ne_zero _
  have translated :
      burnolSourceFeatureCompletionPhysicalMap z
          (quarterFeatureCompletionTranslation z shift sourceValue) =
        (2 : ℂ) • burnolCompactAdditivePhysicalState
          (segment.sourceAt shift lower upper) := by
    apply smul_right_injective Ambient weightNe
    simpa only [quarterFeatureCompletionRightResolventIntegrand,
      map_smul, smul_smul, mul_assoc, mul_comm, mul_left_comm,
      sourceValue] using orbit
  have covariance := burnolSourceFeatureCompletionPhysicalMap_translation
    z shift sourceValue
  rw [translated, rawBase] at covariance
  simp only [map_smul] at covariance
  change burnolEvenAmbientProjection
      (burnolMultiplicativeDilation (-shift / 2)
        (burnolCompactAdditivePhysicalState source : BurnolL2)) = _
  exact (smul_right_injective Ambient
    (by norm_num : (2 : ℂ) ≠ 0) covariance).symm

theorem burnolAnalyticSource_pairedCompression_mem
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ) (nonnegative : 0 ≤ shift)
    (bounded : shift ≤ Real.log (16 / 9 : ℝ)) :
    burnolPairedAmbientCompression (shift / 2)
        (burnolCompactAdditivePhysicalState
          (burnolAnalyticComplementNormalizedSource observation)) ∈
      burnolCompactCoPoissonClosedRange := by
  have lowerNeg : -Real.log (16 / 9 : ℝ) ≤ -shift := by linarith
  have upperNeg : -shift ≤ Real.log 16 := by
    have : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    linarith
  have lowerPos : -Real.log (16 / 9 : ℝ) ≤ shift := by
    have : 0 ≤ Real.log (16 / 9 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have upperPos : shift ≤ Real.log 16 :=
    bounded.trans (Real.log_le_log (by norm_num) (by norm_num))
  have inverseRead := burnolAnalyticSource_oneSidedCompression_eq
    observation nontrivial (-shift) lowerNeg upperNeg
  have forwardRead := burnolAnalyticSource_oneSidedCompression_eq
    observation nontrivial shift lowerPos upperPos
  have inverseRead' :
      evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
          (shift / 2)
          (burnolCompactAdditivePhysicalState
            (burnolAnalyticComplementNormalizedSource observation)) =
        burnolCompactAdditivePhysicalState
          ((burnolAnalyticComplementSignedDilationSegment observation).sourceAt
            (-shift) lowerNeg upperNeg) := by
    simpa only [neg_neg, neg_div] using inverseRead
  rw [burnolPairedAmbientCompression]
  simp only [smul_apply, add_apply]
  rw [show -(shift / 2) = -shift / 2 by ring, inverseRead', forwardRead]
  apply burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem
  apply burnolCompactCoPoissonClosedRange.toSubmodule.add_mem
  · simpa [burnolCompactCoPoissonGenerator] using
      burnolCompactCoPoissonGenerator_mem_closedRange
        (((burnolAnalyticComplementSignedDilationSegment observation).sourceAt
          (-shift) lowerNeg upperNeg), (0 : Fin 2))
  · simpa [burnolCompactCoPoissonGenerator] using
      burnolCompactCoPoissonGenerator_mem_closedRange
        (((burnolAnalyticComplementSignedDilationSegment observation).sourceAt
          shift lowerPos upperPos), (0 : Fin 2))

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
