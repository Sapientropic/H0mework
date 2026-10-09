import H0mework.Versions.V2.Arithmetic.RiemannDivision.AnalyticComplementDivisionJet
import H0mework.Versions.V2.Arithmetic.RiemannDivision.DirectRightResolvent

/-! # Analytic-complement division states and position landing -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set Filter
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal InnerProductSpace

noncomputable section

/-- A quarter coordinate in the open physical Mellin strip gives the full
Burnol completed-Mellin coordinate `2w`. -/
def burnolDivisionCompletedMellinCoordinate
    (w : ℂ) (rightQuarter : 1 / 4 < w.re)
    (belowHalf : w.re < 1 / 2) : BurnolCompletedMellinCoordinate where
  value := 2 * w
  rightHalf := by
    simp only [mul_re]
    norm_num
    linarith
  belowOne := by
    simp only [mul_re]
    norm_num
    linarith

@[simp] theorem burnolDivisionCompletedMellinCoordinate_value
    (w : ℂ) (rightQuarter : 1 / 4 < w.re)
    (belowHalf : w.re < 1 / 2) :
    (burnolDivisionCompletedMellinCoordinate
      w rightQuarter belowHalf).value = 2 * w := rfl

/-- The actual source-generated completion state after `k` right-resolvent
steps. -/
def burnolAnalyticComplementDivisionState
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (k : ℕ) :
    HilbertAmbient (quarterMellinL2Feature (observation.coordinate / 2)) :=
  quarterFeatureCompletionRightResolventIterate
    (observation.coordinate / 2) k
    (burnolAnalyticComplementCompletionSource observation nontrivial)

@[simp] theorem burnolAnalyticComplementDivisionState_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolAnalyticComplementDivisionState observation nontrivial 0 =
      burnolAnalyticComplementCompletionSource observation nontrivial := rfl

@[simp] theorem burnolAnalyticComplementDivisionState_succ
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (k : ℕ) :
    burnolAnalyticComplementDivisionState observation nontrivial (k + 1) =
      quarterFeatureCompletionRightResolvent (observation.coordinate / 2)
        (burnolAnalyticComplementDivisionState observation nontrivial k) := rfl

def burnolAnalyticComplementDivisionAdditiveState
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (k : ℕ) : BurnolL2 :=
  quarterMellinFeatureCompletionEvenAdditive (observation.coordinate / 2)
    (burnolAnalyticComplementDivisionState observation nontrivial k)

private theorem divisionJet_additive_rightResolvent
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : HilbertAmbient (quarterMellinL2Feature z)) :
    quarterMellinFeatureCompletionEvenAdditive z
        (quarterFeatureCompletionRightResolvent z value) =
      -∫ shift : ℝ in Ioi (0 : ℝ),
        positiveMellinQuarterRightResolventWeight z shift •
          burnolMultiplicativeDilation (-shift / 2)
            (quarterMellinFeatureCompletionEvenAdditive z value) := by
  have integrable := quarterFeatureCompletionRightResolventIntegrand_integrableOn
    z rightQuarter value
  unfold quarterFeatureCompletionRightResolvent
  rw [map_neg, ← (quarterMellinFeatureCompletionEvenAdditive z
    ).integral_comp_comm integrable]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro shift _
  unfold quarterFeatureCompletionRightResolventIntegrand
  change quarterMellinFeatureCompletionEvenAdditive z
      (positiveMellinQuarterRightResolventWeight z shift •
        quarterFeatureCompletionTranslation z shift value) = _
  rw [map_smul, quarterMellinFeatureCompletionEvenAdditive_translation]

theorem burnolAnalyticComplementDivisionAdditiveState_positionGap
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (k : ℕ) :
    burnolAnalyticComplementDivisionAdditiveState observation nontrivial k ∈
      locallyConstantFace burnolUnscaledCommonGapRadius := by
  induction k with
  | zero =>
      unfold burnolAnalyticComplementDivisionAdditiveState
      rw [burnolAnalyticComplementDivisionState_zero]
      unfold burnolAnalyticComplementCompletionSource
        burnolSourceQuarterCompletionValue burnolSourceQuarterRelation
      rw [quarterMellinFeatureCompletionEvenAdditive_source]
      have rechart := compactQuarterMellinAdditiveEvenRechart_eq
        (observation.coordinate / 2)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (burnolAnalyticComplementNormalizedSource observation)
      rw [show quarterMellinAdditiveEvenRechart
          (coPoissonQuarterMellinConvergentMap
            (observation.coordinate / 2)
            (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
            (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
            (burnolAnalyticComplementNormalizedSource observation).1) =
          burnolCompactAdditiveL2
            (burnolAnalyticComplementNormalizedSource observation) by
        simpa only using rechart]
      exact (locallyConstantFace burnolUnscaledCommonGapRadius).smul_mem
        (2 : ℂ)
        (burnolCompactAdditiveL2_mem_locallyConstantFace
          (burnolAnalyticComplementNormalizedSource observation))
  | succ k inductionHypothesis =>
      have rightQuarter : 1 / 4 < (observation.coordinate / 2).re := by
        rw [Complex.div_re]
        norm_num
        linarith
      unfold burnolAnalyticComplementDivisionAdditiveState
      rw [burnolAnalyticComplementDivisionState_succ,
        divisionJet_additive_rightResolvent
          (observation.coordinate / 2) rightQuarter]
      apply (locallyConstantFace burnolUnscaledCommonGapRadius).neg_mem
      apply integral_mem_closedSubmodule
        { toSubmodule := locallyConstantFace burnolUnscaledCommonGapRadius
          isClosed' := locallyConstantFace_isClosed
            burnolUnscaledCommonGapRadius }
      · have mapped := (quarterMellinFeatureCompletionEvenAdditive
          (observation.coordinate / 2)).integrable_comp
          (quarterFeatureCompletionRightResolventIntegrand_integrableOn
            (observation.coordinate / 2) rightQuarter
            (burnolAnalyticComplementDivisionState
              observation nontrivial k))
        apply mapped.congr
        filter_upwards with shift
        unfold quarterFeatureCompletionRightResolventIntegrand
        rw [map_smul,
          quarterMellinFeatureCompletionEvenAdditive_translation]
      · filter_upwards [ae_restrict_mem measurableSet_Ioi]
          with shift positiveShift
        apply (locallyConstantFace burnolUnscaledCommonGapRadius).smul_mem
        apply burnolMultiplicativeDilation_mem_locallyConstantFace_of_nonpositive
          burnolUnscaledCommonGapRadius
          (by norm_num [burnolUnscaledCommonGapRadius])
        · exact div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr positiveShift.le) (by norm_num)
        · exact inductionHypothesis

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
