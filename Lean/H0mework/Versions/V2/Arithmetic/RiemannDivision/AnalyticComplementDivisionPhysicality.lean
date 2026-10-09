import H0mework.Versions.V2.Arithmetic.RiemannDivision.AnalyticComplementHeatJetContinuation
import H0mework.Versions.V2.Arithmetic.RiemannDivision.RightDivisionClosedFace
import H0mework.Versions.V2.Arithmetic.BurnolMellin.PhysicalHeatMellinConvergence

/-! # Source-generated physicality of analytic-complement divisions -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set Filter FourierTransform
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal InnerProductSpace Topology

noncomputable section

/-- Sonine division closure generates physicality of every raw state up to
the exact Xi zero order.  Each successor consumes the Fourier zero generated
from the previous state's analytic heat continuation. -/
theorem burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (k : ℕ)
    (atMostOrder :
      k ≤ generatedRiemannXiZeroOrder owner observation.coordinate) :
    burnolAnalyticComplementDivisionAdditiveState observation nontrivial k ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
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
      exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).smul_mem
        (2 : ℂ)
        (burnolCompactAdditiveL2_mem_evenBurnolClosedFace
          (burnolAnalyticComplementNormalizedSource observation))
  | succ k inductionHypothesis =>
      have previousAtMost :
          k ≤ generatedRiemannXiZeroOrder owner observation.coordinate := by
        omega
      have previousPhysical := inductionHypothesis previousAtMost
      have previousBefore :
          k < generatedRiemannXiZeroOrder owner observation.coordinate := by
        omega
      have previousFourierZero :=
        burnolAnalyticComplementDivisionRawFourierRead_zero_of_physical
          observation nontrivial rightHalf k previousBefore previousPhysical
      have rightQuarter : 1 / 4 < (observation.coordinate / 2).re := by
        rw [Complex.div_re]
        norm_num
        linarith
      have belowHalf : (observation.coordinate / 2).re < 1 / 2 := by
        rw [Complex.div_re]
        norm_num
        linarith [observation.coordinate_re_lt_one]
      have positiveRadius : 0 < burnolUnscaledCommonGapRadius := by
        norm_num [burnolUnscaledCommonGapRadius]
      unfold burnolAnalyticComplementDivisionAdditiveState
      rw [burnolAnalyticComplementDivisionState_succ]
      apply quarterMellinFeatureCompletionEvenAdditive_rightResolvent_mem_evenBurnolClosedFace
        burnolUnscaledCommonGapRadius positiveRadius
        (observation.coordinate / 2) rightQuarter belowHalf
        (burnolAnalyticComplementDivisionState observation nontrivial k)
        previousPhysical
      have coordinateEq :
          burnolDivisionCoordinate (observation.coordinate / 2)
              rightQuarter belowHalf =
            burnolDivisionZeroCompletedMellinCoordinate observation rightHalf := by
        unfold burnolDivisionCoordinate
          burnolDivisionZeroCompletedMellinCoordinate
        congr 1
        ring
      rw [coordinateEq]
      change burnolCompletedMellinEvaluator
          (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
          (evenFaceFourier burnolUnscaledCommonGapRadius
            ⟨burnolAnalyticComplementDivisionAdditiveState
              observation nontrivial k, previousPhysical⟩) = 0
      exact previousFourierZero

/-- Unconditional preterminal center zero for the raw source-generated
right-resolvent state. -/
theorem burnolAnalyticComplementDivisionRawHeatMellin_center_eq_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (k : ℕ)
    (beforeOrder :
      k < generatedRiemannXiZeroOrder owner observation.coordinate) :
    mellin
        (burnolGenericGaussianHeatPairTotal
          (burnolAnalyticComplementDivisionAdditiveState
            observation nontrivial k))
        ((1 - observation.coordinate) / 2) = 0 := by
  have physical :=
    burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
      observation nontrivial rightHalf k (Nat.le_of_lt beforeOrder)
  have zero :=
    burnolAnalyticComplementDivisionRawHeatMellin_center_eq_zero_of_physical
      observation nontrivial rightHalf k beforeOrder physical
  have centerEq :
      burnolAnalyticComplementDivisionCenter observation =
        (1 - observation.coordinate) / 2 := by
    unfold burnolAnalyticComplementDivisionCenter
    ring
  rwa [centerEq] at zero

/-- The same preterminal value is backed by an actual convergent integral;
it is not a totalized nonintegrable branch. -/
theorem burnolAnalyticComplementDivisionRawHeatMellin_center_hasMellin_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (k : ℕ)
    (beforeOrder :
      k < generatedRiemannXiZeroOrder owner observation.coordinate) :
    HasMellin
      (burnolGenericGaussianHeatPairTotal
        (burnolAnalyticComplementDivisionAdditiveState
          observation nontrivial k))
      ((1 - observation.coordinate) / 2) 0 := by
  let physicalProof :=
    burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
      observation nontrivial rightHalf k (Nat.le_of_lt beforeOrder)
  let raw : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius :=
    ⟨burnolAnalyticComplementDivisionAdditiveState
      observation nontrivial k, physicalProof⟩
  refine ⟨?_, burnolAnalyticComplementDivisionRawHeatMellin_center_eq_zero
    observation nontrivial rightHalf k beforeOrder⟩
  exact burnolGenericGaussianHeatPair_complement_mellinConvergent raw
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)

/-- Unconditional Fourier-side zero in the exact form consumed by the
division-closure theorem. -/
theorem burnolAnalyticComplementDivisionRawFourierRead_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (k : ℕ)
    (beforeOrder :
      k < generatedRiemannXiZeroOrder owner observation.coordinate) :
    burnolCompletedMellinEvaluator
        (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
        (evenFaceFourier burnolUnscaledCommonGapRadius
          ⟨burnolAnalyticComplementDivisionAdditiveState
              observation nontrivial k,
            burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
              observation nontrivial rightHalf k
                (Nat.le_of_lt beforeOrder)⟩) = 0 := by
  exact burnolAnalyticComplementDivisionRawFourierRead_zero_of_physical
    observation nontrivial rightHalf k beforeOrder
      (burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
        observation nontrivial rightHalf k (Nat.le_of_lt beforeOrder))

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
