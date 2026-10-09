import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.CutoffSource
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.FirstSourceSplit

/-! The original complete first source splits into its generated weighted source and its unchanged unit tail. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolCompleteFirstSource_eq_weighted_add_tail (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    burnolCompleteRemainderSource (coordinate.value / 2) source 1 =
      burnolWeightedReciprocalStepSource (1 / 4) 4 (burnolFirstSourceCoefficient coordinate source)
        (burnolFirstSourceCoefficientSlope coordinate source) +
      burnolFirstSourceMellinCoefficient coordinate.value source • burnolNormalizedFirstSourceUnitTail coordinate := by
  apply Function.Involutive.injective burnolTateReciprocalL2_involutive
  rw [map_add, map_smul]
  apply ext_inner_left ℂ
  intro test
  rw [burnolCompleteFirstSourceTate_pairing, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add
    (burnolTateReciprocalL2 (burnolWeightedReciprocalStepSource (1 / 4) 4
      (burnolFirstSourceCoefficient coordinate source) (burnolFirstSourceCoefficientSlope coordinate source)))
    (burnolFirstSourceMellinCoefficient coordinate.value source • burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate)),
    burnolFirstSourceTateWeighted_coe coordinate source,
    Lp.coeFn_smul (burnolFirstSourceMellinCoefficient coordinate.value source)
      (burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate)),
    burnolNormalizedFirstSourceUnitTail_tate_coeFn coordinate,
    volume.ae_ne (0 : ℝ)] with x hadd hweighted hsmul htail nonzero
  rw [hadd]
  change inner ℂ (test x) (burnolFourierRightDivisionRaw _ _ x) = inner ℂ (test x) (_ + _)
  rw [hweighted, hsmul]
  change inner ℂ (test x) _ = inner ℂ (test x) (_ + burnolFirstSourceMellinCoefficient coordinate.value source * _)
  rw [htail]
  apply congrArg (inner ℂ (test x))
  by_cases small : |x| < (1 / 4 : ℝ)
  · rw [if_pos small, if_neg (fun h => not_le_of_gt small h.1), zero_add, burnolFirstSourceRaw_abs]
    exact burnolFirstSource_rawInner coordinate.value source (abs_pos.mpr nonzero) small.le
  · rw [if_neg small, mul_zero, add_zero]
    by_cases outer : 4 ≤ |x|
    · rw [if_neg (fun h => not_lt_of_ge outer h.2), burnolFirstSourceRaw_outer coordinate source outer]
    · rw [if_pos ⟨le_of_not_gt small, lt_of_not_ge outer⟩, burnolFirstSourceRaw_abs]
      exact (burnolFirstSourceCoefficient_raw coordinate source ⟨le_of_not_gt small, (lt_of_not_ge outer).le⟩).symm

theorem burnolCompleteFirstSource_eq_weighted_add_unitTail (coordinate : BurnolCompletedMellinCoordinate) :
    let source := burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)
    burnolCompleteRemainderSource (coordinate.value / 2) source 1 =
      burnolWeightedReciprocalStepSource (1 / 4) 4 (burnolFirstSourceCoefficient coordinate source)
        (burnolFirstSourceCoefficientSlope coordinate source) + burnolNormalizedFirstSourceUnitTail coordinate := by
  dsimp only
  rw [burnolCompleteFirstSource_eq_weighted_add_tail]
  have unit : burnolFirstSourceMellinCoefficient coordinate.value
      (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) = 1 :=
    burnolCoordinateNormalizedAnnulusSource_mellin_normalization (1 - coordinate.value)
  rw [unit, one_smul]

theorem burnolAnalyticComplementFirstSource_eq_weighted {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    let source := burnolAnalyticComplementNormalizedSource observation
    burnolMobiusSourceL2 (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf) =
      burnolWeightedReciprocalStepSource (1 / 4) 4 (burnolFirstSourceCoefficient coordinate source)
        (burnolFirstSourceCoefficientSlope coordinate source) := by
  dsimp only
  apply add_right_cancel (b := burnolNormalizedFirstSourceUnitTail
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf))
  rw [← burnolAnalyticComplementFirstSource_split observation nontrivial rightHalf]
  exact burnolCompleteFirstSource_eq_weighted_add_unitTail
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
