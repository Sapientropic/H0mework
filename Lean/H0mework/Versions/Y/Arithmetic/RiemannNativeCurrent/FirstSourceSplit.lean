import H0mework.Versions.Y.Arithmetic.RemainderSource.Window
import H0mework.Versions.Y.Arithmetic.RiemannFirstSource.FirstPhysical

/-! The original first Pa class has one complete source: its own finite read plus the generated unit tail. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

local instance canonicalSource1AmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolAnalyticComplementFirstPhysicalState_source_cutoff {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolMobiusSourceL2 (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf) =
      burnolRadiusZeroExtension 4 (burnolRadiusRestriction 4
        (burnolCompleteRemainderSource (observation.coordinate / 2)
          (burnolAnalyticComplementNormalizedSource observation) 1)) := by
  apply burnolRemainderSourceRead_cutoff_source
  · exact burnolCompleteRemainderSource_even _ _ _
  · apply burnolCompleteRemainderSource_innerGap
    rw [Complex.div_re]
    norm_num
    linarith
  · intro test
    have rightQuarter : 1 / 4 < (observation.coordinate / 2).re := by
      rw [Complex.div_re]
      norm_num
      linarith
    have actual := burnolCompleteRemainderSource_realizes (observation.coordinate / 2)
      rightQuarter (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      (burnolAnalyticComplementNormalizedSource observation) 1 test
    simpa only [burnolAnalyticComplementFirstPhysicalState,
      burnolAnalyticComplementDivisionAdditiveState, burnolAnalyticComplementDivisionState,
      burnolAnalyticComplementCompletionSource, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_apply, smul_eq_mul] using actual

theorem burnolCompleteFirstSource_cutoff_add_unitTail (coordinate : BurnolCompletedMellinCoordinate) :
    burnolCompleteRemainderSource (coordinate.value / 2)
        (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) 1 =
      burnolRadiusZeroExtension 4 (burnolRadiusRestriction 4
        (burnolCompleteRemainderSource (coordinate.value / 2)
          (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) 1)) +
        burnolNormalizedFirstSourceUnitTail coordinate := by
  let source := burnolCompleteRemainderSource (coordinate.value / 2)
    (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) 1
  let inside := burnolRadiusZeroExtension 4 (burnolRadiusRestriction 4 source)
  have window := (ae_restrict_iff' (measurableSet_symmetricInterval (4 : ℝ))).mp
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (4 : ℝ)) source)
  apply Lp.ext
  filter_upwards [Lp.coeFn_add inside (burnolNormalizedFirstSourceUnitTail coordinate),
    burnolRadiusZeroExtension_coe (burnolRadiusRestriction 4 source), window,
    burnolNormalizedFirstSourceUnitTail_coeFn coordinate,
    burnolCompleteFirstSource_unitOuter coordinate] with x hadd hext hwindow htail hsource
  change source x = (inside + burnolNormalizedFirstSourceUnitTail coordinate : BurnolL2) x
  rw [hadd]
  change source x = inside x + burnolNormalizedFirstSourceUnitTail coordinate x
  have extension : inside x = (symmetricInterval (4 : ℝ)).indicator
      (fun t => burnolRadiusRestriction 4 source t) x := hext
  rw [extension, htail]
  unfold burnolNormalizedFirstSourceUnitTailRaw
  by_cases belongs : x ∈ symmetricInterval (4 : ℝ)
  · rw [indicator_of_mem belongs, if_neg (not_lt_of_ge (abs_le.mpr belongs))]
    have same : burnolRadiusRestriction 4 source x = source x := hwindow belongs
    rw [same, add_zero]
  · have outside : (4 : ℝ) < |x| := by
      apply lt_of_not_ge
      intro small
      exact belongs (abs_le.mp small)
    rw [indicator_of_notMem belongs, if_pos outside, zero_add]
    exact hsource outside

theorem burnolAnalyticComplementFirstSource_split {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolCompleteRemainderSource (observation.coordinate / 2)
        (burnolAnalyticComplementNormalizedSource observation) 1 =
      burnolMobiusSourceL2 (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf) +
        burnolNormalizedFirstSourceUnitTail
          (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) := by
  rw [burnolAnalyticComplementFirstPhysicalState_source_cutoff]
  exact burnolCompleteFirstSource_cutoff_add_unitTail
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)

theorem burnolAnalyticComplementFirstPaSource_split {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let value := burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf
    burnolCompleteRemainderSource (observation.coordinate / 2)
        (burnolAnalyticComplementNormalizedSource observation) 1 -
      burnolMobiusSourceL2 (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection value) =
      burnolMobiusSourceL2 (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection value) +
        burnolNormalizedFirstSourceUnitTail
          (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) := by
  dsimp only
  rw [burnolAnalyticComplementFirstSource_split observation nontrivial rightHalf,
    Submodule.starProjection_orthogonal_val, map_sub]
  abel

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
