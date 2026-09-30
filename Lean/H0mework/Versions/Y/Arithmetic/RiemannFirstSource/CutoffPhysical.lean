import H0mework.Versions.Y.Arithmetic.RiemannFirstSource.CutoffComplete
import H0mework.Versions.Y.Arithmetic.RiemannNativeCurrent.UnitResponseAction

/-! The original first Pa residual is the actual unit response's projection, through its generated finite source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolAnalyticComplementFirstPhysicalState_wave_add_response {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    let source := burnolAnalyticComplementNormalizedSource observation
    (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf : BurnolL2) =
      burnolWeightedReciprocalStepWave (1 / 4) 4 (burnolFirstSourceCoefficient coordinate source)
        (burnolFirstSourceCoefficientSlope coordinate source) + burnolUnitTailResponse coordinate 4 := by
  dsimp only
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf : BurnolL2)) test = _
  have rightQuarter : 1 / 4 < (observation.coordinate / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  have full := burnolCompleteRemainderSource_realizes (observation.coordinate / 2)
    rightQuarter (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (burnolAnalyticComplementNormalizedSource observation) 1 test
  have read : burnolRemainderSourceRead (burnolCompleteRemainderSource (observation.coordinate / 2)
      (burnolAnalyticComplementNormalizedSource observation) 1) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf : BurnolL2)) test := by
    simpa only [burnolAnalyticComplementFirstPhysicalState, burnolAnalyticComplementDivisionAdditiveState,
      burnolAnalyticComplementDivisionState, burnolAnalyticComplementCompletionSource] using full
  rw [← read, burnolAnalyticComplementFirstSource_split observation nontrivial rightHalf,
    burnolAnalyticComplementFirstSource_eq_weighted observation nontrivial rightHalf]
  rw [← burnolRemainderSourceReadCLM_apply, map_add, burnolRemainderSourceReadCLM_apply,
    burnolRemainderSourceReadCLM_apply, burnolOriginalUnitTail_realizes,
    burnolWeightedReciprocalStepSource_realizes (1 / 4) 4 _ _ (by norm_num) (by norm_num) (by norm_num)
      (burnolFirstSourceCoefficientSlope_continuous _ _).continuousOn]
  simp only [map_add, add_apply]
  rfl

theorem burnolFirstInternalValue_inPa {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolFirstInternalValue observation nontrivial rightHalf ∈ burnolOriginalPaInL2 := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let source := burnolAnalyticComplementNormalizedSource observation
  let state := burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf
  let projection := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection state
  have projected : (projection : BurnolL2) ∈ burnolOriginalPaInL2 :=
    Submodule.mem_map.mpr ⟨projection, Submodule.starProjection_apply_mem _ _, rfl⟩
  have same : burnolFirstInternalValue observation nontrivial rightHalf =
      burnolWeightedReciprocalStepWave (1 / 4) 4 (burnolFirstSourceCoefficient coordinate source)
        (burnolFirstSourceCoefficientSlope coordinate source) - (projection : BurnolL2) := by
    unfold burnolFirstInternalValue
    rw [Submodule.starProjection_orthogonal_val]
    change (state : BurnolL2) - (projection : BurnolL2) - _ = _
    rw [burnolAnalyticComplementFirstPhysicalState_wave_add_response observation nontrivial rightHalf]
    abel
  rw [same]
  exact burnolOriginalPaInL2.sub_mem (burnolFirstSourceWeightedWave_inPa coordinate source) projected

theorem burnolAnalyticComplementFirstPaResidual_eq_unitResponse_projection {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf) =
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolZeroOwnedUnitTailState observation nontrivial rightHalf) := by
  let state := burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf
  let response := burnolZeroOwnedUnitTailState observation nontrivial rightHalf
  have difference : state - response ∈ burnolCompactCoPoissonClosedRange.toSubmodule := by
    have same := burnolAnalyticComplementFirstPhysicalState_wave_add_response observation nontrivial rightHalf
    rcases Submodule.mem_map.mp (burnolFirstSourceWeightedWave_inPa
      (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
      (burnolAnalyticComplementNormalizedSource observation)) with ⟨wave, waveIn, waveRead⟩
    have values : state - response = wave := by
      apply Subtype.ext
      change (state : BurnolL2) - (response : BurnolL2) = (wave : BurnolL2)
      rw [same]
      rw [← waveRead]
      change (wave : BurnolL2) + burnolUnitTailResponse
        (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 4 -
        burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 4 = (wave : BurnolL2)
      abel
    rw [values]
    exact waveIn
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.starProjection_apply_eq_zero_iff _).mpr (by
    simpa only [Submodule.orthogonal_orthogonal] using difference)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
