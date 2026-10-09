import H0mework.Versions.V2.Arithmetic.RiemannUnitRegularity.UnitResponsePhysical

/-! The actual unit response is nonzero; its finite source read vanishes without deleting the full source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolOriginalUnitTail_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (burnolNormalizedFirstSourceUnitTail coordinate) = burnolNormalizedFirstSourceUnitTail coordinate := by
  unfold burnolNormalizedFirstSourceUnitTail
  dsimp only
  rw [map_neg, map_add, reflectL2_reflectL2]
  abel

theorem burnolOriginalUnitTail_window_zero (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ)
    (bounded : radius ≤ 4) : (burnolNormalizedFirstSourceUnitTail coordinate : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval radius)] fun _ => 0 := by
  filter_upwards [ae_restrict_of_ae (burnolNormalizedFirstSourceUnitTail_coeFn coordinate),
    ae_restrict_mem (measurableSet_symmetricInterval radius)] with x actual inside
  rw [actual]
  exact if_neg (not_lt.mpr ((abs_le.mpr inside).trans bounded))

theorem burnolOriginalUnitTail_nonzero (coordinate : BurnolCompletedMellinCoordinate) :
    burnolNormalizedFirstSourceUnitTail coordinate ≠ 0 := by
  intro zero
  have actual := burnolNormalizedFirstSourceUnitTail_current_ne_zero coordinate 1 (by norm_num)
  rw [zero, map_zero, smul_zero, sub_zero] at actual
  exact actual rfl

theorem burnolUnitTailResponse_nonzero (coordinate : BurnolCompletedMellinCoordinate) :
    burnolUnitTailResponse coordinate 4 ≠ 0 := by
  intro zero
  apply burnolOriginalUnitTail_nonzero coordinate
  apply burnolRemainderSourceRead_faithful
  · exact burnolOriginalUnitTail_even coordinate
  · exact burnolOriginalUnitTail_window_zero coordinate (1 / 4) (by norm_num)
  · intro test
    rw [burnolOriginalUnitTail_realizes, zero, map_zero]
    rfl

def burnolZeroOwnedUnitTailState {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) : BurnolPaAmbientCarrier :=
  ⟨burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 4,
    burnolZeroOwnedUnitTailResponse_physical observation nontrivial rightHalf⟩

theorem burnolZeroOwnedUnitTailState_finiteSource_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolMobiusSourceL2 (burnolZeroOwnedUnitTailState observation nontrivial rightHalf) = 0 := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  have read := burnolRemainderSourceRead_cutoff_source (burnolNormalizedFirstSourceUnitTail coordinate)
    (burnolZeroOwnedUnitTailState observation nontrivial rightHalf) (burnolOriginalUnitTail_even coordinate)
    (burnolOriginalUnitTail_window_zero coordinate (1 / 4) (by norm_num)) (fun test => by
      simpa only [burnolZeroOwnedUnitTailState, coordinate, Lp.toTemperedDistributionCLM_apply,
        Lp.toTemperedDistribution_apply, smul_eq_mul] using burnolOriginalUnitTail_realizes coordinate test)
  have restrictionZero : burnolRadiusRestriction 4 (burnolNormalizedFirstSourceUnitTail coordinate) = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (4 : ℝ))
      (burnolNormalizedFirstSourceUnitTail coordinate), burnolOriginalUnitTail_window_zero coordinate 4 le_rfl]
        with x restrictionAt zeroAt
    exact restrictionAt.trans zeroAt
  rw [restrictionZero, map_zero] at read
  exact read

theorem burnolZeroOwnedUnitTailState_notInPa {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolZeroOwnedUnitTailState observation nontrivial rightHalf ∉ burnolCompactCoPoissonClosedRange := by
  intro belongs
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  apply burnolOriginalUnitTail_nonzero coordinate
  apply burnolRemainderSourceRead_faithful
  · exact burnolOriginalUnitTail_even coordinate
  · exact burnolOriginalUnitTail_window_zero coordinate (1 / 4) (by norm_num)
  · intro test
    have read := burnolRemainderSourceRead_Pa (burnolZeroOwnedUnitTailState observation nontrivial rightHalf) belongs test
    rw [burnolZeroOwnedUnitTailState_finiteSource_zero,
      ← burnolRemainderSourceReadCLM_apply, map_zero] at read
    rw [burnolOriginalUnitTail_realizes]
    simpa only [coordinate, burnolZeroOwnedUnitTailState, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_apply, smul_eq_mul] using read.symm

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
