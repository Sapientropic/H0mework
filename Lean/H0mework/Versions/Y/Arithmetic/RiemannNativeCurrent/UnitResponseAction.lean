import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.UnitResponseOccupation

/-! The original unit response and internal value generate the full native current on the original L² carrier. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolUnitTailResponse_dilation (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (admitted : (4 * Real.exp (shift / 2))⁻¹ ≤ 4) :
    burnolMultiplicativeDilation (-shift / 2) (burnolUnitTailResponse coordinate 4) =
      positiveMellinQuarterRightResolventCharacter (coordinate.value / 2) shift •
        burnolUnitTailResponse coordinate (4 * Real.exp (shift / 2)) := by
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    (burnolMultiplicativeDilation (-shift / 2) (burnolUnitTailResponse coordinate 4))) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (positiveMellinQuarterRightResolventCharacter (coordinate.value / 2) shift •
          burnolUnitTailResponse coordinate (4 * Real.exp (shift / 2)))) test
  have read := burnolRemainderRealization_dilation (burnolNormalizedFirstSourceUnitTail coordinate)
    (burnolUnitTailResponse coordinate 4) (burnolOriginalUnitTail_realizes coordinate) (-shift / 2) test
  rw [burnolNormalizedFirstSourceUnitTail_dilation,
    ← burnolRemainderSourceReadCLM_apply, map_smul, burnolRemainderSourceReadCLM_apply,
    burnolUnitTailResponse_realizes coordinate _ (by positivity) admitted] at read
  exact read.symm.trans (by simp only [map_smul, smul_apply])

theorem burnolUnitTailResponse_shell (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ)
    (aboveQuarter : (1 / 4 : ℝ) < radius) (belowFour : radius < 4) :
    burnolUnitTailResponse coordinate radius - burnolUnitTailResponse coordinate 4 = burnolUnitPowerShellWave coordinate radius := by
  have positive : 0 < radius := lt_trans (by norm_num) aboveQuarter
  have bounded : radius⁻¹ ≤ 4 := by
    simpa only [one_div, inv_inv] using
      (inv_le_inv₀ positive (by norm_num : (0 : ℝ) < 1 / 4)).mpr aboveQuarter.le
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    (burnolUnitTailResponse coordinate radius - burnolUnitTailResponse coordinate 4)) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolUnitPowerShellWave coordinate radius)) test
  have read := burnolActualUnitPowerShell_realizes coordinate radius aboveQuarter belowFour test
  rw [← burnolRemainderSourceReadCLM_apply, map_sub,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    burnolUnitTailResponse_realizes coordinate radius positive bounded, burnolOriginalUnitTail_realizes] at read
  simpa only [map_sub, sub_apply] using read

theorem burnolFirstInternalValue_nativeCurrent {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ)
    (aboveQuarter : (1 / 4 : ℝ) < 4 * Real.exp (shift / 2))
    (belowFour : 4 * Real.exp (shift / 2) < 4) :
    let residue := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf)
    let character := positiveMellinQuarterRightResolventCharacter (observation.coordinate / 2) shift
    burnolMultiplicativeDilation (-shift / 2) (residue : BurnolL2) - character • (residue : BurnolL2) =
      (burnolMultiplicativeDilation (-shift / 2) (burnolFirstInternalValue observation nontrivial rightHalf) -
        character • burnolFirstInternalValue observation nontrivial rightHalf) +
      character • burnolUnitPowerShellWave (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
        (4 * Real.exp (shift / 2)) := by
  dsimp only
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  have admitted : (4 * Real.exp (shift / 2))⁻¹ ≤ 4 := by
    simpa only [one_div, inv_inv] using (inv_le_inv₀ (by positivity : (0 : ℝ) < 4 * Real.exp (shift / 2))
      (by norm_num : (0 : ℝ) < 1 / 4)).mpr aboveQuarter.le
  have action := burnolUnitTailResponse_dilation coordinate shift admitted
  have shell := burnolUnitTailResponse_shell coordinate _ aboveQuarter belowFour
  have sameCharacter : positiveMellinQuarterRightResolventCharacter (coordinate.value / 2) shift =
      positiveMellinQuarterRightResolventCharacter (observation.coordinate / 2) shift := rfl
  rw [sameCharacter] at action
  unfold burnolFirstInternalValue
  rw [map_sub, smul_sub, action, ← shell, smul_sub]
  abel

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
