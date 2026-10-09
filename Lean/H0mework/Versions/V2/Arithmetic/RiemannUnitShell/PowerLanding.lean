import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.PowerSource

/-! The actual unit shell generates a Pa correction for the original first native source current. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolUnitPowerShellWave (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) : BurnolL2 :=
  burnolWeightedReciprocalStepWave (1 / 4) radius⁻¹ (burnolUnitPowerWeight coordinate) (burnolUnitPowerSlope coordinate)

theorem burnolUnitPowerShellWave_originalPa (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (aboveQuarter : (1 / 4 : ℝ) < radius) (belowFour : radius < 4) :
    burnolUnitPowerShellWave coordinate radius ∈ burnolOriginalPaInL2 := by
  have positive : 0 < radius := lt_trans (by norm_num) aboveQuarter
  apply burnolWeightedReciprocalStepWave_inPa (1 / 4) radius⁻¹ _ _ (by norm_num) _
    (burnolUnitPowerSlope_continuous coordinate).continuousOn
  constructor
  · rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) positive]
    exact belowFour.le
  · rw [show (4 : ℝ) = (1 / 4 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ positive (by norm_num : (0 : ℝ) < 1 / 4)]
    exact aboveQuarter.le

theorem burnolActualUnitPowerShell_realizes (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (aboveQuarter : (1 / 4 : ℝ) < radius) (belowFour : radius < 4)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead
      (burnolRadiusNormalizedUnitTail coordinate radius (lt_trans (by norm_num) aboveQuarter) -
        burnolNormalizedFirstSourceUnitTail coordinate) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolUnitPowerShellWave coordinate radius)) test := by
  rw [← burnolUnitPowerStep_source_eq_actualShell coordinate radius _ belowFour]
  apply burnolWeightedReciprocalStepSource_realizes (1 / 4) radius⁻¹ _ _ (by norm_num) _ _
    (burnolUnitPowerSlope_continuous coordinate).continuousOn
  · rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) (lt_trans (by norm_num) aboveQuarter)]
    exact belowFour.le
  · rw [show (4 : ℝ) = (1 / 4 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ (lt_trans (by norm_num) aboveQuarter) (by norm_num : (0 : ℝ) < 1 / 4)]
    exact aboveQuarter.le

def burnolActualUnitPowerShellPaState (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (aboveQuarter : (1 / 4 : ℝ) < radius) (belowFour : radius < 4) : BurnolPaAmbientCarrier :=
  ⟨burnolUnitPowerShellWave coordinate radius, by
    rcases Submodule.mem_map.mp (burnolUnitPowerShellWave_originalPa coordinate radius aboveQuarter belowFour) with
      ⟨value, _, same⟩
    rw [← same]
    exact value.property⟩

theorem burnolActualUnitPowerShellPaState_mem (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (aboveQuarter : (1 / 4 : ℝ) < radius) (belowFour : radius < 4) :
    burnolActualUnitPowerShellPaState coordinate radius aboveQuarter belowFour ∈ burnolCompactCoPoissonClosedRange := by
  rcases Submodule.mem_map.mp (burnolUnitPowerShellWave_originalPa coordinate radius aboveQuarter belowFour) with
    ⟨value, belongs, same⟩
  have exactState : value = burnolActualUnitPowerShellPaState coordinate radius aboveQuarter belowFour :=
    Subtype.ext same
  exact exactState ▸ belongs

theorem burnolOriginalFirstCurrent_generatedPaCorrection {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ)
    (aboveQuarter : (1 / 4 : ℝ) < 4 * Real.exp (shift / 2))
    (belowFour : 4 * Real.exp (shift / 2) < 4) :
    let value := burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf
    let character := positiveMellinQuarterRightResolventCharacter (observation.coordinate / 2) shift
    let internal := burnolMobiusSourceL2 (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection value)
    let source := burnolCompleteRemainderSource (observation.coordinate / 2)
        (burnolAnalyticComplementNormalizedSource observation) 1 -
      burnolMobiusSourceL2 (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection value)
    ∃ correction : BurnolPaAmbientCarrier, correction ∈ burnolCompactCoPoissonClosedRange ∧
      ∀ test : SchwartzMap ℝ ℂ,
        burnolRemainderSourceRead (burnolMultiplicativeDilation (-shift / 2) source - character • source) test =
          burnolRemainderSourceRead (burnolMultiplicativeDilation (-shift / 2) internal - character • internal) test +
            (Lp.toTemperedDistributionCLM ℂ volume 2 (correction : BurnolL2)) test := by
  dsimp only
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let character := positiveMellinQuarterRightResolventCharacter (observation.coordinate / 2) shift
  let shell := burnolActualUnitPowerShellPaState coordinate (4 * Real.exp (shift / 2)) aboveQuarter belowFour
  refine ⟨character • shell, burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem character
    (burnolActualUnitPowerShellPaState_mem coordinate _ aboveQuarter belowFour), ?_⟩
  intro test
  rw [burnolAnalyticComplementFirstPaSource_current observation nontrivial rightHalf shift]
  rw [← burnolRemainderSourceReadCLM_apply, map_add, map_smul,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    burnolActualUnitPowerShell_realizes coordinate _ aboveQuarter belowFour]
  change _ = _ + (Lp.toTemperedDistributionCLM ℂ volume 2
    (character • burnolUnitPowerShellWave coordinate (4 * Real.exp (shift / 2)))) test
  simp only [map_smul, smul_apply, smul_eq_mul]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
