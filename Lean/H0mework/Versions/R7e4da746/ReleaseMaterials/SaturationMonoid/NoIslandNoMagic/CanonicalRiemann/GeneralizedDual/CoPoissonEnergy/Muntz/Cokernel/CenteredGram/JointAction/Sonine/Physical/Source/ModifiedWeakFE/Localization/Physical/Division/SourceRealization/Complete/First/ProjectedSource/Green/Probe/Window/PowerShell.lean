import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitShell.PowerLanding
import H0mework.Versions.R7e4da746.Arithmetic.RiemannWholeWard.SecondWindow

/-! The already generated closed-endpoint step source realizes the full second-window power shell. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem fullPowerShell_inPa (coordinate : BurnolCompletedMellinCoordinate) :
    burnolUnitPowerShellWave coordinate (1 / 4) ∈ burnolOriginalPaInL2 := by
  unfold burnolUnitPowerShellWave
  apply burnolWeightedReciprocalStepWave_inPa
  · norm_num
  · norm_num
  · exact (burnolUnitPowerSlope_continuous coordinate).continuousOn

def fullPowerShellState (coordinate : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  ⟨burnolUnitPowerShellWave coordinate (1 / 4), by
    rcases Submodule.mem_map.mp (fullPowerShell_inPa coordinate) with ⟨value, _, same⟩
    rw [← same]
    exact value.property⟩

theorem fullPowerShellState_mem (coordinate : BurnolCompletedMellinCoordinate) :
    fullPowerShellState coordinate ∈ burnolCompactCoPoissonClosedRange := by
  rcases Submodule.mem_map.mp (fullPowerShell_inPa coordinate) with ⟨value, belongs, same⟩
  have exactState : value = fullPowerShellState coordinate := Subtype.ext same
  exact exactState ▸ belongs

theorem fullPowerShell_realizes (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead
      (burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num) -
        burnolNormalizedFirstSourceUnitTail coordinate) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (fullPowerShellState coordinate : BurnolL2)) test := by
  rw [← burnolUnitPowerStep_source_eq_actualShell coordinate (1 / 4) (by norm_num) (by norm_num)]
  exact burnolWeightedReciprocalStepSource_realizes (1 / 4) (1 / 4)⁻¹
    (burnolUnitPowerWeight coordinate) (burnolUnitPowerSlope coordinate)
    (by norm_num) (by norm_num) (by norm_num)
    (burnolUnitPowerSlope_continuous coordinate).continuousOn test

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
