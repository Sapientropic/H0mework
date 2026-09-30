import H0mework.Physics.ADCRuntime.LoadedLoadedRechargeEnergy
import H0mework.Physics.ADCRuntime.LoadedLoadedWaitingEnergy

/-! # All four actual phases pay one generated loaded step -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
  {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {technology : AIGCellTechnology} {actualBoot : FiniteDimensionedSeriesRLCPortState}
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def loadedStepWork : SIJoule :=
  readPhaseWork downstreamTechnology downstreamGraph current +
  outputLoadBackgroundWorkAt downstreamTechnology downstreamGraph current
    (commonOutputLoadDuration (hardware := hardware)
      (clockMax := loadedReceiverInstalledMaxTick hardware technology actualBoot) (technology := technology)
      downstreamTechnology downstreamGraph).value +
  receiverRechargeWorkAt downstreamTechnology downstreamGraph current
    (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value +
  waitingPhaseWork downstreamTechnology downstreamGraph current

def loadedStepHeat : SIJoule :=
  readPhaseHeat downstreamTechnology downstreamGraph current +
  outputLoadWholeHeatAt downstreamTechnology downstreamGraph current
    (commonOutputLoadDuration (hardware := hardware)
      (clockMax := loadedReceiverInstalledMaxTick hardware technology actualBoot) (technology := technology)
      downstreamTechnology downstreamGraph).value +
  rechargePhaseHeat downstreamTechnology downstreamGraph current +
  waitingPhaseHeat downstreamTechnology downstreamGraph current

theorem loadedStepHeat_nonneg :
    0 ≤ (loadedStepHeat downstreamTechnology downstreamGraph current).value :=
  add_nonneg (add_nonneg (add_nonneg
      (readPhaseHeat_nonneg downstreamTechnology downstreamGraph current)
      (outputLoadWholeHeatAt_nonneg downstreamTechnology downstreamGraph current _
        (commonOutputLoadDuration_pos downstreamTechnology downstreamGraph).le))
    (rechargePhaseHeat_nonneg downstreamTechnology downstreamGraph current))
    (waitingPhaseHeat_nonneg downstreamTechnology downstreamGraph current)

/-- Each intermediate energy disappears only through a literal state/clock join.
The independent source-power and heat integrals themselves remain in the bill. -/
theorem loadedStep_energy_balance :
    (jointStoredEnergy (loadedStep downstreamTechnology downstreamGraph current)).value -
        (jointStoredEnergy current).value =
      (loadedStepWork downstreamTechnology downstreamGraph current).value -
        (loadedStepHeat downstreamTechnology downstreamGraph current).value := by
  have read := readPhase_integrated_balance downstreamTechnology downstreamGraph current
  have connected := outputLoadWholeStoredEnergyAt_integrated_balance downstreamTechnology downstreamGraph current
    (commonOutputLoadDuration (hardware := hardware)
      (clockMax := loadedReceiverInstalledMaxTick hardware technology actualBoot) (technology := technology)
      downstreamTechnology downstreamGraph).value
  have recovery := rechargePhase_integrated_balance downstreamTechnology downstreamGraph current
  have waiting := waitingPhase_integrated_balance downstreamTechnology downstreamGraph current
  change _ - (recoveredJointStoredEnergy downstreamTechnology downstreamGraph current).value = _ at waiting
  dsimp only [loadedStepWork, loadedStepHeat, SIQuantity.add_value]
  linarith

theorem loadedStep_no_unpaid_storage_increase :
    (jointStoredEnergy (loadedStep downstreamTechnology downstreamGraph current)).value -
        (jointStoredEnergy current).value ≤
      (loadedStepWork downstreamTechnology downstreamGraph current).value := by
  rw [loadedStep_energy_balance]
  exact sub_le_self _ (loadedStepHeat_nonneg downstreamTechnology downstreamGraph current)

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
