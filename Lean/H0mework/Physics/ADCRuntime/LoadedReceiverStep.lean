import H0mework.Physics.ADCRuntime.LoadedReceiverSnapshotMemory
import H0mework.Physics.ADCRuntime.LoadedInstalledClock

/-! # A source-installed loaded step closes on the existing complete current carrier -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

def startLoadedReceiverCurrent (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (technology : AIGCellTechnology) (actualBoot : FiniteDimensionedSeriesRLCPortState)
    (memory : AIGCapacitorMemory technology (aigOutputBank
      (receiverWholeGraph hardware.adcCode (loadedReceiverInstalledClockBits hardware technology actualBoot))).aig)
    (drive : FiniteBinaryDrive) :
    FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology where
  plant := startFiniteADCPhysicalRuntime hardware actualBoot drive
  inSchedule := loadedReceiverBoot_sampleTick_le_installed hardware technology actualBoot drive
  memory := memory

def compileLoadedReceiverBoot (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (technology : AIGCellTechnology) (actualBoot : FiniteDimensionedSeriesRLCPortState) (drive : FiniteBinaryDrive) :
    FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology :=
  startLoadedReceiverCurrent hardware technology actualBoot
    (AIGCapacitorMemory.zero technology (aigOutputBank
      (receiverWholeGraph hardware.adcCode (loadedReceiverInstalledClockBits hardware technology actualBoot))).aig) drive

namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {technology : AIGCellTechnology} {actualBoot : FiniteDimensionedSeriesRLCPortState}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def loadedStep : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology where
  plant := loadedReceiverFreshSample downstreamTechnology downstreamGraph current
  inSchedule := loadedReceiverFreshSample_sampleTick_le_installed downstreamTechnology downstreamGraph current actualBoot
  memory := loadedReceiverSnapshotMemory downstreamTechnology downstreamGraph current

theorem loadedStep_plant :
    (loadedStep downstreamTechnology downstreamGraph current).plant =
      loadedReceiverFreshSample downstreamTechnology downstreamGraph current := rfl

theorem loadedStep_memory :
    (loadedStep downstreamTechnology downstreamGraph current).memory =
      loadedReceiverSnapshotMemory downstreamTechnology downstreamGraph current := rfl

theorem loadedStep_packet :
    (loadedStep downstreamTechnology downstreamGraph current).packet =
      loadedReceiverFreshPacket downstreamTechnology downstreamGraph current actualBoot := rfl

theorem loadedStep_receives_own_recorded_sample :
    (loadedStep downstreamTechnology downstreamGraph current).physicalRead downstreamTechnology downstreamGraph =
      some (some (loadedStep downstreamTechnology downstreamGraph current).plant.val.drive) :=
  physicalRead_received _ _ _

theorem loadedStep_no_recipient_reset :
    finiteADCPhysicalStateAt (loadedStep downstreamTechnology downstreamGraph current).plant 0 =
      (commonRecoveryTarget downstreamTechnology downstreamGraph current).2 :=
  loadedReceiverFreshSample_no_reset _ _ _

theorem loadedStep_no_memory_reset
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      (loadedReceiverInstalledClockBits hardware technology actualBoot))).aig.decls.size) (polarity : Bool) :
    (loadedStep downstreamTechnology downstreamGraph current).receiverStateAt downstreamTechnology downstreamGraph node polarity 0 =
      loadedReceiverAwaitingStateAt downstreamTechnology downstreamGraph current node polarity
        (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value :=
  loadedReceiverSnapshotMemory_restarts_without_reset _ _ _ _ _ _

theorem loadedStep_feedback :
    (loadedStep downstreamTechnology downstreamGraph current).plant.val.drive =
      fun channel => !(current.plant.val.drive channel) :=
  loadedReceiverFreshSample_feedback _ _ _

theorem loadedStep_changes_current :
    loadedStep downstreamTechnology downstreamGraph current ≠ current := by
  intro unchanged
  have plant := congrArg (fun state : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology => state.plant) unchanged
  exact loadedReceiverFreshSample_is_not_read_only downstreamTechnology downstreamGraph current plant

/-- Every switched phase contributes to the physical gap between the two actual ADC snapshots. -/
def loadedStepDuration : SISecond :=
  ⟨(commonOutputRecoveryStart (hardware := hardware)
      (clockMax := loadedReceiverInstalledMaxTick hardware technology actualBoot) (technology := technology)
      downstreamTechnology downstreamGraph).value +
    (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value +
    (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value⟩

theorem loadedStepDuration_ge_tick :
    (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource hardware.clockCode).value ≤
      (loadedStepDuration downstreamTechnology downstreamGraph current).value := by
  have startNonnegative := commonOutputRecoveryStart_nonnegative (hardware := hardware)
    (clockMax := loadedReceiverInstalledMaxTick hardware technology actualBoot) (technology := technology)
    downstreamTechnology downstreamGraph
  have recovery := commonRecoverySampleTime_nonnegative downstreamTechnology downstreamGraph current
  have sample := finiteADCPhysicalCurrent_duration_ge_tick (loadedReceiverFreshSample downstreamTechnology downstreamGraph current)
  change _ ≤ (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value at sample
  change _ ≤ _ + _ + _
  linarith

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
