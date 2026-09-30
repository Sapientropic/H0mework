import H0mework.Computation.LoadedADCPacket.Source

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

def headerSeconds (code : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) : ℝ :=
  ((unpackADCWirePacket hardware code).sampleTick : ℝ) *
    (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource hardware.clockCode).value

def headerDecoder (code : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) : ℂ :=
  headerSeconds code

theorem packet_duration
    (current : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    current.plant.val.executedDuration.value = headerSeconds current.packet := by
  have actual := (finiteADCPhysicalCurrent_generates_receipt current.plant).executedDurationIsClockTick
  unfold finiteADCPhysicalCurrentSource at actual
  rw [← current.plant.property] at actual
  have values := congrArg (fun time : SISecond => time.value) actual
  change current.plant.val.executedDuration.value =
    (current.plant.val.sampleTick : ℝ) * current.plant.val.clockTick.value at values
  have clock := congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.clockTick current.plant.property
  change current.plant.val.clockTick =
    finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource hardware.clockCode at clock
  rw [clock] at values
  exact values.trans (congrArg (fun count : Nat => (count : ℝ) *
    (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource hardware.clockCode).value)
      (unpack_header current)).symm

variable {β : Type} [DecidableEq β] [Hashable β]
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def sampleTask (bound : Nat) (actor : Fin (bound + 1)) : ℂ :=
  (loadedStep downstreamTechnology downstreamGraph
    (loadedAfter downstreamTechnology downstreamGraph seed actor.val)).plant.val.executedDuration.value

theorem sampleTask_eq_decode_next (bound : Nat) (actor : Fin (bound + 1)) :
    sampleTask downstreamTechnology downstreamGraph seed bound actor =
      headerDecoder (nextPacket downstreamTechnology downstreamGraph seed bound actor) :=
  congrArg Complex.ofReal (packet_duration
    (loadedStep downstreamTechnology downstreamGraph (loadedAfter downstreamTechnology downstreamGraph seed actor.val)))

theorem four_phase_duration_from_packet
    (current : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    (loadedStepDuration downstreamTechnology downstreamGraph current).value =
      (readDelay (hardware := hardware)
        (clockMax := loadedReceiverInstalledMaxTick hardware technology actualBoot) (technology := technology)
        downstreamTechnology downstreamGraph).value +
      (commonOutputLoadDuration (hardware := hardware)
        (clockMax := loadedReceiverInstalledMaxTick hardware technology actualBoot) (technology := technology)
        downstreamTechnology downstreamGraph).value +
      (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value +
      headerSeconds (loadedReceiverFreshPacket downstreamTechnology downstreamGraph current actualBoot) := by
  rw [loadedStepDuration_four_phases]
  have restored := packet_duration (loadedStep downstreamTechnology downstreamGraph current)
  rw [loadedStep_plant, loadedStep_packet] at restored
  rw [restored]

end
end FiniteADCWholeJointCurrent.Information.Packet
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
