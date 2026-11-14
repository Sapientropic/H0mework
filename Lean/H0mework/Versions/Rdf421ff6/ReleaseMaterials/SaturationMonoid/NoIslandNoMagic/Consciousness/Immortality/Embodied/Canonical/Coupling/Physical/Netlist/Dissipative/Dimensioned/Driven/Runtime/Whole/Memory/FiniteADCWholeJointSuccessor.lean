import H0mework.Physics.ADCRuntime.WholeJointReadout

/-! # The recipient and every receiver capacitor jointly generate a reusable current -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {bootInitial : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (current : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology)
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

def emittedNext : Option (Option (FiniteADCPhysicalRuntimeCurrent hardware)) :=
  receiverWholeDrivenPhysicalNext? (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
    (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology current.memory.inputInitial
    current.memory.gateInitial downstreamTechnology downstreamGraph current.plant current.fits

theorem emittedNext_generated :
    current.emittedNext downstreamTechnology downstreamGraph =
      some (some (finiteADCPhysicalDelayedSuccessor
        (receiverWholeHardwareProcessingTicks hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
          technology downstreamTechnology downstreamGraph) current.plant)) :=
  receiverWholeDrivenPhysicalNext_generated (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
    (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology current.memory.inputInitial
    (fun node atom registered => current.memory.inputInitial_in_rail atom node registered)
    current.memory.gateInitial current.memory.gateInitial_in_rail
    downstreamTechnology downstreamGraph current.plant current.fits current.inSchedule

/-- Extraction consumes the actual emitted value; the erased proof only rules out absent output. -/
def nextPlant : FiniteADCPhysicalRuntimeCurrent hardware :=
  (current.emittedNext downstreamTechnology downstreamGraph).join.get (by
    rw [current.emittedNext_generated downstreamTechnology downstreamGraph]
    rfl)

theorem nextPlant_eq_delayed :
    current.nextPlant downstreamTechnology downstreamGraph =
      finiteADCPhysicalDelayedSuccessor
        (receiverWholeHardwareProcessingTicks hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
          technology downstreamTechnology downstreamGraph) current.plant := by
  simp only [nextPlant, emittedNext_generated, Option.join_some, Option.get_some]

/-- Old packet controls remain installed while the new recipient reaches its own next snapshot. -/
def memoryEndpointTime : ℝ :=
  (readDelay (hardware := hardware) (clockMax := finiteADCPhysicalRuntimeMaxTick hardware bootInitial) (technology := technology)
    downstreamTechnology downstreamGraph).value +
      (current.nextPlant downstreamTechnology downstreamGraph).val.executedDuration.value

theorem memoryEndpointTime_nonneg :
    0 ≤ current.memoryEndpointTime downstreamTechnology downstreamGraph := by
  have duration := finiteADCPhysicalCurrent_duration_ge_tick (current.nextPlant downstreamTechnology downstreamGraph)
  have tick := finiteSamplingClockTickPeriod_pos hardware.meteredSource.fixture.coreSource hardware.clockCode
  exact add_nonneg (readDelay_nonneg downstreamTechnology downstreamGraph) (tick.le.trans duration)

def nextMemory : AIGCapacitorMemory technology (aigOutputBank
    (receiverWholeGraph hardware.adcCode (finiteADCPhysicalRuntimeClockBits hardware bootInitial))).aig :=
  aigMemoryEndpoint technology
    (receiverWholeGraph hardware.adcCode (finiteADCPhysicalRuntimeClockBits hardware bootInitial))
    current.memory current.assignment downstreamTechnology downstreamGraph
    hardware.meteredSource.fixture.coreSource hardware.clockCode
    (current.memoryEndpointTime downstreamTechnology downstreamGraph)
    (current.memoryEndpointTime_nonneg downstreamTechnology downstreamGraph)

theorem nextPlant_in_schedule :
    (current.nextPlant downstreamTechnology downstreamGraph).val.sampleTick ≤
      finiteADCPhysicalRuntimeMaxTick hardware bootInitial := by
  rw [current.nextPlant_eq_delayed downstreamTechnology downstreamGraph]
  exact (finiteADCPhysicalDelayedSuccessor_sampleTick_le current.plant _).trans (le_max_right _ _)

def step : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology where
  plant := current.nextPlant downstreamTechnology downstreamGraph
  inSchedule := current.nextPlant_in_schedule downstreamTechnology downstreamGraph
  memory := current.nextMemory downstreamTechnology downstreamGraph

theorem step_plant :
    (current.step downstreamTechnology downstreamGraph).plant =
      finiteADCPhysicalDelayedSuccessor
        (receiverWholeHardwareProcessingTicks hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
          technology downstreamTechnology downstreamGraph) current.plant :=
  current.nextPlant_eq_delayed downstreamTechnology downstreamGraph

theorem step_plant_no_reset :
    finiteADCPhysicalStateAt (current.step downstreamTechnology downstreamGraph).plant 0 =
      finiteADCPhysicalStateAt current.plant (finiteADCPhysicalSwitchTimeAt current.plant
        (receiverWholeHardwareProcessingTicks hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
          technology downstreamTechnology downstreamGraph)) := by
  rw [current.step_plant downstreamTechnology downstreamGraph]
  exact finiteADCPhysicalDelayedSuccessor_no_reset _ current.plant

theorem step_reopens_receiver :
    (current.step downstreamTechnology downstreamGraph).physicalRead downstreamTechnology downstreamGraph =
      some (some (current.step downstreamTechnology downstreamGraph).plant.val.drive) :=
  (current.step downstreamTechnology downstreamGraph).physicalRead_received downstreamTechnology downstreamGraph

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
