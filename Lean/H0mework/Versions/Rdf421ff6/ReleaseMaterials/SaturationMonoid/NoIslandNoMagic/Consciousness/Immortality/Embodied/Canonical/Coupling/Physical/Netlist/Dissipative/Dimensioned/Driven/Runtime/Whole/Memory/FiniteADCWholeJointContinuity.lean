import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Runtime.Whole.Memory.FiniteADCWholeJointSuccessor
import H0mework.Computation.AIGHold.AIGMemoryRestart

/-! # The read, the stored capacitor endpoints and the next physical cycle are one occurrence -/

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

theorem step_receiver_memory_no_reset
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      (finiteADCPhysicalRuntimeClockBits hardware bootInitial))).aig.decls.size) (polarity : Bool) :
    (current.step downstreamTechnology downstreamGraph).receiverStateAt downstreamTechnology downstreamGraph node polarity 0 =
      current.receiverStateAt downstreamTechnology downstreamGraph node polarity
        (current.memoryEndpointTime downstreamTechnology downstreamGraph) := by
  exact aigMemoryStateAt_restart technology
    (receiverWholeGraph hardware.adcCode (finiteADCPhysicalRuntimeClockBits hardware bootInitial))
    current.memory current.assignment (current.step downstreamTechnology downstreamGraph).assignment
    downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode
    (current.memoryEndpointTime downstreamTechnology downstreamGraph)
    (current.memoryEndpointTime_nonneg downstreamTechnology downstreamGraph) node polarity

/-- The wait for the next ADC snapshot is part of the old capacitor history, not a free pause. -/
theorem step_memory_joins_next_snapshot :
    current.memoryEndpointTime downstreamTechnology downstreamGraph =
      (readDelay (hardware := hardware) (clockMax := finiteADCPhysicalRuntimeMaxTick hardware bootInitial) (technology := technology)
        downstreamTechnology downstreamGraph).value +
          (current.step downstreamTechnology downstreamGraph).plant.val.executedDuration.value := rfl

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
