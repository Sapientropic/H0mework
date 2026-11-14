import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Runtime.Whole.Memory.FiniteADCWholeJointContinuation

/-! # Read-only or replacement-memory endpoints cannot be the actual joint step -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Regression

open Std.Sat Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Producer
open Netlist.Dissipative.Dimensioned.Driven.Interface

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {bootInitial : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (current : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology)
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

theorem wholeJoint_step_is_not_read_only :
    current.step downstreamTechnology downstreamGraph ≠ current := by
  intro same
  have drive := congrArg (fun state : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology =>
    state.plant.val.drive) same
  rw [current.step_plant downstreamTechnology downstreamGraph,
    finiteADCPhysicalDelayedSuccessor_feedback_exact] at drive
  have point := congrFun drive .noPowerMinting
  cases actual : current.plant.val.drive .noPowerMinting <;> simp [actual] at point

theorem wholeJoint_replacement_memory_rejected
    (replacement : AIGCapacitorMemory technology (aigOutputBank
      (receiverWholeGraph hardware.adcCode (finiteADCPhysicalRuntimeClockBits hardware bootInitial))).aig)
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      (finiteADCPhysicalRuntimeClockBits hardware bootInitial))).aig.decls.size) (polarity : Bool)
    (different : replacement.gateInitial node polarity ≠
      current.receiverStateAt downstreamTechnology downstreamGraph node polarity
        (current.memoryEndpointTime downstreamTechnology downstreamGraph)) :
    (current.step downstreamTechnology downstreamGraph).memory ≠ replacement := by
  intro same
  have initialized := aigMemoryStateAt_initial technology
    (receiverWholeGraph hardware.adcCode (finiteADCPhysicalRuntimeClockBits hardware bootInitial))
    (current.step downstreamTechnology downstreamGraph).memory
    (current.step downstreamTechnology downstreamGraph).assignment downstreamTechnology downstreamGraph
    hardware.meteredSource.fixture.coreSource hardware.clockCode node polarity
  have joined := initialized.symm.trans
    (current.step_receiver_memory_no_reset downstreamTechnology downstreamGraph node polarity)
  rw [same] at joined
  exact different joined

end Netlist.Dissipative.Dimensioned.Driven.Regression
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
