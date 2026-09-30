import H0mework.Computation.AIGHold.AIGCapacitorMemory

/-! # Every next capacitor coordinate is read from the same actual held run -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

noncomputable section

def aigMemoryInputWave (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool) :
    α → ℝ → SIVolt :=
  packetLineInputWave technology (aigOutputBank entry).aig assignment memory.inputInitial

def aigMemoryStateAt (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    Fin (aigOutputBank entry).aig.decls.size → Bool → ℝ → SIVolt :=
  aigHeldBankStateAt technology entry (aigMemoryInputWave technology entry memory assignment)
    memory.gateInitial downstreamTechnology downstreamGraph
    (packetLineReadyTime technology (aigOutputBank entry).aig).value clock code

theorem aigMemoryStateAt_mem_rail (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    InRail (compileDualRailCell technology (aigOutputBank entry).aig node polarity)
      (aigMemoryStateAt technology entry memory assignment downstreamTechnology downstreamGraph clock code node polarity time) := by
  apply aigHeldBankStateAt_mem_rail technology entry _ memory.gateInitial memory.gateInitial_in_rail
  · intro _ atom _
    exact packetLineInputWave_continuous technology (aigOutputBank entry).aig assignment memory.inputInitial atom
  · intro registeredNode atom registered t ht
    exact packetLineInputWave_mem_rail technology (aigOutputBank entry).aig assignment memory.inputInitial atom
      (memory.inputInitial_in_rail atom registeredNode registered) t ht
  · exact packetLineReadyTime_nonneg technology (aigOutputBank entry).aig
  · exact nonnegative

def aigMemoryEndpoint (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    AIGCapacitorMemory technology (aigOutputBank entry).aig where
  inputVoltage := fun port => aigMemoryInputWave technology entry memory assignment port.val time
  inputRail := by
    intro port
    obtain ⟨node, registered⟩ := port.property
    exact packetLineInputWave_mem_rail technology (aigOutputBank entry).aig assignment memory.inputInitial port.val
      (memory.inputInitial_in_rail port.val node registered) time nonnegative
  cellVoltage := fun address => aigMemoryStateAt technology entry memory assignment
    downstreamTechnology downstreamGraph clock code address.val.1 address.val.2 time
  cellRail := fun address => aigMemoryStateAt_mem_rail technology entry memory assignment
    downstreamTechnology downstreamGraph clock code address.val.1 address.val.2 time nonnegative

theorem aigMemoryEndpoint_input_exact (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (time : ℝ) (nonnegative : 0 ≤ time) (port : AIGInputPort (aigOutputBank entry).aig) :
    (aigMemoryEndpoint technology entry memory assignment downstreamTechnology downstreamGraph clock code time nonnegative).inputInitial
      port.val = aigMemoryInputWave technology entry memory assignment port.val time := by
  exact (aigMemoryEndpoint technology entry memory assignment downstreamTechnology downstreamGraph clock code time nonnegative).inputInitial_registered
    port

theorem aigMemoryEndpoint_cell_exact (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (time : ℝ) (nonnegative : 0 ≤ time) (address : AIGCapacitorAddress (aigOutputBank entry).aig) :
    (aigMemoryEndpoint technology entry memory assignment downstreamTechnology downstreamGraph clock code time nonnegative).gateInitial
      address.val.1 address.val.2 =
        aigMemoryStateAt technology entry memory assignment downstreamTechnology downstreamGraph clock code
          address.val.1 address.val.2 time := by
  exact (aigMemoryEndpoint technology entry memory assignment downstreamTechnology downstreamGraph clock code time nonnegative).gateInitial_capacitor
    address

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
