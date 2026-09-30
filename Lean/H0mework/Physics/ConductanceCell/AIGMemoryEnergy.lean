import H0mework.Physics.ConductanceCell.AIGEnergy
import H0mework.Computation.AIGHold.AIGMemoryRestart

/-! # The complete registered memory reads the driven energy at actual capture -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

noncomputable section

def aigActualStoredEnergy (technology : AIGCellTechnology) (graph : AIG α)
    (inputVoltage : α → SIVolt) (cellVoltage : Fin graph.decls.size → Bool → SIVolt) : SIJoule :=
  ⟨(∑ atom ∈ aigRegisteredInputAtoms graph,
      (compilePacketLineDriver technology graph atom).capacitance.value / 2 * (inputVoltage atom).value ^ 2) +
    ∑ address : AIGCapacitorAddress graph,
      (compileDualRailCell technology graph address.val.1 address.val.2).capacitance.value / 2 *
        (cellVoltage address.val.1 address.val.2).value ^ 2⟩

def AIGCapacitorMemory.storedEnergy {technology : AIGCellTechnology} {graph : AIG α}
    (memory : AIGCapacitorMemory technology graph) : SIJoule :=
  aigActualStoredEnergy technology graph memory.inputInitial memory.gateInitial

variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)

def aigMemoryStoredEnergyAt (time : ℝ) : SIJoule :=
  aigActualStoredEnergy technology (aigOutputBank entry).aig
    (fun atom => aigMemoryInputWave technology entry memory assignment atom time)
    (fun node polarity => aigMemoryStateAt technology entry memory assignment
      downstreamTechnology downstreamGraph clock code node polarity time)

theorem aigMemoryStoredEnergyAt_initial :
    aigMemoryStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph clock code 0 =
      memory.storedEnergy := by
  unfold aigMemoryStoredEnergyAt AIGCapacitorMemory.storedEnergy
  congr 1
  · funext atom
    exact packetLineInputWave_initial _ _ _ _ atom
  · funext node polarity
    exact aigMemoryStateAt_initial _ _ _ _ _ _ _ _ node polarity

theorem aigMemoryStoredEnergyAt_eq_driven_before_capture (time : ℝ)
    (before : time ≤ (aigInputSampledTime technology (aigOutputBank entry).aig
      (packetLineReadyTime technology (aigOutputBank entry).aig).value clock code).value) :
    aigMemoryStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph clock code time =
      aigDrivenStoredEnergyAt technology (aigOutputBank entry).aig assignment memory.inputInitial memory.gateInitial time := by
  apply SIQuantity.ext
  change _ + _ = _ + _
  congr 1
  apply Finset.sum_congr rfl
  intro address _
  unfold aigCapacitorStoredEnergyAt aigCapacitorVoltageAt
  dsimp only
  rw [show aigMemoryStateAt technology entry memory assignment downstreamTechnology downstreamGraph clock code
      address.val.1 address.val.2 time =
      (compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig
        (aigMemoryInputWave technology entry memory assignment) memory.gateInitial address.val.1).wave address.val.2 time from
    aigHeldBankStateAt_before_capture _ _ _ _ _ _ _ _ _ _ _ _ before]
  rfl

theorem aigMemoryStoredEnergyAt_paid_before_capture (time : ℝ)
    (before : time ≤ (aigInputSampledTime technology (aigOutputBank entry).aig
      (packetLineReadyTime technology (aigOutputBank entry).aig).value clock code).value) :
    (aigMemoryStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph clock code time).value -
        memory.storedEnergy.value =
      (aigDrivenWorkAt technology (aigOutputBank entry).aig assignment memory.inputInitial memory.gateInitial time).value -
        (aigDrivenHeatAt technology (aigOutputBank entry).aig assignment memory.inputInitial memory.gateInitial time).value := by
  have initialMatch : aigDrivenStoredEnergyAt technology (aigOutputBank entry).aig
      assignment memory.inputInitial memory.gateInitial 0 = memory.storedEnergy := by
    apply SIQuantity.ext
    simp only [aigDrivenStoredEnergyAt, packetLinesStoredEnergyAt, packetLineStoredEnergyAt,
      packetLineInputWave_initial, aigCapacitorStoredEnergyAt_initial,
      AIGCapacitorMemory.storedEnergy, aigActualStoredEnergy]
  rw [aigMemoryStoredEnergyAt_eq_driven_before_capture _ _ _ _ _ _ _ _ time before]
  exact initialMatch ▸ aigDrivenStoredEnergyAt_integrated_balance technology (aigOutputBank entry).aig
    assignment memory.inputInitial memory.gateInitial time

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
