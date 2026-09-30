import H0mework.Computation.AIGHold.HeldCapacitorWork
import H0mework.Computation.AIGHold.InputWork

/-! # The complete held memory, including still-powered internal and input capacitors -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

noncomputable section

variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)

def aigMemoryWorkAt (time : ℝ) : SIJoule :=
  ⟨(packetLinesWorkAt technology (aigOutputBank entry).aig assignment memory.inputInitial time).value +
    ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
      (aigMemoryCapacitorWorkAt technology entry memory assignment clock code address time).value⟩

def aigMemoryHeatAt (time : ℝ) : SIJoule :=
  ⟨(packetLinesHeatAt technology (aigOutputBank entry).aig assignment memory.inputInitial time).value +
    ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
      (aigMemoryCapacitorHeatAt technology entry memory assignment downstreamTechnology downstreamGraph
        clock code address time).value⟩

theorem aigMemoryHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (aigMemoryHeatAt technology entry memory assignment downstreamTechnology downstreamGraph clock code time).value :=
  add_nonneg (packetLinesHeatAt_nonneg _ _ _ _ _ nonnegative)
    (Finset.sum_nonneg fun address _ =>
      aigMemoryCapacitorHeatAt_nonneg _ _ _ _ _ _ _ _ address time nonnegative)

/-- A driven input/internal row remains paid after capture; only the actual isolated
output rows switch to leakage. Every initial charge is the inherited memory. -/
theorem aigMemoryStoredEnergyAt_integrated_balance (time : ℝ) :
    (aigMemoryStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph clock code time).value -
        memory.storedEnergy.value =
      (aigMemoryWorkAt technology entry memory assignment clock code time).value -
        (aigMemoryHeatAt technology entry memory assignment downstreamTechnology downstreamGraph clock code time).value := by
  have inputs := packetLinesStoredEnergyAt_integrated_balance technology (aigOutputBank entry).aig
    assignment memory.inputInitial time
  have cells :
      (∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
        (aigMemoryCapacitorStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph
          clock code address time).value) -
      (∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
        (aigMemoryCapacitorStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph
          clock code address 0).value) =
      (∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
        (aigMemoryCapacitorWorkAt technology entry memory assignment clock code address time).value) -
      (∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
        (aigMemoryCapacitorHeatAt technology entry memory assignment downstreamTechnology downstreamGraph
          clock code address time).value) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro address _
    rw [aigMemoryCapacitorStoredEnergyAt_initial]
    exact aigMemoryCapacitorStoredEnergyAt_integrated_balance _ _ _ _ _ _ _ _ address time
  rw [← aigMemoryStoredEnergyAt_initial technology entry memory assignment downstreamTechnology downstreamGraph clock code]
  change
    ((packetLinesStoredEnergyAt technology (aigOutputBank entry).aig assignment memory.inputInitial time).value +
      ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
        (aigMemoryCapacitorStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph
          clock code address time).value) -
    ((packetLinesStoredEnergyAt technology (aigOutputBank entry).aig assignment memory.inputInitial 0).value +
      ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
        (aigMemoryCapacitorStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph
          clock code address 0).value) = _
  dsimp only [aigMemoryWorkAt, aigMemoryHeatAt]
  linarith

theorem aigMemoryWorkAt_pays_energy_increase (time : ℝ) (nonnegative : 0 ≤ time) :
    (aigMemoryStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph clock code time).value -
        memory.storedEnergy.value ≤
      (aigMemoryWorkAt technology entry memory assignment clock code time).value := by
  have paid := aigMemoryStoredEnergyAt_integrated_balance technology entry memory assignment downstreamTechnology downstreamGraph clock code time
  have heat := aigMemoryHeatAt_nonneg technology entry memory assignment downstreamTechnology downstreamGraph clock code time nonnegative
  linarith

/-- The endpoint writer preserves exactly the registered energy coordinates. -/
theorem aigMemoryEndpoint_storedEnergy (time : ℝ) (nonnegative : 0 ≤ time) :
    (aigMemoryEndpoint technology entry memory assignment downstreamTechnology downstreamGraph
      clock code time nonnegative).storedEnergy =
      aigMemoryStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph clock code time := by
  apply SIQuantity.ext
  unfold AIGCapacitorMemory.storedEnergy aigMemoryStoredEnergyAt aigActualStoredEnergy
  dsimp only
  congr 1
  · apply Finset.sum_congr rfl
    intro atom registered
    let port : AIGInputPort (aigOutputBank entry).aig :=
      ⟨atom, (mem_aigRegisteredInputAtoms_iff _ _).mp registered⟩
    have same := aigMemoryEndpoint_input_exact technology entry memory assignment
      downstreamTechnology downstreamGraph clock code time nonnegative port
    change (aigMemoryEndpoint technology entry memory assignment downstreamTechnology downstreamGraph
      clock code time nonnegative).inputInitial atom = _ at same
    rw [same]
  · apply Finset.sum_congr rfl
    intro address _
    rw [aigMemoryEndpoint_cell_exact]

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
