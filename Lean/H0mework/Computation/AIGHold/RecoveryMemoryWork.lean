import H0mework.Computation.AIGHold.RecoveryCapacitorWork
import H0mework.Computation.AIGHold.HeldMemoryIntervalWork

/-!
# Complete recovery memory and its actual source-work account

Registered input drivers continue on the original `offset..offset+t` interval; every
literal capacitor contributes its already proved recovery account. The actual recovery
writer preserves precisely these input and capacitor coordinates at the generated clock.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α : Type} [DecidableEq α] [Hashable α] {width : Nat}

noncomputable section

variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
  (actualInitial : Fin width → SIVolt) (offset : ℝ)

def aigRecoveryMemoryStoredEnergyAt (time : ℝ) : SIJoule :=
  aigActualStoredEnergy technology (aigOutputBank entry).aig
    (fun atom => aigMemoryInputWave technology entry memory assignment atom (offset + time))
    (fun node polarity => aigBankCommonRecoveryStateAt technology entry memory assignment
      actualInitial offset node polarity time)

def aigRecoveryMemoryWorkAt (time : ℝ) : SIJoule :=
  ⟨((packetLinesWorkAt technology (aigOutputBank entry).aig assignment memory.inputInitial (offset + time)).value -
      (packetLinesWorkAt technology (aigOutputBank entry).aig assignment memory.inputInitial offset).value) +
    ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
      (aigRecoveryCapacitorWorkAt technology entry memory assignment actualInitial offset address time).value⟩

def aigRecoveryMemoryHeatAt (time : ℝ) : SIJoule :=
  ⟨((packetLinesHeatAt technology (aigOutputBank entry).aig assignment memory.inputInitial (offset + time)).value -
      (packetLinesHeatAt technology (aigOutputBank entry).aig assignment memory.inputInitial offset).value) +
    ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
      (aigRecoveryCapacitorHeatAt technology entry memory assignment actualInitial offset address time).value⟩

theorem aigRecoveryMemoryHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (aigRecoveryMemoryHeatAt technology entry memory assignment actualInitial offset time).value := by
  dsimp only [aigRecoveryMemoryHeatAt]
  exact add_nonneg (packetLinesHeatAt_interval_nonneg _ _ _ _ _ _ (le_add_of_nonneg_right nonnegative))
    (Finset.sum_nonneg (fun address _ =>
      aigRecoveryCapacitorHeatAt_nonneg technology entry memory assignment actualInitial offset address time nonnegative))

/-- No input driver is omitted and no literal capacitor is counted a second time. -/
theorem aigRecoveryMemoryStoredEnergyAt_integrated_balance (time : ℝ) :
    (aigRecoveryMemoryStoredEnergyAt technology entry memory assignment actualInitial offset time).value -
      (aigRecoveryMemoryStoredEnergyAt technology entry memory assignment actualInitial offset 0).value =
        (aigRecoveryMemoryWorkAt technology entry memory assignment actualInitial offset time).value -
          (aigRecoveryMemoryHeatAt technology entry memory assignment actualInitial offset time).value := by
  have inputs := packetLinesStoredEnergyAt_interval_balance technology (aigOutputBank entry).aig
    assignment memory.inputInitial offset (offset + time)
  have rows := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (address : AIGCapacitorAddress (aigOutputBank entry).aig) _ =>
      aigRecoveryCapacitorStoredEnergyAt_integrated_balance technology entry memory assignment actualInitial offset address time)
  simp only [Finset.sum_sub_distrib] at rows
  change
    ((packetLinesStoredEnergyAt technology (aigOutputBank entry).aig assignment memory.inputInitial (offset + time)).value +
      ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
        (aigRecoveryCapacitorStoredEnergyAt technology entry memory assignment actualInitial offset address time).value) -
    ((packetLinesStoredEnergyAt technology (aigOutputBank entry).aig assignment memory.inputInitial (offset + 0)).value +
      ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
        (aigRecoveryCapacitorStoredEnergyAt technology entry memory assignment actualInitial offset address 0).value) = _
  dsimp only [aigRecoveryMemoryWorkAt, aigRecoveryMemoryHeatAt]
  rw [add_zero]
  linarith

/-- The pre-existing writer generates its endpoint from the same raw input and recovery sheets. -/
theorem aigBankCommonRecoveryMemory_storedEnergy
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) (offsetNonnegative : 0 ≤ offset) :
    (aigBankCommonRecoveryMemory technology entry memory assignment actualInitial offset clock code offsetNonnegative).storedEnergy =
      aigRecoveryMemoryStoredEnergyAt technology entry memory assignment actualInitial offset
        (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value := by
  apply SIQuantity.ext
  unfold AIGCapacitorMemory.storedEnergy aigRecoveryMemoryStoredEnergyAt aigActualStoredEnergy
  dsimp only
  congr 1
  · apply Finset.sum_congr rfl
    intro atom registered
    let port : AIGInputPort (aigOutputBank entry).aig :=
      ⟨atom, (mem_aigRegisteredInputAtoms_iff _ _).mp registered⟩
    have same := aigBankCommonRecoveryMemory_input_exact technology entry memory assignment
      actualInitial offset clock code offsetNonnegative port
    change (aigBankCommonRecoveryMemory technology entry memory assignment actualInitial offset
      clock code offsetNonnegative).inputInitial atom = _ at same
    rw [same]
  · apply Finset.sum_congr rfl
    intro address _
    rw [aigBankCommonRecoveryMemory_cell_exact]

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
