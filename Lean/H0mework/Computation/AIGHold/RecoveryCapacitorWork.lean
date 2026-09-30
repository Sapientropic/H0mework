import H0mework.Computation.AIGHold.RecoveryCapacitorRestriction

/-!
# Per-capacitor source work and heat of the actual common recovery

The source's actual loaded voltages restart the appended positive cells with their original
negative controls. Every other capacitor continues its original history. The address test is
not an isolation assertion: recovery outputs again conduct through the same physical cell.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance

variable {α : Type} [DecidableEq α] [Hashable α] {width : Nat}

noncomputable section

variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
  (actualInitial : Fin width → SIVolt) (offset : ℝ)
  (address : AIGCapacitorAddress (aigOutputBank entry).aig)

local notation "actualCell" => compileDualRailCell technology (AIG.RefVecEntry.aig (aigOutputBank entry))
  (Prod.fst (Subtype.val address)) (Prod.snd (Subtype.val address))
local notation "rawInput" => aigMemoryInputWave technology entry memory assignment

/-- Both branches integrate actual source power; the ordinary branch includes the entire wait. -/
def aigRecoveryCapacitorWorkAt (time : ℝ) : SIJoule :=
  if restored : aigMemoryCapacitorIsHeld entry address then
    let index := aigRecoveryCapacitorIndex entry address restored
    (aigBankCell technology entry index).drivenWorkAt
      (aigBankRecoveryControl technology entry memory assignment index offset)
      (aigBankRecoveryControl technology entry memory assignment index offset) (actualInitial index) time
  else aigRecoveryRawCapacitorWorkBetween technology entry memory assignment address offset (offset + time)

def aigRecoveryCapacitorHeatAt (time : ℝ) : SIJoule :=
  if restored : aigMemoryCapacitorIsHeld entry address then
    let index := aigRecoveryCapacitorIndex entry address restored
    (aigBankCell technology entry index).drivenHeatAt
      (aigBankRecoveryControl technology entry memory assignment index offset)
      (aigBankRecoveryControl technology entry memory assignment index offset) (actualInitial index) time
  else aigRecoveryRawCapacitorHeatBetween technology entry memory assignment address offset (offset + time)

/-- Energy reads the existing recovery-state voltage at the literal capacitor address. -/
def aigRecoveryCapacitorStoredEnergyAt (time : ℝ) : SIJoule :=
  ⟨(actualCell).capacitance.value / 2 *
    (aigBankCommonRecoveryStateAt technology entry memory assignment actualInitial offset
      address.val.1 address.val.2 time).value ^ 2⟩

theorem aigRecoveryCapacitorStoredEnergyAt_initial :
    (aigRecoveryCapacitorStoredEnergyAt technology entry memory assignment actualInitial offset address 0).value =
      (actualCell).capacitance.value / 2 *
        (if restored : aigMemoryCapacitorIsHeld entry address then
          actualInitial (aigRecoveryCapacitorIndex entry address restored)
        else aigCapacitorVoltageAt technology (aigOutputBank entry).aig rawInput memory.gateInitial address offset).value ^ 2 := by
  unfold aigRecoveryCapacitorStoredEnergyAt
  by_cases restored : aigMemoryCapacitorIsHeld entry address
  · rw [dif_pos restored, aigRecoveryCapacitorStateAt_output _ _ _ _ _ _ _ _ restored,
      aigBankRecoveryVoltageAt_initial]
  · rw [dif_neg restored, aigRecoveryCapacitorStateAt_history _ _ _ _ _ _ _ _ restored, add_zero]

theorem aigRecoveryCapacitorHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (aigRecoveryCapacitorHeatAt technology entry memory assignment actualInitial offset address time).value := by
  unfold aigRecoveryCapacitorHeatAt
  split
  · exact LoadedConductanceCellSource.drivenHeatAt_nonneg _ _ _ _ time nonnegative
  · exact aigRecoveryRawCapacitorHeatBetween_nonneg technology entry memory assignment address offset
      (offset + time) (le_add_of_nonneg_right nonnegative)

/-- Same-C recovery and uninterrupted raw history both pay the actual energy change. -/
theorem aigRecoveryCapacitorStoredEnergyAt_integrated_balance (time : ℝ) :
    (aigRecoveryCapacitorStoredEnergyAt technology entry memory assignment actualInitial offset address time).value -
      (aigRecoveryCapacitorStoredEnergyAt technology entry memory assignment actualInitial offset address 0).value =
        (aigRecoveryCapacitorWorkAt technology entry memory assignment actualInitial offset address time).value -
          (aigRecoveryCapacitorHeatAt technology entry memory assignment actualInitial offset address time).value := by
  unfold aigRecoveryCapacitorStoredEnergyAt aigRecoveryCapacitorWorkAt aigRecoveryCapacitorHeatAt
  by_cases restored : aigMemoryCapacitorIsHeld entry address
  · simp only [dif_pos restored]
    rw [aigRecoveryCapacitorStateAt_output _ _ _ _ _ _ _ _ restored,
      aigRecoveryCapacitorStateAt_output _ _ _ _ _ _ _ _ restored,
      aigBankRecoveryVoltageAt_initial, aigRecoveryCapacitorCell_eq_bank _ _ _ restored]
    let index := aigRecoveryCapacitorIndex entry address restored
    have controls := aigBankRecoveryControl_continuous technology entry memory assignment index offset
    have paid := (aigBankCell technology entry index).drivenStoredEnergyAt_integrated_balance
      (aigBankRecoveryControl technology entry memory assignment index offset)
      (aigBankRecoveryControl technology entry memory assignment index offset) (actualInitial index) controls controls time
    change (aigBankCell technology entry index).capacitance.value / 2 *
      (aigBankRecoveryVoltageAt technology entry memory assignment index (actualInitial index) offset time).value ^ 2 = _ at paid
    linarith
  · simp only [dif_neg restored]
    rw [aigRecoveryCapacitorStateAt_history _ _ _ _ _ _ _ _ restored,
      aigRecoveryCapacitorStateAt_history _ _ _ _ _ _ _ _ restored, add_zero]
    exact aigRecoveryRawCapacitor_integrated_balance technology entry memory assignment address offset (offset + time)

/-- The untouched branch reads exactly the original branch powers, never a new zero-current history. -/
theorem aigRecoveryCapacitorWorkAt_ordinary (time : ℝ)
    (ordinary : ¬ aigMemoryCapacitorIsHeld entry address) :
    aigRecoveryCapacitorWorkAt technology entry memory assignment actualInitial offset address time =
      aigRecoveryRawCapacitorWorkBetween technology entry memory assignment address offset (offset + time) :=
  dif_neg ordinary

theorem aigRecoveryCapacitorHeatAt_ordinary (time : ℝ)
    (ordinary : ¬ aigMemoryCapacitorIsHeld entry address) :
    aigRecoveryCapacitorHeatAt technology entry memory assignment actualInitial offset address time =
      aigRecoveryRawCapacitorHeatBetween technology entry memory assignment address offset (offset + time) :=
  dif_neg ordinary

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
