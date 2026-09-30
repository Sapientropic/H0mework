import H0mework.Computation.AIGHold.HeldCapacitorRestriction
import H0mework.Computation.AIGHold.AIGBankRecoveryMemory

/-!
# Literal recovery addresses and uninterrupted raw-branch work

`aigMemoryCapacitorIsHeld` is reused only as the original appended-positive address test.
These capacitors are actively driven during recovery, not isolated. All other addresses
remain restrictions of the original raw history at `offset + time`.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance MeasureTheory

variable {α : Type} [DecidableEq α] [Hashable α] {width : Nat}

noncomputable section

def aigRecoveryCapacitorIndex (entry : AIG.RefVecEntry α width)
    (address : AIGCapacitorAddress (aigOutputBank entry).aig)
    (_restored : aigMemoryCapacitorIsHeld entry address) : Fin width :=
  ⟨address.val.1.val - entry.aig.decls.size, by
    have bound := address.val.1.isLt
    have size := aigOutputBank_size entry
    have after := _restored.1
    omega⟩

theorem aigRecoveryCapacitorIndex_node (entry : AIG.RefVecEntry α width)
    (address : AIGCapacitorAddress (aigOutputBank entry).aig)
    (restored : aigMemoryCapacitorIsHeld entry address) :
    (⟨((aigOutputBank entry).vec.get (aigRecoveryCapacitorIndex entry address restored).val
      (aigRecoveryCapacitorIndex entry address restored).isLt).gate,
      ((aigOutputBank entry).vec.get (aigRecoveryCapacitorIndex entry address restored).val
        (aigRecoveryCapacitorIndex entry address restored).isLt).hgate⟩ :
      Fin (aigOutputBank entry).aig.decls.size) = address.val.1 := by
  apply Fin.ext
  dsimp only
  rw [aigOutputBank_ref_gate]
  dsimp only [aigRecoveryCapacitorIndex]
  exact Nat.add_sub_of_le restored.1

theorem aigRecoveryCapacitorCell_eq_bank (technology : AIGCellTechnology)
    (entry : AIG.RefVecEntry α width) (address : AIGCapacitorAddress (aigOutputBank entry).aig)
    (restored : aigMemoryCapacitorIsHeld entry address) :
    compileDualRailCell technology (aigOutputBank entry).aig address.val.1 address.val.2 =
      aigBankCell technology entry (aigRecoveryCapacitorIndex entry address restored) := by
  unfold aigBankCell
  rw [aigRecoveryCapacitorIndex_node, restored.2]

variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
  (address : AIGCapacitorAddress (aigOutputBank entry).aig)

theorem aigRecoveryCapacitorStateAt_output (actualInitial : Fin width → SIVolt) (offset time : ℝ)
    (restored : aigMemoryCapacitorIsHeld entry address) :
    aigBankCommonRecoveryStateAt technology entry memory assignment actualInitial offset
      address.val.1 address.val.2 time =
      aigBankRecoveryVoltageAt technology entry memory assignment (aigRecoveryCapacitorIndex entry address restored)
        (actualInitial (aigRecoveryCapacitorIndex entry address restored)) offset time := by
  rw [restored.2, ← aigRecoveryCapacitorIndex_node entry address restored]
  exact aigBankCommonRecoveryStateAt_output technology entry memory assignment actualInitial offset _ time

theorem aigRecoveryCapacitorStateAt_history (actualInitial : Fin width → SIVolt) (offset time : ℝ)
    (ordinary : ¬ aigMemoryCapacitorIsHeld entry address) :
    aigBankCommonRecoveryStateAt technology entry memory assignment actualInitial offset
      address.val.1 address.val.2 time =
      aigCapacitorVoltageAt technology (aigOutputBank entry).aig
        (aigMemoryInputWave technology entry memory assignment) memory.gateInitial address (offset + time) :=
  dif_neg ordinary

local notation "rawInput" => aigMemoryInputWave technology entry memory assignment
local notation "actualCell" => compileDualRailCell technology (AIG.RefVecEntry.aig (aigOutputBank entry))
  (Prod.fst (Subtype.val address)) (Prod.snd (Subtype.val address))

def aigRecoveryRawCapacitorWorkBetween (start stop : ℝ) : SIJoule :=
  ⟨∫ t in start..stop,
    (aigCapacitorSupplyPowerAt technology (aigOutputBank entry).aig rawInput memory.gateInitial address t).value⟩

def aigRecoveryRawCapacitorHeatBetween (start stop : ℝ) : SIJoule :=
  ⟨∫ t in start..stop,
    (aigCapacitorDissipatedPowerAt technology (aigOutputBank entry).aig rawInput memory.gateInitial address t).value⟩

theorem aigRecoveryRawCapacitorHeatBetween_nonneg (start stop : ℝ) (ordered : start ≤ stop) :
    0 ≤ (aigRecoveryRawCapacitorHeatBetween technology entry memory assignment address start stop).value :=
  intervalIntegral.integral_nonneg_of_forall ordered (fun t =>
    aigCapacitorDissipatedPowerAt_nonneg technology (aigOutputBank entry).aig rawInput memory.gateInitial address t)

/-- This is the original branch's finite interval, with neither a new seed nor a new trajectory. -/
theorem aigRecoveryRawCapacitor_integrated_balance (start stop : ℝ) :
    (aigCapacitorStoredEnergyAt technology (aigOutputBank entry).aig rawInput memory.gateInitial address stop).value -
      (aigCapacitorStoredEnergyAt technology (aigOutputBank entry).aig rawInput memory.gateInitial address start).value =
        (aigRecoveryRawCapacitorWorkBetween technology entry memory assignment address start stop).value -
          (aigRecoveryRawCapacitorHeatBetween technology entry memory assignment address start stop).value := by
  have inputs : ∀ (node : Fin (aigOutputBank entry).aig.decls.size) atom,
      (aigOutputBank entry).aig.decls[node.val] = .atom atom → Continuous (fun t => (rawInput atom t).value) :=
    fun _ atom _ => packetLineInputWave_continuous _ _ _ _ atom
  obtain ⟨sourceContinuous, heatContinuous⟩ := (actualCell).powerFunctions_continuous
    (aigCapacitorControl technology (aigOutputBank entry).aig rawInput memory.gateInitial address false)
    (aigCapacitorControl technology (aigOutputBank entry).aig rawInput memory.gateInitial address true)
    (aigCapacitorVoltageAt technology (aigOutputBank entry).aig rawInput memory.gateInitial address)
    (aigCapacitorControl_continuous _ _ _ _ inputs address false)
    (aigCapacitorControl_continuous _ _ _ _ inputs address true)
    (aigCapacitorVoltageAt_continuous _ _ _ _ inputs address)
  change Continuous (fun t => (aigCapacitorSupplyPowerAt technology (aigOutputBank entry).aig
    rawInput memory.gateInitial address t).value) at sourceContinuous
  change Continuous (fun t => (aigCapacitorDissipatedPowerAt technology (aigOutputBank entry).aig
    rawInput memory.gateInitial address t).value) at heatContinuous
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc start stop) =>
      aigCapacitorStoredEnergyAt_power_balance technology (aigOutputBank entry).aig rawInput
        memory.gateInitial inputs address t)
    ((sourceContinuous.sub heatContinuous).intervalIntegrable start stop)
  rw [intervalIntegral.integral_sub (sourceContinuous.intervalIntegrable start stop)
    (heatContinuous.intervalIntegrable start stop)] at paid
  exact paid.symm

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
