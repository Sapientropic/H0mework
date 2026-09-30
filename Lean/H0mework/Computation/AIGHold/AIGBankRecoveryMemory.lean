import H0mework.Computation.AIGHold.AIGBankCommonRecovery
import H0mework.Computation.AIGHold.AIGMemoryRestart

/-! # Simultaneous recovery generates a complete reusable memory without resetting its other coordinates -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

noncomputable section

variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
  (actualInitial : Fin width → SIVolt) (offset : ℝ)

def aigBankCommonRecoveryStateAt (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool) (time : ℝ) : SIVolt :=
  if restored : entry.aig.decls.size ≤ node.val ∧ polarity = false then
    let index : Fin width := ⟨node.val - entry.aig.decls.size, by
      have size := aigOutputBank_size entry
      have bound := node.isLt
      omega⟩
    aigBankRecoveryVoltageAt technology entry memory assignment index (actualInitial index) offset time
  else
    (compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig
      (aigMemoryInputWave technology entry memory assignment) memory.gateInitial node).wave polarity (offset + time)

theorem aigBankCommonRecoveryStateAt_output (index : Fin width) (time : ℝ) :
    aigBankCommonRecoveryStateAt technology entry memory assignment actualInitial offset
      ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate, ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false time =
      aigBankRecoveryVoltageAt technology entry memory assignment index (actualInitial index) offset time := by
  unfold aigBankCommonRecoveryStateAt
  rw [dif_pos ⟨by dsimp only; rw [aigOutputBank_ref_gate]; omega, rfl⟩]
  dsimp only
  apply congrArg (fun selected : Fin width =>
    aigBankRecoveryVoltageAt technology entry memory assignment selected (actualInitial selected) offset time)
  apply Fin.ext
  dsimp only
  simp only [aigOutputBank_ref_gate, Nat.add_sub_cancel_left]

variable (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)

theorem aigBankCommonRecoveryStateAt_sample_in_rail (offsetNonnegative : 0 ≤ offset)
    (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool) :
    InRail (compileDualRailCell technology (aigOutputBank entry).aig node polarity)
      (aigBankCommonRecoveryStateAt technology entry memory assignment actualInitial offset node polarity
        (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value) := by
  unfold aigBankCommonRecoveryStateAt
  split
  · rename_i restored
    let index : Fin width := ⟨node.val - entry.aig.decls.size, by
      have size := aigOutputBank_size entry
      have bound := node.isLt
      omega⟩
    have address : (⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
      ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ : Fin (aigOutputBank entry).aig.decls.size) = node := by
      apply Fin.ext
      dsimp only
      rw [aigOutputBank_ref_gate]
      dsimp only [index]
      omega
    have rail := aigBankCommonRecoveryTime_in_rail technology entry memory assignment actualInitial offset clock code index
    change InRail (compileDualRailCell technology (aigOutputBank entry).aig
      ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
        ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false) _ at rail
    rw [address, ← restored.2] at rail
    exact rail
  · apply compileAIGDualRailTrajectoryFromInputs_mem_rail technology (aigOutputBank entry).aig
      (aigMemoryInputWave technology entry memory assignment) memory.gateInitial memory.gateInitial_in_rail
    · intro _ atom _
      exact packetLineInputWave_continuous _ _ _ _ _
    · intro registeredNode atom registered t ht
      exact packetLineInputWave_mem_rail technology (aigOutputBank entry).aig assignment memory.inputInitial atom
        (memory.inputInitial_in_rail atom registeredNode registered) t ht
    · exact add_nonneg offsetNonnegative (aigBankCommonRecoveryTime_nonneg technology entry actualInitial offset clock code)

def aigBankCommonRecoveryMemory (offsetNonnegative : 0 ≤ offset) : AIGCapacitorMemory technology (aigOutputBank entry).aig where
  inputVoltage := fun port => aigMemoryInputWave technology entry memory assignment port.val
    (offset + (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value)
  inputRail := by
    intro port
    obtain ⟨node, registered⟩ := port.property
    exact packetLineInputWave_mem_rail technology (aigOutputBank entry).aig assignment memory.inputInitial port.val
      (memory.inputInitial_in_rail port.val node registered) _
      (add_nonneg offsetNonnegative (aigBankCommonRecoveryTime_nonneg technology entry actualInitial offset clock code))
  cellVoltage := fun address => aigBankCommonRecoveryStateAt technology entry memory assignment actualInitial offset
    address.val.1 address.val.2 (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value
  cellRail := fun address => aigBankCommonRecoveryStateAt_sample_in_rail technology entry memory assignment actualInitial offset
    clock code offsetNonnegative address.val.1 address.val.2

variable (offsetNonnegative : 0 ≤ offset)

theorem aigBankCommonRecoveryMemory_input_exact (port : AIGInputPort (aigOutputBank entry).aig) :
    (aigBankCommonRecoveryMemory technology entry memory assignment actualInitial offset clock code offsetNonnegative).inputInitial port.val =
      aigMemoryInputWave technology entry memory assignment port.val
        (offset + (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value) :=
  (aigBankCommonRecoveryMemory technology entry memory assignment actualInitial offset clock code offsetNonnegative).inputInitial_registered port

theorem aigBankCommonRecoveryMemory_cell_exact (address : AIGCapacitorAddress (aigOutputBank entry).aig) :
    (aigBankCommonRecoveryMemory technology entry memory assignment actualInitial offset clock code offsetNonnegative).gateInitial
      address.val.1 address.val.2 =
      aigBankCommonRecoveryStateAt technology entry memory assignment actualInitial offset address.val.1 address.val.2
        (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value :=
  (aigBankCommonRecoveryMemory technology entry memory assignment actualInitial offset clock code offsetNonnegative).gateInitial_capacitor address

theorem aigBankCommonRecoveryMemory_initial_exact (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool) :
    (aigBankCommonRecoveryMemory technology entry memory assignment actualInitial offset clock code offsetNonnegative).gateInitial node polarity =
      aigBankCommonRecoveryStateAt technology entry memory assignment actualInitial offset node polarity
        (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value := by
  by_cases capacitive : aigNodeHasCapacitor (aigOutputBank entry).aig node polarity = true
  · exact aigBankCommonRecoveryMemory_cell_exact technology entry memory assignment actualInitial offset clock code
      offsetNonnegative (⟨(node, polarity), capacitive⟩ : AIGCapacitorAddress (aigOutputBank entry).aig)
  · have old := aigOutputBank_noncapacitive_is_old entry node polarity capacitive
    rw [AIGCapacitorMemory.gateInitial, dif_neg capacitive, aigBankCommonRecoveryStateAt,
      dif_neg (by intro restored; omega)]
    have equation := compileAIGDualRailTrajectoryFromInputs.eq_def technology (aigOutputBank entry).aig
      (aigMemoryInputWave technology entry memory assignment) memory.gateInitial node
    split at equation
    · rename_i selected
      rw [equation]
      cases polarity <;> simp only [selected, AIGDualRailTrajectory.wave_false,
        AIGDualRailTrajectory.wave_true, Bool.false_eq_true, ↓reduceIte]
    · rename_i atom selected
      rw [equation]
      cases polarity
      · simp only [selected, AIGDualRailTrajectory.wave_false]
        exact aigBankCommonRecoveryMemory_input_exact technology entry memory assignment actualInitial offset clock code offsetNonnegative
          (⟨atom, ⟨node, selected⟩⟩ : AIGInputPort (aigOutputBank entry).aig)
      · exact False.elim (capacitive (by simp only [aigNodeHasCapacitor, selected]))
    · rename_i l r selected
      exact False.elim (capacitive (by simp only [aigNodeHasCapacitor, selected]))

theorem aigBankCommonRecoveryMemory_restart (newAssignment : α → Bool)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool) :
    aigMemoryStateAt technology entry
      (aigBankCommonRecoveryMemory technology entry memory assignment actualInitial offset clock code offsetNonnegative)
      newAssignment downstreamTechnology downstreamGraph clock code node polarity 0 =
      aigBankCommonRecoveryStateAt technology entry memory assignment actualInitial offset node polarity
        (aigBankCommonRecoveryTime technology entry actualInitial offset clock code).value := by
  rw [aigMemoryStateAt_initial]
  exact aigBankCommonRecoveryMemory_initial_exact technology entry memory assignment actualInitial offset clock code offsetNonnegative node polarity

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
