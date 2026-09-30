import H0mework.Computation.AIGHold.AIGMemoryEndpoint
import H0mework.Physics.ConductanceCell.ArbitraryRecovery
import H0mework.Physics.ConductanceCell.DrivenEnergy

/-! # The original bank control histories recover their own actually loaded output capacitor -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical

open Std.Sat Units.Interface Set
open Netlist.Dissipative.Dimensioned.Driven.Producer

namespace Cells.Conductance

theorem compileAIGInputTrajectory_prefix_eq
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (left right : Fin graph.decls.size → Bool → SIVolt) (bound : Nat)
    (same : ∀ node, node.val < bound → ∀ polarity, left node polarity = right node polarity)
    (node : Fin graph.decls.size) (before : node.val < bound) :
    compileAIGDualRailTrajectoryFromInputs technology graph input left node =
      compileAIGDualRailTrajectoryFromInputs technology graph input right node := by
  conv_lhs => rw [compileAIGDualRailTrajectoryFromInputs.eq_def]
  conv_rhs => rw [compileAIGDualRailTrajectoryFromInputs.eq_def]
  split
  · rfl
  · rename_i atom selected
    simp only [same node before true]
  · rename_i l r selected
    have earlier := graph.hdag node.isLt selected
    dsimp only
    rw [compileAIGInputTrajectory_prefix_eq technology graph input left right bound same
      ⟨l.gate, earlier.1.trans node.isLt⟩ (earlier.1.trans before)]
    rw [compileAIGInputTrajectory_prefix_eq technology graph input left right bound same
      ⟨r.gate, earlier.2.trans node.isLt⟩ (earlier.2.trans before)]
    simp only [same node before false, same node before true]
termination_by (node.val, 0)

end Cells.Conductance
namespace Cells.Storage

open Cells.Conductance

variable {α : Type} [DecidableEq α] [Hashable α] {width : Nat}

private abbrev bankRecoveryNode (entry : AIG.RefVecEntry α width) (index : Fin width) :
    Fin (aigOutputBank entry).aig.decls.size :=
  ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
    ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩

/-- Updating isolated positive output capacitors cannot rewrite the actual negative controls. -/
theorem aigBankNegative_independent_of_positive_replacement
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width) (input : α → ℝ → SIVolt)
    (left right : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (sameOld : ∀ node, node.val < entry.aig.decls.size → ∀ polarity, left node polarity = right node polarity)
    (sameNegative : ∀ node, left node true = right node true) (index : Fin width) :
    (compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig input left
      (bankRecoveryNode entry index)).wave true =
    (compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig input right
      (bankRecoveryNode entry index)).wave true := by
  have declaration := aigOutputBank_decl entry index
  have controls := aigOutputBank_controls_are_old entry (bankRecoveryNode entry index) _ _ declaration
  conv_lhs => rw [compileAIGDualRailTrajectoryFromInputs.eq_def]
  conv_rhs => rw [compileAIGDualRailTrajectoryFromInputs.eq_def]
  split
  · rename_i selected
    exact False.elim (by cases selected.symm.trans declaration)
  · rename_i atom selected
    exact False.elim (by cases selected.symm.trans declaration)
  · rename_i l r selected
    obtain ⟨rfl, rfl⟩ := AIG.Decl.gate.inj (selected.symm.trans declaration)
    have earlier := (aigOutputBank entry).aig.hdag (bankRecoveryNode entry index).isLt declaration
    simp only [AIG.Fanin.gate_mk] at earlier controls
    simp only [AIGDualRailTrajectory.wave_true, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]
    rw [sameNegative]
    rw [compileAIGInputTrajectory_prefix_eq technology (aigOutputBank entry).aig input left right
      entry.aig.decls.size sameOld
      ⟨(entry.vec.get index.val index.isLt).gate, earlier.1.trans (bankRecoveryNode entry index).isLt⟩ controls.1]
    rw [compileAIGInputTrajectory_prefix_eq technology (aigOutputBank entry).aig input left right
      entry.aig.decls.size sameOld ⟨0, earlier.2.trans (bankRecoveryNode entry index).isLt⟩ controls.2]

noncomputable section

variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)

def aigBankRecoveryControl (index : Fin width) (offset time : ℝ) : SIVolt :=
  (compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig
    (aigMemoryInputWave technology entry memory assignment) memory.gateInitial
    (bankRecoveryNode entry index)).wave true (offset + time)

def aigBankRecoveryReady (offset : ℝ) : ℝ :=
  max 0 ((packetLineReadyTime technology (aigOutputBank entry).aig).value +
    (aigDualRailGraphDeadline technology (aigOutputBank entry).aig).value - offset)

private theorem bankNegativeWindow (index : Fin width) (last : ℝ) :
    CellRailWindow (aigBankCell technology entry index)
      (!(AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩))
      ((compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig
        (aigMemoryInputWave technology entry memory assignment) memory.gateInitial
        (bankRecoveryNode entry index)).wave true)
      ((packetLineReadyTime technology (aigOutputBank entry).aig).value +
        (compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig
          (aigMemoryInputWave technology entry memory assignment) memory.gateInitial
          (bankRecoveryNode entry index)).ready true) last := by
  have inputs := packetLineInputWave_registered_consumers technology (aigOutputBank entry).aig assignment memory.inputInitial
    (fun node atom registered => memory.inputInitial_in_rail atom node registered) last
  have actual := compileAIGDualRailTrajectoryFromInputs_window technology (aigOutputBank entry).aig
    (aigMemoryInputWave technology entry memory assignment) memory.gateInitial memory.gateInitial_in_rail inputs.1
    assignment (packetLineReadyTime technology (aigOutputBank entry).aig).value last
    (packetLineReadyTime_nonneg technology (aigOutputBank entry).aig) inputs.2 (bankRecoveryNode entry index) true
  have logical := aigOutputBank_denote entry index assignment
  simp only [AIG.denote, aigOutputBank_ref_invert, Bool.xor_false] at logical
  simp only [bankRecoveryNode, Bool.xor_true, logical] at actual
  exact actual.same_supply rfl

theorem aigBankRecoveryControl_continuous (index : Fin width) (offset : ℝ) :
    Continuous (fun t => (aigBankRecoveryControl technology entry memory assignment index offset t).value) :=
  (bankNegativeWindow technology entry memory assignment index 0).continuous.comp (continuous_const.add continuous_id)

theorem aigBankRecoveryControl_band (index : Fin width) (offset time : ℝ)
    (late : aigBankRecoveryReady technology entry offset ≤ time) :
    BitBand (aigBankCell technology entry index)
      (!(AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩))
      (aigBankRecoveryControl technology entry memory assignment index offset time) := by
  have window := bankNegativeWindow technology entry memory assignment index (offset + time)
  have delay := compileAIGDualRailTrajectoryFromInputs_ready_le_graphDeadline technology (aigOutputBank entry).aig
    (aigMemoryInputWave technology entry memory assignment) memory.gateInitial (bankRecoveryNode entry index) true
  have first := (le_max_right 0 ((packetLineReadyTime technology (aigOutputBank entry).aig).value +
    (aigDualRailGraphDeadline technology (aigOutputBank entry).aig).value - offset)).trans late
  exact window.settled (offset + time) ⟨by linarith, le_rfl⟩

def aigBankRecoveryVoltageAt (index : Fin width) (actualInitial : SIVolt) (offset time : ℝ) : SIVolt :=
  ⟨(aigBankCell technology entry index).drivenVoltageAt
    (aigBankRecoveryControl technology entry memory assignment index offset)
    (aigBankRecoveryControl technology entry memory assignment index offset) actualInitial time⟩

theorem aigBankRecoveryVoltageAt_initial (index : Fin width) (actualInitial : SIVolt) (offset : ℝ) :
    aigBankRecoveryVoltageAt technology entry memory assignment index actualInitial offset 0 = actualInitial := by
  apply SIQuantity.ext
  exact (aigBankCell technology entry index).drivenVoltageAt_initial _ _ _

def aigBankRecoverySampleTime (index : Fin width) (actualInitial : SIVolt) (offset : ℝ)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) : SISecond :=
  finiteSamplingClockSampleTime clock code
    ⟨aigBankRecoveryReady technology entry offset + ((aigBankCell technology entry index).arbitraryRecoveryTime actualInitial).value⟩

theorem aigBankRecoverySampleTime_correct (index : Fin width) (actualInitial : SIVolt) (offset : ℝ)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    BitBand (aigBankCell technology entry index)
      (AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩)
      (aigBankRecoveryVoltageAt technology entry memory assignment index actualInitial offset
        (aigBankRecoverySampleTime technology entry index actualInitial offset clock code).value) := by
  have controls := aigBankRecoveryControl_continuous technology entry memory assignment index offset
  have generated := (aigBankCell technology entry index).driven_nand_from_arbitrary_initial
    (!(AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩))
    (!(AIG.denote assignment ⟨entry.aig, entry.vec.get index.val index.isLt⟩))
    (aigBankRecoveryControl technology entry memory assignment index offset)
    (aigBankRecoveryControl technology entry memory assignment index offset) actualInitial controls controls
    (aigBankRecoveryReady technology entry offset) _ (le_max_left _ _)
    (finiteSamplingClock_requested_le_sampleTime clock code _)
    (fun t ht => ⟨aigBankRecoveryControl_band technology entry memory assignment index offset t ht.1,
      aigBankRecoveryControl_band technology entry memory assignment index offset t ht.1⟩)
  simpa only [Bool.and_self, Bool.not_not, aigBankRecoveryVoltageAt, aigBankRecoverySampleTime] using generated

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
