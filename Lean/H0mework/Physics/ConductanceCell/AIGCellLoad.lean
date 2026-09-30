import Std.Sat.AIG.Basic
import Mathlib.Data.Fintype.Prod
import H0mework.Physics.Measurement.Units
import H0mework.Physics.ConductanceCell.Clock

/-!
# Source-addressed capacitive loads

Every actual input pin is counted, including two pins with the same source and
opposite polarities. The load rule includes one storage input and two controlled
conductance pins per downstream input. This is a load census, not a claim that
NAND alone implements an AIG AND or its inverted references.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat
open Units.Interface

/-- False selects the left input; true selects the right input. -/
abbrev CellInputSide := Bool

def cellInputFanin? {α : Type} (decl : AIG.Decl α) (side : CellInputSide) : Option AIG.Fanin :=
  match decl, side with
  | .gate left _, false => some left
  | .gate _ right, true => some right
  | _, _ => none

def aigCellLoadPins {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size) : Finset (Fin graph.decls.size × CellInputSide) :=
  Finset.univ.filter fun pin =>
    (cellInputFanin? graph.decls[pin.1.val] pin.2).map AIG.Fanin.gate = some node.val

theorem mem_aigCellLoadPins_iff {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size) (pin : Fin graph.decls.size × CellInputSide) :
    pin ∈ aigCellLoadPins graph node ↔
      (cellInputFanin? graph.decls[pin.1.val] pin.2).map AIG.Fanin.gate = some node.val := by
  simp only [aigCellLoadPins, Finset.mem_filter, Finset.mem_univ, true_and]

def aigCellFanoutCount {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size) : Nat :=
  (aigCellLoadPins graph node).card

theorem aigCellFanoutCount_le {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size) :
    aigCellFanoutCount graph node ≤ 2 * graph.decls.size := by
  have bound := Finset.card_le_card (Finset.filter_subset
    (fun pin : Fin graph.decls.size × CellInputSide =>
      (cellInputFanin? graph.decls[pin.1.val] pin.2).map AIG.Fanin.gate = some node.val)
    Finset.univ)
  have sides : Fintype.card CellInputSide = 2 := rfl
  simpa only [aigCellFanoutCount, aigCellLoadPins, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, sides, Nat.mul_comm] using bound

noncomputable section

def aigCellLoadCapacitance {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size)
    (intrinsic pin : SIFarad) : SIFarad :=
  ⟨intrinsic.value + ((1 + 2 * aigCellFanoutCount graph node : Nat) : ℝ) * pin.value⟩

theorem aigCellLoadCapacitance_pos {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size)
    (intrinsic pin : SIFarad) (intrinsicPositive : 0 < intrinsic.value)
    (pinNonnegative : 0 ≤ pin.value) :
    0 < (aigCellLoadCapacitance graph node intrinsic pin).value := by
  exact add_pos_of_pos_of_nonneg intrinsicPositive
    (mul_nonneg (Nat.cast_nonneg _) pinNonnegative)

/-- Technology parameters are independent of the graph's inputs or requested logical result. -/
structure AIGCellTechnology where
  supply : SIVolt
  resistance : SIOhm
  intrinsicCapacitance : SIFarad
  pinCapacitance : SIFarad
  supply_pos : 0 < supply.value
  resistance_pos : 0 < resistance.value
  intrinsic_pos : 0 < intrinsicCapacitance.value
  pin_nonnegative : 0 ≤ pinCapacitance.value

def compileAIGLoadedCell {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (node : Fin graph.decls.size) :
    LoadedConductanceCellSource where
  supply := technology.supply
  resistance := technology.resistance
  capacitance := aigCellLoadCapacitance graph node technology.intrinsicCapacitance technology.pinCapacitance
  supply_pos := technology.supply_pos
  resistance_pos := technology.resistance_pos
  capacitance_pos := aigCellLoadCapacitance_pos graph node _ _ technology.intrinsic_pos technology.pin_nonnegative

theorem compiledAIGCell_wait_reads_actual_load {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (node : Fin graph.decls.size) :
    (compileAIGLoadedCell technology graph node).settlingTime.value =
      1152 * technology.resistance.value *
        (technology.intrinsicCapacitance.value +
          ((1 + 2 * aigCellFanoutCount graph node : Nat) : ℝ) * technology.pinCapacitance.value) :=
  (compileAIGLoadedCell technology graph node).settlingTime_eq

/-- This cell uses the source node's actual addressed load and the existing source clock. -/
theorem compiledAIGCell_sampled_nand {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (node : Fin graph.decls.size)
    (clockSource : Netlist.Dissipative.Dimensioned.Driven.Producer.ResonantDrivenCoreSource)
    (code : Netlist.Dissipative.Dimensioned.Driven.Producer.FiniteSamplingClockCode)
    (leftBit rightBit : Bool) (left right initial : SIVolt)
    (leftBand : BitBand (compileAIGLoadedCell technology graph node) leftBit left)
    (rightBand : BitBand (compileAIGLoadedCell technology graph node) rightBit right)
    (initialRail : InRail (compileAIGLoadedCell technology graph node) initial) :
    let cell := compileAIGLoadedCell technology graph node
    BitBand cell (!(leftBit && rightBit))
      (cell.flowAt left right initial (cell.sampledTime clockSource code)) ∧
    railRead? cell (cell.flowAt left right initial (cell.sampledTime clockSource code)) =
      some (!(leftBit && rightBit)) :=
  (compileAIGLoadedCell technology graph node).sampled_nand clockSource code
    leftBit rightBit left right initial leftBand rightBand initialRail

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
