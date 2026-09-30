import H0mework.Physics.ConductanceCell.AIGCellLoad
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option

/-!
# Literal loads of the dual-rail AIG lowering

Each rail has one read/storage pin. An external NAND input connects two local
conductance controls. A tied-input internal inverter connects four controls;
it is driven by a gate's negative rail or an atom's positive rail. These pins
are generated from the same declaration and polarity, never a logical verdict.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface

/-- `none` is the read pin; `inl` is an external addressed control; `inr` is internal. -/
abbrev DualRailLoadPin (nodes : Nat) :=
  Option (((Fin nodes × CellInputSide) × Bool) ⊕ (CellInputSide × Bool))

def internalInverterDriver? {α : Type} (decl : AIG.Decl α) : Option Bool :=
  match decl with
  | .false => none
  | .atom _ => some false
  | .gate _ _ => some true

def dualRailLoadPinPresent {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size) (polarity : Bool)
    (pin : DualRailLoadPin graph.decls.size) : Bool :=
  match pin with
  | none => true
  | some (.inl (address, _control)) =>
      match cellInputFanin? graph.decls[address.1.val] address.2 with
      | none => false
      | some fanin => decide (fanin.gate = node.val ∧ fanin.invert = polarity)
  | some (.inr _) => decide (internalInverterDriver? graph.decls[node.val] = some polarity)

def dualRailLoadPins {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size) (polarity : Bool) :
    Finset (DualRailLoadPin graph.decls.size) :=
  Finset.univ.filter fun pin => dualRailLoadPinPresent graph node polarity pin = true

theorem dualRailReadPin_present {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size) (polarity : Bool) :
    none ∈ dualRailLoadPins graph node polarity := by
  simp [dualRailLoadPins, dualRailLoadPinPresent]

theorem dualRailInternalPin_present_iff {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size) (polarity side control : Bool) :
    some (Sum.inr (side, control)) ∈ dualRailLoadPins graph node polarity ↔
      internalInverterDriver? graph.decls[node.val] = some polarity := by
  simp [dualRailLoadPins, dualRailLoadPinPresent]

def dualRailLoadCount {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size) (polarity : Bool) : Nat :=
  (dualRailLoadPins graph node polarity).card

theorem dualRailLoadCount_pos {α : Type} [DecidableEq α] [Hashable α]
    (graph : AIG α) (node : Fin graph.decls.size) (polarity : Bool) :
    0 < dualRailLoadCount graph node polarity :=
  Finset.card_pos.mpr ⟨none, dualRailReadPin_present graph node polarity⟩

noncomputable section

def compileDualRailCell {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (node : Fin graph.decls.size)
    (polarity : Bool) : LoadedConductanceCellSource where
  supply := technology.supply
  resistance := technology.resistance
  capacitance := ⟨technology.intrinsicCapacitance.value +
    (dualRailLoadCount graph node polarity : ℝ) * technology.pinCapacitance.value⟩
  supply_pos := technology.supply_pos
  resistance_pos := technology.resistance_pos
  capacitance_pos := add_pos_of_pos_of_nonneg technology.intrinsic_pos
    (mul_nonneg (Nat.cast_nonneg _) technology.pin_nonnegative)

theorem compileDualRailCell_wait {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (node : Fin graph.decls.size)
    (polarity : Bool) :
    (compileDualRailCell technology graph node polarity).settlingTime.value =
      1152 * technology.resistance.value * (technology.intrinsicCapacitance.value +
        (dualRailLoadCount graph node polarity : ℝ) * technology.pinCapacitance.value) :=
  (compileDualRailCell technology graph node polarity).settlingTime_eq

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
