import H0mework.Computation.AIGHold.AIGHeldState

/-! # Isolated positive outputs have a source load independent of the receiver's word width -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance

variable {α : Type} [DecidableEq α] [Hashable α] {width : Nat}
variable (entry : AIG.RefVecEntry α width) (index : Fin width)

private abbrev outputLoadNode : Fin (aigOutputBank entry).aig.decls.size :=
  ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
    ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩

theorem aigBankPositiveLoadPin_iff_read (pin : DualRailLoadPin (aigOutputBank entry).aig.decls.size) :
    dualRailLoadPinPresent (aigOutputBank entry).aig (outputLoadNode entry index) false pin = true ↔ pin = none := by
  cases pin with
  | none => simp only [dualRailLoadPinPresent]
  | some pin =>
    cases pin with
    | inl address =>
      obtain ⟨⟨consumer, side⟩, control⟩ := address
      cases selected : (aigOutputBank entry).aig.decls[consumer.val] with
      | false => cases side <;> simp [dualRailLoadPinPresent, selected, cellInputFanin?]
      | atom atom => cases side <;> simp [dualRailLoadPinPresent, selected, cellInputFanin?]
      | gate left right =>
        have older := aigOutputBank_controls_are_old entry consumer left right selected
        have addressExact := aigOutputBank_ref_gate entry index
        have leftDifferent : left.gate ≠ (outputLoadNode entry index).val := by
          dsimp only [outputLoadNode]
          omega
        have rightDifferent : right.gate ≠ (outputLoadNode entry index).val := by
          dsimp only [outputLoadNode]
          omega
        cases side <;> simp [dualRailLoadPinPresent, selected, cellInputFanin?, leftDifferent, rightDifferent]
    | inr internal =>
      simp [dualRailLoadPinPresent, aigOutputBank_decl, internalInverterDriver?]

theorem aigBankPositiveLoadPins_exact :
    dualRailLoadPins (aigOutputBank entry).aig (outputLoadNode entry index) false = {none} := by
  ext pin
  simp only [dualRailLoadPins, Finset.mem_filter, Finset.mem_univ, true_and,
    aigBankPositiveLoadPin_iff_read, Finset.mem_singleton]

theorem aigBankPositiveLoadCount_eq_one :
    dualRailLoadCount (aigOutputBank entry).aig (outputLoadNode entry index) false = 1 := by
  rw [dualRailLoadCount, aigBankPositiveLoadPins_exact, Finset.card_singleton]

theorem aigBankCell_capacitance_eq (technology : AIGCellTechnology) :
    (aigBankCell technology entry index).capacitance.value =
      technology.intrinsicCapacitance.value + technology.pinCapacitance.value := by
  change technology.intrinsicCapacitance.value +
    (dualRailLoadCount (aigOutputBank entry).aig (outputLoadNode entry index) false : ℝ) * technology.pinCapacitance.value = _
  rw [aigBankPositiveLoadCount_eq_one]
  simp only [Nat.cast_one, one_mul]

end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
