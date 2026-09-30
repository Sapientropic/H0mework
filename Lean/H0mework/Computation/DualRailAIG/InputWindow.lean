import H0mework.Computation.DualRailAIG.InputTrajectory
import H0mework.Computation.DualRailAIG.CellWindow

/-! # Original AIG semantics from a finite stable window of actual input voltages -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface Set

theorem compileAIGDualRailTrajectoryFromInputs_window
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (initialRail : ∀ node polarity,
      InRail (compileDualRailCell technology graph node polarity) (initial node polarity))
    (inputContinuous : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom → Continuous (fun t => (input atom t).value))
    (assign : α → Bool) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (inputBands : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom → ∀ t ∈ Icc first last,
        BitBand (compileDualRailCell technology graph node false) (assign atom) (input atom t))
    (node : Fin graph.decls.size) (polarity : Bool) :
    CellRailWindow (compileDualRailCell technology graph node polarity)
      (AIG.denote.go node.val graph.decls assign node.isLt graph.hdag ^^ polarity)
      ((compileAIGDualRailTrajectoryFromInputs technology graph input initial node).wave polarity)
      (first + (compileAIGDualRailTrajectoryFromInputs technology graph input initial node).ready polarity) last := by
  rw [compileAIGDualRailTrajectoryFromInputs.eq_def]
  split
  · rw [AIG.denote.go.eq_def]
    split <;> simp_all only [reduceCtorEq]
    cases polarity with
    | false =>
        simpa only [AIGDualRailTrajectory.wave_false, AIGDualRailTrajectory.ready_false,
          Bool.false_xor, Bool.false_eq_true, ↓reduceIte, add_zero] using
          CellRailWindow.constant (compileDualRailCell technology graph node false) false first last firstNonnegative
    | true =>
        simpa only [AIGDualRailTrajectory.wave_true, AIGDualRailTrajectory.ready_true,
          Bool.false_xor, ↓reduceIte, compileDualRailCell, add_zero] using
          CellRailWindow.constant (compileDualRailCell technology graph node true) true first last firstNonnegative
  · rename_i atom selected
    have primary : CellRailWindow (compileDualRailCell technology graph node false)
        (assign atom) (input atom) first last :=
      ⟨firstNonnegative, inputContinuous node atom selected, inputBands node atom selected⟩
    have negativePrimary := primary.same_supply (other := compileDualRailCell technology graph node true) rfl
    have inverted := negativePrimary.nand negativePrimary (initial node true) (initialRail node true)
    rw [AIG.denote.go.eq_def]
    split <;> simp_all only [AIG.Decl.atom.injEq, reduceCtorEq]
    cases polarity
    · simpa only [AIGDualRailTrajectory.wave_false, AIGDualRailTrajectory.ready_false,
        Bool.xor_false, add_zero] using primary
    · simpa only [AIGDualRailTrajectory.wave_true, AIGDualRailTrajectory.ready_true,
        Bool.and_self, Bool.xor_true, max_self] using inverted
  · rename_i left right selected
    have fanins := graph.hdag node.isLt selected
    let leftNode : Fin graph.decls.size := ⟨left.gate, by omega⟩
    let rightNode : Fin graph.decls.size := ⟨right.gate, by omega⟩
    have leftActual := (compileAIGDualRailTrajectoryFromInputs_window technology graph input initial
      initialRail inputContinuous assign first last firstNonnegative inputBands leftNode left.invert).same_supply
      (other := compileDualRailCell technology graph node true) rfl
    have rightActual := (compileAIGDualRailTrajectoryFromInputs_window technology graph input initial
      initialRail inputContinuous assign first last firstNonnegative inputBands rightNode right.invert).same_supply
      (other := compileDualRailCell technology graph node true) rfl
    have negative := leftActual.nand rightActual (initial node true) (initialRail node true)
    have negativeForPositive := negative.same_supply (other := compileDualRailCell technology graph node false) rfl
    have positive := negativeForPositive.nand negativeForPositive (initial node false) (initialRail node false)
    rw [AIG.denote.go.eq_def]
    split <;> simp_all only [reduceCtorEq]
    rename_i left' right' sameDeclaration
    obtain ⟨rfl, rfl⟩ := AIG.Decl.gate.inj (selected.symm.trans sameDeclaration)
    cases polarity
    · simpa only [AIGDualRailTrajectory.wave_false, AIGDualRailTrajectory.ready_false,
        Bool.xor_false, Bool.and_self, Bool.not_not, max_self, leftNode, rightNode, ← add_max, add_assoc] using positive
    · simpa only [AIGDualRailTrajectory.wave_true, AIGDualRailTrajectory.ready_true,
        Bool.xor_true, leftNode, rightNode, ← add_max, add_assoc] using negative
termination_by (node.val, 0)

end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
