import H0mework.Physics.ConductanceCell.Margins
import H0mework.Computation.DualRailAIG.InputReadout

/-! # A real final NAND stage generates the stronger storage capture band -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface Set Storage

theorem compileAIGDualRailTrajectoryFromInputs_gate_capture
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
    (node : Fin graph.decls.size) (left right : AIG.Fanin)
    (selected : graph.decls[node.val] = .gate left right)
    (time : ℝ) (within : time ≤ last)
    (late : first + (compileAIGDualRailTrajectoryFromInputs technology graph input initial node).ready false ≤ time) :
    CaptureBand (compileDualRailCell technology graph node false)
      (AIG.denote.go node.val graph.decls assign node.isLt graph.hdag)
      ((compileAIGDualRailTrajectoryFromInputs technology graph input initial node).wave false time) := by
  have negativeActual := (compileAIGDualRailTrajectoryFromInputs_window technology graph input initial
    initialRail inputContinuous assign first last firstNonnegative inputBands node true).same_supply
    (other := compileDualRailCell technology graph node false) rfl
  have equation := compileAIGDualRailTrajectoryFromInputs.eq_def technology graph input initial node
  split at equation <;> simp_all only [reduceCtorEq]
  have capture := (compileDualRailCell technology graph node false).driven_capture_nand
    (AIG.denote.go node.val graph.decls assign node.isLt graph.hdag ^^ true)
    (AIG.denote.go node.val graph.decls assign node.isLt graph.hdag ^^ true)
    _ _ (initial node false) negativeActual.continuous negativeActual.continuous (initialRail node false)
    _ time negativeActual.ready_nonneg
    (by simpa only [AIGDualRailTrajectory.ready_false, AIGDualRailTrajectory.ready_true, add_assoc] using late)
    (fun t ht => ⟨negativeActual.settled t ⟨ht.1, ht.2.trans within⟩,
      negativeActual.settled t ⟨ht.1, ht.2.trans within⟩⟩)
  simpa only [AIGDualRailTrajectory.wave_false, AIGDualRailTrajectory.wave_true,
    Bool.xor_true, Bool.and_self, Bool.not_not] using capture

end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
