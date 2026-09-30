import H0mework.Computation.DualRailAIG.Clock

/-! # Actual input histories retain the same source-only propagation schedule -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface

noncomputable section

theorem compileAIGDualRailTrajectoryFromInputs_ready_eq_source
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) (polarity : Bool) :
    (compileAIGDualRailTrajectoryFromInputs technology graph input initial node).ready polarity =
      aigDualRailReadyAt technology graph node polarity := by
  rw [compileAIGDualRailTrajectoryFromInputs.eq_def]
  split
  · rw [aigDualRailReadyAt.eq_def]
    dsimp only [AIGDualRailTrajectory.ready]
    cases polarity <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals split <;> simp_all
  · rw [aigDualRailReadyAt.eq_def]
    dsimp only [AIGDualRailTrajectory.ready]
    cases polarity <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals split <;> simp_all
  · rename_i left right declaration
    have fanins := graph.hdag node.isLt declaration
    have leftRead := compileAIGDualRailTrajectoryFromInputs_ready_eq_source technology graph input initial
      ⟨left.gate, by omega⟩ left.invert
    have rightRead := compileAIGDualRailTrajectoryFromInputs_ready_eq_source technology graph input initial
      ⟨right.gate, by omega⟩ right.invert
    rw [aigDualRailReadyAt.eq_def]
    split <;> simp_all [AIGDualRailTrajectory.ready]
    rename_i left' right' sameDeclaration
    obtain ⟨rfl, rfl⟩ := AIG.Decl.gate.inj (declaration.symm.trans sameDeclaration)
    rfl
termination_by (node.val, 0)

theorem compileAIGDualRailTrajectoryFromInputs_ready_nonneg
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) (polarity : Bool) :
    0 ≤ (compileAIGDualRailTrajectoryFromInputs technology graph input initial node).ready polarity := by
  rw [compileAIGDualRailTrajectoryFromInputs_ready_eq_source]
  exact aigDualRailReadyAt_nonneg technology graph node polarity

theorem compileAIGDualRailTrajectoryFromInputs_ready_le_graphDeadline
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) (polarity : Bool) :
    (compileAIGDualRailTrajectoryFromInputs technology graph input initial node).ready polarity ≤
      (aigDualRailGraphDeadline technology graph).value := by
  rw [compileAIGDualRailTrajectoryFromInputs_ready_eq_source]
  exact aigDualRailReadyAt_le_graphDeadline technology graph node polarity

theorem compileAIGDualRailTrajectoryFromInputs_ready_independent
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (input₁ input₂ : α → ℝ → SIVolt)
    (initial₁ initial₂ : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) (polarity : Bool) :
    (compileAIGDualRailTrajectoryFromInputs technology graph input₁ initial₁ node).ready polarity =
      (compileAIGDualRailTrajectoryFromInputs technology graph input₂ initial₂ node).ready polarity := by
  rw [compileAIGDualRailTrajectoryFromInputs_ready_eq_source,
    compileAIGDualRailTrajectoryFromInputs_ready_eq_source]

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
