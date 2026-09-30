import H0mework.Computation.DualRailAIG.InputTrajectory

/-!
# Ideal-input restriction of the actual voltage-trajectory compiler

The ideal assignment selects supply/ground input trajectories of the one raw
source compiler. The constructor equation below is a compatibility readout,
not a second recursive producer or a latch construction.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface

noncomputable section

/-- Ideal primary rails restrict the actual-input compiler without duplicating it. -/
def compileAIGDualRailTrajectory {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (assign : α → Bool)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) : AIGDualRailTrajectory :=
  compileAIGDualRailTrajectoryFromInputs technology graph
    (fun atom _ => if assign atom then technology.supply else ⟨0⟩) initial node

/-- The original constructor mouth is inherited from the raw source equation. -/
theorem compileAIGDualRailTrajectory.constructor_eq {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (assign : α → Bool)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) :
    compileAIGDualRailTrajectory technology graph assign initial node =
  match declaration : graph.decls[node.val] with
  | .false =>
      { positive := fun _ => ⟨0⟩
        negative := fun _ => technology.supply
        positiveReady := 0
        negativeReady := 0 }
  | .atom atom =>
      let positive : ℝ → SIVolt := fun _ => if assign atom then technology.supply else ⟨0⟩
      let negativeCell := compileDualRailCell technology graph node true
      { positive := positive
        negative := fun time => ⟨negativeCell.drivenVoltageAt positive positive (initial node true) time⟩
        positiveReady := 0
        negativeReady := negativeCell.settlingTime.value }
  | .gate left right =>
      have fanins := graph.hdag node.isLt declaration
      let leftTrajectory := compileAIGDualRailTrajectory technology graph assign initial
        ⟨left.gate, by omega⟩
      let rightTrajectory := compileAIGDualRailTrajectory technology graph assign initial
        ⟨right.gate, by omega⟩
      let leftWave := leftTrajectory.wave left.invert
      let rightWave := rightTrajectory.wave right.invert
      let negativeCell := compileDualRailCell technology graph node true
      let positiveCell := compileDualRailCell technology graph node false
      let negative : ℝ → SIVolt := fun time =>
        ⟨negativeCell.drivenVoltageAt leftWave rightWave (initial node true) time⟩
      let first := max (leftTrajectory.ready left.invert) (rightTrajectory.ready right.invert)
      let negativeReady := first + negativeCell.settlingTime.value
      { positive := fun time => ⟨positiveCell.drivenVoltageAt negative negative (initial node false) time⟩
        negative := negative
        positiveReady := negativeReady + positiveCell.settlingTime.value
        negativeReady := negativeReady } := by
  unfold compileAIGDualRailTrajectory
  rw [compileAIGDualRailTrajectoryFromInputs.eq_def]
  rfl

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
