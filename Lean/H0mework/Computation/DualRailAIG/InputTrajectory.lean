import H0mework.Computation.DualRailAIG.DualRailLoad
import H0mework.Physics.ConductanceCell.Restoration

/-!
# The source graph driven by actual input voltage histories

Atom inputs are voltage trajectories, not logical assignments. Every internal
capacitor starts at time zero and sees the complete upstream history. Ready
fields are source-relative propagation delays; they do not assert that an input
has already settled. Input labels and stable windows belong only to consumers.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface

structure AIGDualRailTrajectory where
  positive : ℝ → SIVolt
  negative : ℝ → SIVolt
  positiveReady : ℝ
  negativeReady : ℝ

namespace AIGDualRailTrajectory

/-- The AIG polarity bit selects the inverted rail exactly when it is true. -/
def wave (trajectory : AIGDualRailTrajectory) (polarity : Bool) : ℝ → SIVolt :=
  if polarity then trajectory.negative else trajectory.positive

def ready (trajectory : AIGDualRailTrajectory) (polarity : Bool) : ℝ :=
  if polarity then trajectory.negativeReady else trajectory.positiveReady

@[simp] theorem wave_false (trajectory : AIGDualRailTrajectory) :
    trajectory.wave false = trajectory.positive := rfl

@[simp] theorem wave_true (trajectory : AIGDualRailTrajectory) :
    trajectory.wave true = trajectory.negative := rfl

@[simp] theorem ready_false (trajectory : AIGDualRailTrajectory) :
    trajectory.ready false = trajectory.positiveReady := rfl

@[simp] theorem ready_true (trajectory : AIGDualRailTrajectory) :
    trajectory.ready true = trajectory.negativeReady := rfl

end AIGDualRailTrajectory

noncomputable section

/-- One source-native recursive producer supplies both raw and ideal-input operation. -/
def compileAIGDualRailTrajectoryFromInputs {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) : AIGDualRailTrajectory :=
  match declaration : graph.decls[node.val] with
  | .false =>
      { positive := fun _ => ⟨0⟩
        negative := fun _ => technology.supply
        positiveReady := 0
        negativeReady := 0 }
  | .atom atom =>
      let positive := input atom
      let negativeCell := compileDualRailCell technology graph node true
      { positive := positive
        negative := fun time => ⟨negativeCell.drivenVoltageAt positive positive (initial node true) time⟩
        positiveReady := 0
        negativeReady := negativeCell.settlingTime.value }
  | .gate left right =>
      have fanins := graph.hdag node.isLt declaration
      let leftTrajectory := compileAIGDualRailTrajectoryFromInputs technology graph input initial
        ⟨left.gate, by omega⟩
      let rightTrajectory := compileAIGDualRailTrajectoryFromInputs technology graph input initial
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
        negativeReady := negativeReady }
termination_by (node.val, 0)

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
