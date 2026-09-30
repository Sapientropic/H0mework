import H0mework.Computation.DualRailAIG.InputTrajectory

/-!
# Actual initial charge and reusable physical endpoint of the same raw graph

Only generated capacitive outputs inherit `initial`: both gate rails and the
atom's negative rail. Constant rails and positive atom rails remain their
actual supply/input sources. No logical output label enters these state laws.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface

variable {α : Type} [DecidableEq α] [Hashable α]

theorem compileAIGDualRailTrajectoryFromInputs_initial
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) (polarity : Bool) :
    (compileAIGDualRailTrajectoryFromInputs technology graph input initial node).wave polarity 0 =
      match graph.decls[node.val], polarity with
      | .false, false => ⟨0⟩
      | .false, true => technology.supply
      | .atom atom, false => input atom 0
      | _, _ => initial node polarity := by
  rw [compileAIGDualRailTrajectoryFromInputs.eq_def]
  split <;> rename_i selected
  all_goals
    cases polarity <;>
      simp only [selected, AIGDualRailTrajectory.wave_false, AIGDualRailTrajectory.wave_true,
        LoadedConductanceCellSource.drivenVoltageAt_initial]

theorem compileAIGDualRailTrajectoryFromInputs_gate_initial
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt) (node : Fin graph.decls.size)
    (left right : AIG.Fanin) (selected : graph.decls[node.val] = .gate left right) (polarity : Bool) :
    (compileAIGDualRailTrajectoryFromInputs technology graph input initial node).wave polarity 0 =
      initial node polarity := by
  rw [compileAIGDualRailTrajectoryFromInputs_initial, selected]

theorem compileAIGDualRailTrajectoryFromInputs_atom_negative_initial
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt) (node : Fin graph.decls.size)
    (atom : α) (selected : graph.decls[node.val] = .atom atom) :
    (compileAIGDualRailTrajectoryFromInputs technology graph input initial node).wave true 0 =
      initial node true := by
  rw [compileAIGDualRailTrajectoryFromInputs_initial, selected]

theorem compileAIGDualRailTrajectoryFromInputs_atom_positive_initial
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt) (node : Fin graph.decls.size)
    (atom : α) (selected : graph.decls[node.val] = .atom atom) :
    (compileAIGDualRailTrajectoryFromInputs technology graph input initial node).wave false 0 = input atom 0 := by
  rw [compileAIGDualRailTrajectoryFromInputs_initial, selected]

theorem compileAIGDualRailTrajectoryFromInputs_state_invariant
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (initialRail : ∀ node polarity,
      InRail (compileDualRailCell technology graph node polarity) (initial node polarity))
    (inputContinuous : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom → Continuous (fun t => (input atom t).value))
    (inputRail : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom → ∀ t, 0 ≤ t →
        InRail (compileDualRailCell technology graph node false) (input atom t))
    (node : Fin graph.decls.size) (polarity : Bool) :
    Continuous (fun t =>
      ((compileAIGDualRailTrajectoryFromInputs technology graph input initial node).wave polarity t).value) ∧
    (∀ t, 0 ≤ t → InRail (compileDualRailCell technology graph node polarity)
      ((compileAIGDualRailTrajectoryFromInputs technology graph input initial node).wave polarity t)) := by
  rw [compileAIGDualRailTrajectoryFromInputs.eq_def]
  split
  · cases polarity
    · simp only [AIGDualRailTrajectory.wave_false]
      refine ⟨continuous_const, ?_⟩
      intro _ _
      exact ⟨le_rfl, technology.supply_pos.le⟩
    · simp only [AIGDualRailTrajectory.wave_true]
      refine ⟨continuous_const, ?_⟩
      intro _ _
      exact ⟨technology.supply_pos.le, le_rfl⟩
  · rename_i atom selected
    have continuous := inputContinuous node atom selected
    cases polarity
    · exact ⟨continuous, inputRail node atom selected⟩
    · exact ⟨(compileDualRailCell technology graph node true).drivenVoltageAt_continuous
        _ _ _ continuous continuous,
        (compileDualRailCell technology graph node true).drivenVoltageAt_mem_rail
          _ _ _ continuous continuous (initialRail node true)⟩
  · rename_i left right selected
    have fanins := graph.hdag node.isLt selected
    let leftNode : Fin graph.decls.size := ⟨left.gate, by omega⟩
    let rightNode : Fin graph.decls.size := ⟨right.gate, by omega⟩
    have leftContinuous := (compileAIGDualRailTrajectoryFromInputs_state_invariant technology graph input initial
      initialRail inputContinuous inputRail leftNode left.invert).1
    have rightContinuous := (compileAIGDualRailTrajectoryFromInputs_state_invariant technology graph input initial
      initialRail inputContinuous inputRail rightNode right.invert).1
    have negativeContinuous := (compileDualRailCell technology graph node true).drivenVoltageAt_continuous
      _ _ (initial node true) leftContinuous rightContinuous
    cases polarity
    · exact ⟨(compileDualRailCell technology graph node false).drivenVoltageAt_continuous
        _ _ _ negativeContinuous negativeContinuous,
        (compileDualRailCell technology graph node false).drivenVoltageAt_mem_rail
          _ _ _ negativeContinuous negativeContinuous (initialRail node false)⟩
    · exact ⟨negativeContinuous,
        (compileDualRailCell technology graph node true).drivenVoltageAt_mem_rail
          _ _ _ leftContinuous rightContinuous (initialRail node true)⟩
termination_by (node.val, 0)

theorem compileAIGDualRailTrajectoryFromInputs_mem_rail
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (initialRail : ∀ node polarity,
      InRail (compileDualRailCell technology graph node polarity) (initial node polarity))
    (inputContinuous : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom → Continuous (fun t => (input atom t).value))
    (inputRail : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom → ∀ t, 0 ≤ t →
        InRail (compileDualRailCell technology graph node false) (input atom t))
    (node : Fin graph.decls.size) (polarity : Bool) (time : ℝ) (nonnegative : 0 ≤ time) :
    InRail (compileDualRailCell technology graph node polarity)
      ((compileAIGDualRailTrajectoryFromInputs technology graph input initial node).wave polarity time) :=
  (compileAIGDualRailTrajectoryFromInputs_state_invariant technology graph input initial
    initialRail inputContinuous inputRail node polarity).2 time nonnegative

end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
