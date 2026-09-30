import H0mework.Computation.AIGHold.AIGCapacitorMemory

/-!
# Literal control histories of every actual AIG capacitor

Controls are restrictions of the existing raw-input trajectory, not a new
trajectory compiler. Continuity uses only registered input continuity; arbitrary
initial charge needs no rail or logical-output certificate.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface Storage

variable {α : Type} [DecidableEq α] [Hashable α]

noncomputable section

/-- The continuity part of the existing input-state induction does not need its rail invariant. -/
theorem compileAIGDualRailTrajectoryFromInputs_continuous
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (inputContinuous : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom → Continuous (fun t => (input atom t).value))
    (node : Fin graph.decls.size) (polarity : Bool) :
    Continuous (fun t =>
      ((compileAIGDualRailTrajectoryFromInputs technology graph input initial node).wave polarity t).value) := by
  rw [compileAIGDualRailTrajectoryFromInputs.eq_def]
  split
  · cases polarity <;>
      simp only [AIGDualRailTrajectory.wave_false, AIGDualRailTrajectory.wave_true] <;>
      exact continuous_const
  · rename_i atom selected
    have continuous := inputContinuous node atom selected
    cases polarity
    · exact continuous
    · exact (compileDualRailCell technology graph node true).drivenVoltageAt_continuous
        _ _ _ continuous continuous
  · rename_i left right selected
    have fanins := graph.hdag node.isLt selected
    have leftContinuous := compileAIGDualRailTrajectoryFromInputs_continuous
      technology graph input initial inputContinuous ⟨left.gate, by omega⟩ left.invert
    have rightContinuous := compileAIGDualRailTrajectoryFromInputs_continuous
      technology graph input initial inputContinuous ⟨right.gate, by omega⟩ right.invert
    have negativeContinuous := (compileDualRailCell technology graph node true).drivenVoltageAt_continuous
      _ _ (initial node true) leftContinuous rightContinuous
    cases polarity
    · exact (compileDualRailCell technology graph node false).drivenVoltageAt_continuous
        _ _ _ negativeContinuous negativeContinuous
    · exact negativeContinuous
termination_by (node.val, 0)

/-- Negative atoms read their source; negative gates read signed fanins; positive gates read their negative rail. -/
def aigCapacitorControl (technology : AIGCellTechnology) (graph : AIG α)
    (input : α → ℝ → SIVolt) (initial : Fin graph.decls.size → Bool → SIVolt)
    (address : AIGCapacitorAddress graph) (side : CellInputSide) : ℝ → SIVolt :=
  match selected : graph.decls[address.val.1.val] with
  | .false => fun _ => ⟨0⟩
  | .atom atom => input atom
  | .gate left right =>
      have fanins := graph.hdag address.val.1.isLt selected
      if address.val.2 then
        if side then
          (compileAIGDualRailTrajectoryFromInputs technology graph input initial
            ⟨right.gate, by omega⟩).wave right.invert
        else
          (compileAIGDualRailTrajectoryFromInputs technology graph input initial
            ⟨left.gate, by omega⟩).wave left.invert
      else
        (compileAIGDualRailTrajectoryFromInputs technology graph input initial address.val.1).wave true

theorem aigCapacitorControl_atom
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt) (address : AIGCapacitorAddress graph)
    (side : CellInputSide) (atom : α) (selected : graph.decls[address.val.1.val] = .atom atom) :
    aigCapacitorControl technology graph input initial address side = input atom := by
  have controls := aigCapacitorControl.eq_1 technology graph input initial address side
  split at controls <;> simp_all only [reduceCtorEq, AIG.Decl.atom.injEq]

theorem aigCapacitorControl_gate
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt) (address : AIGCapacitorAddress graph)
    (side : CellInputSide) (left right : AIG.Fanin)
    (selected : graph.decls[address.val.1.val] = .gate left right) :
    aigCapacitorControl technology graph input initial address side =
      have fanins := graph.hdag address.val.1.isLt selected
      if address.val.2 then
        if side then
          (compileAIGDualRailTrajectoryFromInputs technology graph input initial
            ⟨right.gate, by omega⟩).wave right.invert
        else
          (compileAIGDualRailTrajectoryFromInputs technology graph input initial
            ⟨left.gate, by omega⟩).wave left.invert
      else
        (compileAIGDualRailTrajectoryFromInputs technology graph input initial address.val.1).wave true := by
  have controls := aigCapacitorControl.eq_1 technology graph input initial address side
  split at controls <;> simp_all only [reduceCtorEq]
  rename_i left' right' sameDeclaration
  obtain ⟨rfl, rfl⟩ := AIG.Decl.gate.inj (selected.symm.trans sameDeclaration)
  rfl

/-- The voltage is the literal address projection of the existing compiler. -/
def aigCapacitorVoltageAt (technology : AIGCellTechnology) (graph : AIG α)
    (input : α → ℝ → SIVolt) (initial : Fin graph.decls.size → Bool → SIVolt)
    (address : AIGCapacitorAddress graph) (time : ℝ) : SIVolt :=
  (compileAIGDualRailTrajectoryFromInputs technology graph input initial address.val.1).wave
    address.val.2 time

theorem aigCapacitorControl_continuous
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (inputContinuous : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom → Continuous (fun t => (input atom t).value))
    (address : AIGCapacitorAddress graph) (side : CellInputSide) :
    Continuous (fun t => (aigCapacitorControl technology graph input initial address side t).value) := by
  have controls := aigCapacitorControl.eq_1 technology graph input initial address side
  split at controls
  · rename_i selected
    rw [controls]
    exact continuous_const
  · rename_i atom selected
    rw [controls]
    exact inputContinuous address.val.1 atom selected
  · rw [controls]
    split
    · split <;> exact compileAIGDualRailTrajectoryFromInputs_continuous
        technology graph input initial inputContinuous _ _
    · exact compileAIGDualRailTrajectoryFromInputs_continuous
        technology graph input initial inputContinuous _ _

/-- Both control pins and the actual voltage belong to the same generated cell occurrence. -/
theorem aigCapacitorVoltageAt_eq_driven
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (address : AIGCapacitorAddress graph) (time : ℝ) :
    (aigCapacitorVoltageAt technology graph input initial address time).value =
      (compileDualRailCell technology graph address.val.1 address.val.2).drivenVoltageAt
        (aigCapacitorControl technology graph input initial address false)
        (aigCapacitorControl technology graph input initial address true)
        (initial address.val.1 address.val.2) time := by
  rcases address with ⟨⟨node, polarity⟩, capacitive⟩
  have equation := compileAIGDualRailTrajectoryFromInputs.eq_def technology graph input initial node
  split at equation
  · rename_i selected
    simp only [aigNodeHasCapacitor, selected, Bool.false_eq_true] at capacitive
  · rename_i atom selected
    have polarity_eq : polarity = true := by simpa only [aigNodeHasCapacitor, selected] using capacitive
    subst polarity
    rw [aigCapacitorControl_atom technology graph input initial _ false atom selected,
      aigCapacitorControl_atom technology graph input initial _ true atom selected]
    simp only [aigCapacitorVoltageAt, equation]
    rfl
  · rename_i left right selected
    rw [aigCapacitorControl_gate technology graph input initial _ false left right selected,
      aigCapacitorControl_gate technology graph input initial _ true left right selected]
    cases polarity <;>
      simp only [aigCapacitorVoltageAt, equation,
        Bool.false_eq_true, ↓reduceIte, AIGDualRailTrajectory.wave_true, AIGDualRailTrajectory.wave_false]

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
