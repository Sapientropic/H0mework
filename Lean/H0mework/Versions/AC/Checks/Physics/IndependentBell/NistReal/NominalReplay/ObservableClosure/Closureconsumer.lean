import H0mework.Versions.AC.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.Observableclosure

set_option autoImplicit false

namespace P23.ObservableClosure.Consumer

noncomputable section

@[ext] structure Outcomes where
  both : ℝ
  onlyA : ℝ
  onlyB : ℝ
  neither : ℝ

def windowOutcomes (s : Snapshot) (cell : Cell) (bgA bgB : ℝ) (pulse : ℝ) : Outcomes :=
  let qa := ((1-bgA)/(1+meanA s cell.a))^5
  let qb := ((1-bgB)/(1+meanB s cell.b))^5
  let qab := ((1-bgA)*(1-bgB)*pulse)^5
  ⟨1-qa-qb+qab,qb-qab,qa-qab,qab⟩

def generatedWindow (s : Snapshot) (cell : Cell) (bgA bgB : ℝ) : Outcomes :=
  windowOutcomes s cell bgA bgB (pulse00 s cell)

def predictedWindow (s : Snapshot) (seed cell : Cell) (bgA bgB : ℝ) : Outcomes :=
  windowOutcomes s cell bgA bgB (closurePulse s seed cell)

theorem outcomes_sum_one (s : Snapshot) (cell : Cell) (bgA bgB pulse : ℝ) :
    let o := windowOutcomes s cell bgA bgB pulse
    o.both+o.onlyA+o.onlyB+o.neither=1 := by dsimp [windowOutcomes]; ring

theorem same_source_all_cells (s : Snapshot) (seed : Cell) (hg : g s seed ≠ 0)
    (bgA bgB : ℝ) :
    ∀ cell : Cell, predictedWindow s seed cell bgA bgB=generatedWindow s cell bgA bgB := by
  intro cell
  rw [predictedWindow,same_source_cell_closure s seed cell hg]
  rfl

theorem shared_training_root_and_heldout (s : Snapshot) (a0 a1 bgA bgB : ℝ)
    (ha : Real.cos (2*a0)^2 ≠ Real.cos (2*a1)^2) :
    (trainingF s (mirror a0) (mirror a1)).polynomial.natDegree ≤ 2 ∧
    (trainingF s (mirror a0) (mirror a1)).polynomial.eval (e s)=0 ∧
    (sylvester (trainingF s (mirror a0) (mirror a1))
      (cellRelation s (mirror a0) ⟨a0,-a1⟩)).det=0 ∧
    (sylvester (trainingF s (mirror a0) (mirror a1))
      (cellRelation s (mirror a0) ⟨a1,-a0⟩)).det=0 ∧
    ((g s (mirror a0) ≠ 0 ∧
      ∀ cell, predictedWindow s (mirror a0) cell bgA bgB=generatedWindow s cell bgA bgB) ∨
    (g s (mirror a0)=0 ∧ g s (mirror a1) ≠ 0 ∧
      ∀ cell, predictedWindow s (mirror a1) cell bgA bgB=generatedWindow s cell bgA bgB)) := by
  have hroot := same_source_quadratic_root s (mirror a0) (mirror a1)
  refine ⟨hroot.1,hroot.2,source_resultant_necessary s _ _ _,source_resultant_necessary s _ _ _,?_⟩
  by_cases hg0 : g s (mirror a0) ≠ 0
  · exact Or.inl ⟨hg0,same_source_all_cells s (mirror a0) hg0 bgA bgB⟩
  · have hg1 := (mirror_training_informative s a0 a1 ha).resolve_left hg0
    exact Or.inr ⟨not_ne_iff.mp hg0,hg1,same_source_all_cells s (mirror a1) hg1 bgA bgB⟩

end
end P23.ObservableClosure.Consumer
