import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Solve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

def projectLast : (n : ℕ) → List (Inequality (n + 1)) → List (Inequality 1)
  | 0, rows => rows
  | n + 1, rows => projectLast n (reduce rows).system

def extendLast : (n : ℕ) → List (Inequality (n + 1)) → ℚ → (Fin (n + 1) → ℚ)
  | 0, _, value => fun _ => value
  | n + 1, rows, value =>
      let reduction := reduce rows
      let rest := extendLast n reduction.system value
      Fin.cons (reduction.head rest) rest

theorem extendLast_keeps_value (n : ℕ) (rows : List (Inequality (n + 1))) (value : ℚ) :
    extendLast n rows value (Fin.last n) = value := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [extendLast, ← Fin.succ_last, Fin.cons_succ]
      exact ih (reduce rows).system

theorem extendLast_feasible (n : ℕ) (rows : List (Inequality (n + 1))) (value : ℚ)
    (projected : Feasible (projectLast n rows) (fun _ => value)) :
    Feasible rows (extendLast n rows value) := by
  induction n with
  | zero => exact projected
  | succ n ih => exact (reduce rows).lifts _ (ih (reduce rows).system projected)

theorem projectLast_sound (n : ℕ) (rows : List (Inequality (n + 1))) (values : Fin (n + 1) → ℚ)
    (original : Feasible rows values) :
    Feasible (projectLast n rows) (fun _ => values (Fin.last n)) := by
  induction n with
  | zero =>
      have same : (fun _ : Fin 1 => values (Fin.last 0)) = values := by
        funext i
        apply congrArg values
        apply Fin.ext
        have bounded := i.isLt
        have terminal := (Fin.last 0).isLt
        omega
      change Feasible rows (fun _ : Fin 1 => values (Fin.last 0))
      rwa [same]
  | succ n ih =>
      exact ih (reduce rows).system (Fin.tail values) ((reduce rows).projects values original)

/-- The retained coordinate is characterized exactly, and every rational
value in its projection lifts to an explicit feasible original assignment. -/
theorem projectLast_iff (n : ℕ) (rows : List (Inequality (n + 1))) (value : ℚ) :
    Feasible (projectLast n rows) (fun _ => value) ↔
      ∃ values, Feasible rows values ∧ values (Fin.last n) = value := by
  constructor
  · intro projected
    exact ⟨extendLast n rows value, extendLast_feasible n rows value projected, extendLast_keeps_value n rows value⟩
  · rintro ⟨values, original, rfl⟩
    exact projectLast_sound n rows values original

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
