import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Pin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

variable {n : ℕ}

def chooseHead (rows : List (Inequality (n + 1))) (values : Fin n → ℚ) : ℚ :=
  let read := fun row : Inequality (n + 1) => row.boundAt values
  match (lowerRows rows).argmax read with
  | some lower => read lower
  | none =>
    match (upperRows rows).argmin read with
    | some upper => read upper
    | none => 0

private theorem chooseHead_between (rows : List (Inequality (n + 1))) (values : Fin n → ℚ)
    (projected : Feasible (eliminate rows) values) :
    (∀ lower ∈ lowerRows rows, lower.boundAt values ≤ chooseHead rows values) ∧
    (∀ upper ∈ upperRows rows, chooseHead rows values ≤ upper.boundAt values) := by
  let read := fun row : Inequality (n + 1) => row.boundAt values
  cases low : (lowerRows rows).argmax read with
  | none =>
      have absent := List.argmax_eq_none.mp low
      cases up : (upperRows rows).argmin read with
      | none => simp only [absent, List.argmin_eq_none.mp up, List.not_mem_nil, false_implies, implies_true, and_self]
      | some upper =>
          refine ⟨by simp [absent], ?_⟩
          intro row present
          change (match (lowerRows rows).argmax read with
            | some lower => read lower
            | none => match (upperRows rows).argmin read with
              | some upper => read upper
              | none => 0) ≤ read row
          rw [low, up]
          exact List.le_of_mem_argmin present (Option.mem_def.mpr up)
  | some lower =>
      have chosen : lower ∈ (lowerRows rows).argmax read := Option.mem_def.mpr low
      have equals : chooseHead rows values = read lower := by
        unfold chooseHead
        change (match (lowerRows rows).argmax read with
          | some lower => read lower
          | none => match (upperRows rows).argmin read with
            | some upper => read upper
            | none => 0) = read lower
        rw [low]
      rw [equals]
      exact ⟨fun _ present => List.le_of_mem_argmax present chosen,
        fun _ present => eliminate_keeps_pair projected (List.argmax_mem chosen) present⟩

theorem eliminate_complete {rows : List (Inequality (n + 1))} {values : Fin n → ℚ}
    (projected : Feasible (eliminate rows) values) :
    Feasible rows (Fin.cons (chooseHead rows values) values) := by
  intro row original
  have endpoints := chooseHead_between rows values projected
  rcases lt_trichotomy (row.coeff 0) 0 with negative | zero | positive
  · exact (holds_lower row _ values negative).mpr (endpoints.1 row (mem_lowerRows.mpr ⟨original, negative⟩))
  · apply (holds_zero row _ values zero).mpr
    exact projected _ (List.mem_append_left _ (List.mem_map.mpr ⟨row, mem_zeroRows.mpr ⟨original, zero⟩, rfl⟩))
  · exact (holds_upper row _ values positive).mpr (endpoints.2 row (mem_upperRows.mpr ⟨original, positive⟩))

theorem eliminate_iff (rows : List (Inequality (n + 1))) (values : Fin n → ℚ) :
    Feasible (eliminate rows) values ↔ ∃ head : ℚ, Feasible rows (Fin.cons head values) :=
  ⟨fun projected => ⟨chooseHead rows values, eliminate_complete projected⟩,
    fun ⟨_, original⟩ => eliminate_sound original⟩

structure Reduction (rows : List (Inequality (n + 1))) where
  system : List (Inequality n)
  head : (Fin n → ℚ) → ℚ
  projects : ∀ values, Feasible rows values → Feasible system (Fin.tail values)
  lifts : ∀ values, Feasible system values → Feasible rows (Fin.cons (head values) values)

/-- A fixed original singleton coordinate is substituted. All other
coordinates use the complete signed-pair elimination. -/
def reduce (rows : List (Inequality (n + 1))) : Reduction rows :=
  match findPin rows with
  | some fixed => {
      system := substitute rows fixed.value
      head := fun _ => fixed.value
      projects := fun values checked => (substitute_iff rows fixed.value (Fin.tail values)).mpr (by
        rw [← fixed.determined values checked, Fin.cons_self_tail]
        exact checked)
      lifts := fun values checked => (substitute_iff rows fixed.value values).mp checked
    }
  | none => {
      system := eliminate rows
      head := chooseHead rows
      projects := fun values checked => eliminate_sound (by
        rw [Fin.cons_self_tail]
        exact checked)
      lifts := fun _ checked => eliminate_complete checked
    }

/-- Exact elimination and rational back-substitution. A negative result
refutes every assignment to the original coordinates. -/
def solve : {n : ℕ} → (rows : List (Inequality n)) → Result rows
  | 0, rows => by
      by_cases constants : ∀ row ∈ rows, 0 ≤ row.bound
      · exact .feasible Fin.elim0 (fun row listed => by
          simpa only [Inequality.Holds, dot, Finset.univ_eq_empty, Finset.sum_empty] using constants row listed)
      · exact .infeasible (fun ⟨values, feasible⟩ => constants (fun row listed => by
          simpa only [Inequality.Holds, dot, Finset.univ_eq_empty, Finset.sum_empty] using feasible row listed))
  | n + 1, rows =>
      let reduction := reduce rows
      match solve reduction.system with
      | .feasible values checked => .feasible (Fin.cons (reduction.head values) values) (reduction.lifts values checked)
      | .infeasible impossible => .infeasible fun ⟨values, checked⟩ =>
          impossible ⟨Fin.tail values, reduction.projects values checked⟩

def Result.isFeasible {rows : List (Inequality n)} : Result rows → Bool
  | .feasible _ _ => true
  | .infeasible _ => false

theorem solve_feasible_iff (rows : List (Inequality n)) :
    (solve rows).isFeasible = true ↔ ∃ values, Feasible rows values := by
  cases solve rows with
  | feasible values checked => exact iff_of_true rfl ⟨values, checked⟩
  | infeasible impossible =>
      change false = true ↔ _
      exact iff_of_false (by decide) impossible

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
