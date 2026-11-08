import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Projection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

variable {n : ℕ}

inductive Minimum (rows : List (Inequality (n + 1))) where
  | empty (impossible : ¬ ∃ values, Feasible rows values)
  | attained (values : Fin (n + 1) → ℚ) (checked : Feasible rows values)
      (least : ∀ other, Feasible rows other → values (Fin.last n) ≤ other (Fin.last n))
  | unboundedBelow (lower : (limit : ℚ) →
      { values : Fin (n + 1) → ℚ // Feasible rows values ∧ values (Fin.last n) < limit })

private theorem singleton_cons (value : ℚ) :
    Fin.cons value Fin.elim0 = (fun _ : Fin 1 => value) := by
  funext i
  have zero : i = 0 := Fin.ext (by
    have bounded := i.isLt
    omega)
  rw [zero, Fin.cons_zero]

private theorem singleton_value (values : Fin 1 → ℚ) : (fun _ => values 0) = values := by
  funext i
  apply congrArg values
  apply Fin.ext
  have bounded := i.isLt
  omega

private theorem with_no_lower_row {rows : List (Inequality 1)} {current earlier : ℚ}
    (feasible : Feasible rows (fun _ => current)) (noLower : lowerRows rows = [])
    (moves : earlier ≤ current) : Feasible rows (fun _ => earlier) := by
  intro row original
  rw [← singleton_cons]
  have holds : row.Holds (Fin.cons current Fin.elim0) := singleton_cons current ▸ feasible row original
  rcases lt_trichotomy (row.coeff 0) 0 with negative | zero | positive
  · have inside := (mem_lowerRows (rows := rows)).mpr ⟨original, negative⟩
    rw [noLower] at inside
    exact (List.not_mem_nil inside).elim
  · exact (holds_zero row _ _ zero).mpr ((holds_zero row _ _ zero).mp holds)
  · exact (holds_upper row _ _ positive).mpr (moves.trans ((holds_upper row _ _ positive).mp holds))

private theorem selected_lower_value (rows : List (Inequality 1)) (lower : Inequality 1)
    (selected : (lowerRows rows).argmax (fun row => row.boundAt Fin.elim0) = some lower) :
    chooseHead rows Fin.elim0 = lower.boundAt Fin.elim0 := by
  unfold chooseHead
  dsimp only
  rw [selected]

/-- Optimize the last original coordinate over every feasible assignment.
Any finite lower endpoint is attained, since the original rows are weak
inequalities over the rationals. -/
def minimumLast (rows : List (Inequality (n + 1))) : Minimum rows :=
  let projection := projectLast n rows
  match solve projection with
  | .infeasible impossible => .empty fun ⟨values, checked⟩ =>
      impossible ⟨_, projectLast_sound n rows values checked⟩
  | .feasible sample accepted =>
    let read := fun row : Inequality 1 => row.boundAt Fin.elim0
    match selected : (lowerRows projection).argmax read with
    | none => .unboundedBelow fun limit =>
        let value := min (sample 0) (limit - 1)
        have fits : Feasible projection (fun _ => value) := with_no_lower_row
          ((singleton_value sample).symm ▸ accepted) (List.argmax_eq_none.mp selected) (min_le_left _ _)
        ⟨extendLast n rows value, extendLast_feasible n rows value fits, by
          rw [extendLast_keeps_value]
          exact (min_le_right _ _).trans_lt (sub_lt_self _ zero_lt_one)⟩
    | some lower =>
        let value := read lower
        have chosen : chooseHead projection Fin.elim0 = value :=
          selected_lower_value projection lower selected
        have rest : Feasible (eliminate projection) Fin.elim0 :=
          eliminate_sound (singleton_cons (sample 0) ▸ ((singleton_value sample).symm ▸ accepted))
        have fits : Feasible projection (fun _ => value) := by
          rw [← singleton_cons, ← chosen]
          exact eliminate_complete rest
        .attained (extendLast n rows value) (extendLast_feasible n rows value fits) (fun other original => by
          rw [extendLast_keeps_value]
          have inside := List.argmax_mem (Option.mem_def.mpr selected)
          obtain ⟨listed, negative⟩ := mem_lowerRows.mp inside
          have otherFits := (projectLast_sound n rows other original) lower listed
          rw [← singleton_cons] at otherFits
          exact (holds_lower lower _ _ negative).mp otherFits)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
