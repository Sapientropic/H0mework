import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Solve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

structure Tagged (Label : Type*) (n : ℕ) where
  label : Label
  inequality : Inequality n

variable {Label : Type*} {n : ℕ}

def numeric (rows : List (Tagged Label n)) : List (Inequality n) :=
  rows.map Tagged.inequality

/-- A feasible assignment for the exact preceding prefix and a refutation
of all assignments after adding the original constraint at `position`. -/
structure Conflict (rows : List (Tagged Label n)) where
  position : Fin rows.length
  witness : Fin n → ℚ
  prior : Feasible (numeric (rows.take position.val)) witness
  impossible : ¬ ∃ values, Feasible (numeric (rows.take (position.val + 1))) values

def Conflict.failed {rows : List (Tagged Label n)} (failure : Conflict rows) : Tagged Label n :=
  rows.get failure.position

def Conflict.label {rows : List (Tagged Label n)} (failure : Conflict rows) : Label :=
  failure.failed.label

theorem Conflict.failed_is_original {rows : List (Tagged Label n)} (failure : Conflict rows) :
    failure.failed ∈ rows :=
  List.get_mem _ _

private theorem feasible_take {rows : List (Tagged Label n)} {values : Fin n → ℚ}
    (whole : Feasible (numeric rows) values) (cut : ℕ) :
    Feasible (numeric (rows.take cut)) values := by
  intro inequality present
  obtain ⟨row, listed, rfl⟩ := List.mem_map.mp present
  exact whole _ (List.mem_map.mpr ⟨row, List.mem_of_mem_take listed, rfl⟩)

theorem Conflict.earlier_fits {rows : List (Tagged Label n)} (failure : Conflict rows)
    (cut : ℕ) (earlier : cut ≤ failure.position.val) :
    Feasible (numeric (rows.take cut)) failure.witness := by
  simpa only [List.take_take, min_eq_left earlier] using feasible_take failure.prior cut

theorem Conflict.refutes {rows : List (Tagged Label n)} (failure : Conflict rows) :
    ¬ ∃ values, Feasible (numeric rows) values := by
  rintro ⟨values, whole⟩
  exact failure.impossible ⟨values, feasible_take whole _⟩

theorem Conflict.later_impossible {rows : List (Tagged Label n)} (failure : Conflict rows)
    (cut : ℕ) (later : failure.position.val < cut) :
    ¬ ∃ values, Feasible (numeric (rows.take cut)) values := by
  rintro ⟨values, checked⟩
  apply failure.impossible
  refine ⟨values, ?_⟩
  simpa only [List.take_take, min_eq_left (Nat.succ_le_of_lt later)] using
    feasible_take checked (failure.position.val + 1)

theorem Conflict.first_row_rules_out_every_prefix_assignment
    {rows : List (Tagged Label n)} (failure : Conflict rows) {values : Fin n → ℚ}
    (checked : Feasible (numeric (rows.take failure.position.val)) values) :
    ¬ failure.failed.inequality.Holds values := by
  intro fits
  apply failure.impossible
  refine ⟨values, ?_⟩
  intro inequality listed
  rw [← List.take_concat_get failure.position.isLt] at listed
  unfold numeric at listed
  rw [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil] at listed
  rcases List.mem_append.mp listed with earlier | last
  · exact checked _ earlier
  · have same := List.mem_singleton.mp last
    rw [same]
    exact fits

inductive Diagnosis (rows : List (Tagged Label n)) where
  | feasible (values : Fin n → ℚ) (checked : Feasible (numeric rows) values)
  | blocked (failure : Conflict rows)

private def narrow (rows : List (Tagged Label n)) (lower upper : ℕ)
    (separated : lower < upper) (within : upper ≤ rows.length)
    (values : Fin n → ℚ) (checked : Feasible (numeric (rows.take lower)) values)
    (impossible : ¬ ∃ values, Feasible (numeric (rows.take upper)) values) : Conflict rows :=
  if adjacent : upper = lower + 1 then
    ⟨⟨lower, separated.trans_le within⟩, values, checked, adjacent ▸ impossible⟩
  else
    let middle := (lower + upper) / 2
    have above : lower < middle := by dsimp [middle]; omega
    have below : middle < upper := by dsimp [middle]; omega
    match solve (numeric (rows.take middle)) with
    | .feasible next fits => narrow rows middle upper below within next fits impossible
    | .infeasible blocked => narrow rows lower middle above (below.le.trans within) values checked blocked
termination_by upper - lower
decreasing_by all_goals omega

/-- Reuse a rejection of the same numerical system when the caller has
already performed the full solve. The prefix and named row are computed. -/
def conflictOfInfeasible (rows : List (Tagged Label n))
    (impossible : ¬ ∃ values, Feasible (numeric rows) values) : Conflict rows :=
  have nonempty : 0 < rows.length := by
    cases rows with
    | nil => exact (impossible ⟨fun _ => 0, by simp [numeric, Feasible]⟩).elim
    | cons _ _ => simp
  narrow rows 0 rows.length nonempty le_rfl (fun _ => 0)
    (by simp [numeric, Feasible]) (by simpa only [List.take_length] using impossible)

/-- Inspect the complete original system once. A blocked system is then
bisected on prefixes, keeping a concrete earlier feasible assignment. -/
def diagnose (rows : List (Tagged Label n)) : Diagnosis rows :=
  match solve (numeric rows) with
  | .feasible values checked => .feasible values checked
  | .infeasible impossible => .blocked (conflictOfInfeasible rows impossible)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics
