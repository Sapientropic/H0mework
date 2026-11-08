import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Eliminate
import Mathlib.Data.List.MinMax

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

variable {n : ℕ}

/-- Original singleton bounds determine this coordinate in every feasible
assignment. The chosen value may be any rational. -/
structure Pin (rows : List (Inequality (n + 1))) where
  value : ℚ
  determined : ∀ values, Feasible rows values → values 0 = value

private def onHead (row : Inequality (n + 1)) : Bool :=
  (List.finRange n).all fun i => decide (row.tail.coeff i = 0)

private theorem onHead_eval (row : Inequality (n + 1)) (single : onHead row = true)
    (values : Fin n → ℚ) : dot row.tail.coeff values = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have absent := of_decide_eq_true ((List.all_eq_true.mp single) i (List.mem_finRange i))
  rw [absent, zero_mul]

private def axisValue (row : Inequality (n + 1)) : ℚ := row.bound / row.coeff 0

private def matched_axes_pin
    {rows : List (Inequality (n + 1))} {low high : Inequality (n + 1)}
    (lower : low ∈ lowerRows (rows.filter onHead)) (upper : high ∈ upperRows (rows.filter onHead))
    (same : axisValue low = axisValue high) : Pin rows := by
  refine ⟨axisValue low, ?_⟩
  intro values original
  obtain ⟨lowListed, negative⟩ := mem_lowerRows.mp lower
  obtain ⟨highListed, positive⟩ := mem_upperRows.mp upper
  obtain ⟨lowOriginal, lowOnly⟩ := List.mem_filter.mp lowListed
  obtain ⟨highOriginal, highOnly⟩ := List.mem_filter.mp highListed
  have lowerFits : low.Holds (Fin.cons (values 0) (Fin.tail values)) := by
    rw [Fin.cons_self_tail]
    exact original low lowOriginal
  have upperFits : high.Holds (Fin.cons (values 0) (Fin.tail values)) := by
    rw [Fin.cons_self_tail]
    exact original high highOriginal
  have atLeast : axisValue low ≤ values 0 := by
    simpa only [Inequality.boundAt, onHead_eval low lowOnly, sub_zero, axisValue] using
      (holds_lower low (values 0) (Fin.tail values) negative).mp lowerFits
  have atMost : values 0 ≤ axisValue high := by
    simpa only [Inequality.boundAt, onHead_eval high highOnly, sub_zero, axisValue] using
      (holds_upper high (values 0) (Fin.tail values) positive).mp upperFits
  exact le_antisymm (atMost.trans_eq same.symm) atLeast

/-- A recognized equality can be substituted directly before generating
the lower/upper cross product. Nonmatching bounds use ordinary elimination. -/
def findPin (rows : List (Inequality (n + 1))) : Option (Pin rows) :=
  let axes := rows.filter onHead
  match lower : (lowerRows axes).argmax axisValue, upper : (upperRows axes).argmin axisValue with
  | some low, some high =>
    if same : axisValue low = axisValue high then
      some (matched_axes_pin (List.argmax_mem (Option.mem_def.mpr lower))
        (List.argmin_mem (Option.mem_def.mpr upper)) same)
    else none
  | _, _ => none

def Inequality.substitute (row : Inequality (n + 1)) (value : ℚ) : Inequality n :=
  ⟨row.tail.coeff, row.bound - row.coeff 0 * value⟩

def substitute (rows : List (Inequality (n + 1))) (value : ℚ) : List (Inequality n) :=
  rows.map fun row => row.substitute value

private theorem substitute_holds (row : Inequality (n + 1)) (value : ℚ) (values : Fin n → ℚ) :
    (row.substitute value).Holds values ↔ row.Holds (Fin.cons value values) := by
  simp only [Inequality.Holds, Inequality.substitute, Inequality.tail, dot, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, le_sub_iff_add_le]
  rw [add_comm]

theorem substitute_iff (rows : List (Inequality (n + 1))) (value : ℚ) (values : Fin n → ℚ) :
    Feasible (substitute rows value) values ↔ Feasible rows (Fin.cons value values) := by
  constructor
  · intro projected row original
    exact (substitute_holds row value values).mp
      (projected _ (List.mem_map.mpr ⟨row, original, rfl⟩))
  · intro original row listed
    obtain ⟨before, originalMem, rfl⟩ := List.mem_map.mp listed
    exact (substitute_holds before value values).mpr (original before originalMem)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
