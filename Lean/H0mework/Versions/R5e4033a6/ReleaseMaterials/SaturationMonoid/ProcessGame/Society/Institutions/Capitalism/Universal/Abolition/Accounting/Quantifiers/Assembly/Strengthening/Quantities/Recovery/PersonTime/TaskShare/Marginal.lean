import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare.Domain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare

open SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

variable {Task : Type*} [Fintype Task] [DecidableEq Task]

def Sole (log : Log Task) (task : Task) (cell : Cell log) : Prop :=
  ∀ other, allows log other cell = true → other = task

instance (log : Log Task) (task : Task) (cell : Cell log) : Decidable (Sole log task cell) := by
  unfold Sole
  infer_instance

def exclusive (log : Log Task) (task : Task) : ℚ :=
  ∑ cell, if Sole log task cell then width log cell else 0

theorem every_task_charge_lies_between_its_sole_and_full_occupation (log : Log Task)
    (allocation : Task → Cell log → ℚ) (paid : Allocates log allocation) (task : Task) :
    exclusive log task ≤ Network.rowTotal allocation task ∧ Network.rowTotal allocation task ≤ full log task := by
  refine ⟨Finset.sum_le_sum fun cell _ => ?_, paid.1.2.1 task⟩
  by_cases sole : Sole log task cell
  · have onlyTask : Network.columnTotal allocation cell = allocation task cell := by
      unfold Network.columnTotal
      rw [Finset.sum_eq_single task]
      · intro other _ different
        apply (paid.1.1 other cell).2
        cases edge : allows log other cell
        · exact edge
        · exact (different (sole other edge)).elim
      · simp
    rw [if_pos sole, ← onlyTask, paid.2]
  · rw [if_neg sole]
    exact (paid.1.1 task cell).1

private def assignWhole (log : Log Task) (select : Cell log → Task) (task : Task) (cell : Cell log) : ℚ :=
  if task = select cell then width log cell else 0

private theorem assigning_each_cell_to_its_own_task_pays_the_entire_union
    (log : Log Task) (select : Cell log → Task) (eligible : ∀ cell, allows log (select cell) cell = true) :
    Allocates log (assignWhole log select) := by
  have column (cell : Cell log) : Network.columnTotal (assignWhole log select) cell = width log cell := by
    unfold Network.columnTotal
    rw [Finset.sum_eq_single (select cell)]
    · simp [assignWhole]
    · intro other _ different
      simp [assignWhole, different]
    · simp
  refine ⟨⟨?_, ?_, fun cell => (column cell).le⟩, column⟩
  · intro task cell
    by_cases chosen : task = select cell
    · subst task
      refine ⟨by simpa [assignWhole] using width_nonnegative log cell, fun impossible => ?_⟩
      change allows log (select cell) cell = false at impossible
      rw [eligible] at impossible
      cases impossible
    · simp [assignWhole, chosen]
  · intro task
    apply Finset.sum_le_sum
    intro cell _
    by_cases chosen : task = select cell
    · subst task
      simp [assignWhole, eligible]
    · simp only [assignWhole, if_neg chosen]
      split <;> first | exact width_nonnegative log cell | exact le_rfl

theorem the_full_task_charge_is_attained (log : Log Task) (task : Task) :
    ∃ allocation, Allocates log allocation ∧ Network.rowTotal allocation task = full log task := by
  classical
  let select (cell : Cell log) : Task :=
    if allows log task cell then task else Classical.choose (some_original_task_occupies_each_cell log cell)
  have eligible (cell : Cell log) : allows log (select cell) cell = true := by
    unfold select
    split
    · assumption
    · exact Classical.choose_spec (some_original_task_occupies_each_cell log cell)
  refine ⟨assignWhole log select, assigning_each_cell_to_its_own_task_pays_the_entire_union log select eligible, ?_⟩
  apply Finset.sum_congr rfl
  intro cell _
  by_cases can : allows log task cell = true
  · simp [assignWhole, select, can]
  · have different : task ≠ select cell := fun same => can (same ▸ eligible cell)
    simp [assignWhole, different, can]

theorem the_sole_task_charge_is_attained (log : Log Task) (task : Task) :
    ∃ allocation, Allocates log allocation ∧ Network.rowTotal allocation task = exclusive log task := by
  classical
  let alternate (cell : Cell log) := ∃ other, allows log other cell = true ∧ other ≠ task
  let select (cell : Cell log) : Task :=
    if existsOther : alternate cell then Classical.choose existsOther
    else Classical.choose (some_original_task_occupies_each_cell log cell)
  have eligible (cell : Cell log) : allows log (select cell) cell = true := by
    unfold select
    split
    · rename_i existsOther
      exact (Classical.choose_spec existsOther).1
    · exact Classical.choose_spec (some_original_task_occupies_each_cell log cell)
  refine ⟨assignWhole log select, assigning_each_cell_to_its_own_task_pays_the_entire_union log select eligible, ?_⟩
  apply Finset.sum_congr rfl
  intro cell _
  by_cases sole : Sole log task cell
  · have chosen : task = select cell := (sole _ (eligible cell)).symm
    rw [assignWhole, if_pos chosen, if_pos sole]
  · have existsOther : alternate cell := by
      obtain ⟨other, differs⟩ := not_forall.mp sole
      exact ⟨other, Classical.not_imp.mp differs⟩
    have different : task ≠ select cell := by
      unfold select
      rw [dif_pos existsOther]
      exact (Classical.choose_spec existsOther).2.symm
    simp [assignWhole, different, sole]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare
