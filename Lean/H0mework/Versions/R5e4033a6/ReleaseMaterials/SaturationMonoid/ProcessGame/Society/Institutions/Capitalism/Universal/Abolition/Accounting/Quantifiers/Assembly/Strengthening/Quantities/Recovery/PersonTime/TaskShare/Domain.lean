import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare.Cells

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare

open Intervals
open SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

variable {Task : Type*} [Fintype Task] [DecidableEq Task]

/-- Every personal clock cell is distributed exactly once, among the
original tasks actually occupied in that cell. -/
def Allocates (log : Log Task) (allocation : Task → Cell log → ℚ) : Prop :=
  (network log).Admissible allocation ∧
    ∀ cell, Network.columnTotal allocation cell = width log cell

theorem the_total_task_charges_equal_personal_hours (log : Log Task) (allocation : Task → Cell log → ℚ)
    (paid : Allocates log allocation) :
    (∑ task, Network.rowTotal allocation task) = length (allSpans log) := by
  unfold Network.rowTotal
  rw [Finset.sum_comm]
  change (∑ cell, Network.columnTotal allocation cell) = _
  rw [← all_cell_widths_equal_the_personal_union log]
  exact Finset.sum_congr rfl (fun cell _ => paid.2 cell)

theorem conserving_the_total_pays_each_original_cell (log : Log Task) (allocation : Task → Cell log → ℚ)
    (admitted : (network log).Admissible allocation)
    (total : (∑ task, Network.rowTotal allocation task) = length (allSpans log)) :
    Allocates log allocation := by
  refine ⟨admitted, ?_⟩
  have totalColumns : (∑ cell, Network.columnTotal allocation cell) = ∑ cell, width log cell := by
    rw [all_cell_widths_equal_the_personal_union log, ← total]
    exact Finset.sum_comm
  intro cell
  apply le_antisymm (admitted.2.2 cell)
  by_contra! deficit
  have tooSmall : (∑ cell, Network.columnTotal allocation cell) < ∑ cell, width log cell :=
    Finset.sum_lt_sum (fun item _ => admitted.2.2 item) ⟨cell, Finset.mem_univ _, deficit⟩
  exact (lt_irrefl _) (totalColumns ▸ tooSmall)

theorem fully_distributed_hours_iff_original_task_group_cuts (log : Log Task) (charges : Task → ℚ) :
    (∃ allocation, Allocates log allocation ∧ ∀ task, Network.rowTotal allocation task = charges task) ↔
    (∀ task, 0 ≤ charges task ∧ charges task ≤ full log task) ∧
      (∑ task, charges task) = length (allSpans log) ∧
      ∀ group : Finset Task, (∑ task ∈ group, charges task) ≤ (network log).supplyOf ((network log).neighbours group) := by
  constructor
  · rintro ⟨allocation, paid, exactRow⟩
    obtain ⟨limits, cuts⟩ := ((network log).exact_profile_iff_original_group_bounds charges).mp
      ⟨allocation, paid.1, exactRow⟩
    have balance := the_total_task_charges_equal_personal_hours log allocation paid
    exact ⟨limits, by simpa only [exactRow] using balance, cuts⟩
  · rintro ⟨limits, total, cuts⟩
    obtain ⟨allocation, admitted, exactRow⟩ :=
      ((network log).exact_profile_iff_original_group_bounds charges).mpr ⟨limits, cuts⟩
    exact ⟨allocation, conserving_the_total_pays_each_original_cell log allocation admitted
      (by simpa only [exactRow] using total), exactRow⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare
