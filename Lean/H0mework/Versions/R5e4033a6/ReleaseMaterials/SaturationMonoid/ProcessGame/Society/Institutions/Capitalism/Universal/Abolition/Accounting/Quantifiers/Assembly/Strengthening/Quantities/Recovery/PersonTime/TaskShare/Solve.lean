import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare.Domain
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Solver
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare

open Intervals
open SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

variable {Task : Type*} [Fintype Task] [DecidableEq Task]

private def cellKeys (log : Log Task) : List (Cell log) :=
  ((activeCells log).sort (· ≤ ·)).attach.map
    fun entry => ⟨entry.val, (Finset.mem_sort (r := (· ≤ ·))).mp entry.property⟩

omit [Fintype Task] [DecidableEq Task] in
private theorem every_cell_is_listed (log : Log Task) (cell : Cell log) : cell ∈ cellKeys log := by
  let listed : {point // point ∈ (activeCells log).sort (· ≤ ·)} :=
    ⟨cell.val, (Finset.mem_sort (r := (· ≤ ·))).mpr cell.property⟩
  exact List.mem_map.mpr ⟨listed, List.mem_attach _ _, Subtype.ext rfl⟩

inductive Decision (log : Log Task) (charges : Task → ℚ)
  | paid (allocation : Task → Cell log → ℚ) (cells : Allocates log allocation)
      (tasks : ∀ task, Network.rowTotal allocation task = charges task)
  | invalidTask (task : Task) (invalid : charges task < 0 ∨ full log task < charges task)
  | differentTotal (difference : (∑ task, charges task) ≠ length (allSpans log))
  | competingTasks (group : Finset Task) (short : (network log).supplyOf ((network log).neighbours group) <
      ∑ task ∈ group, charges task)

/-- The original finite quantity solver pays a submitted task-charge
profile or identifies the exact original task, total or group cut
that prevents its payment. -/
def solve (log : Log Task) (charges : Task → ℚ) (tasks : List Task) (allTasks : ∀ task, task ∈ tasks) :
    Decision log charges :=
  let invalid := fun task => decide (charges task < 0 ∨ full log task < charges task)
  match bad : tasks.find? invalid with
  | some task =>
    have found : invalid task = true := List.find?_some (p := invalid) bad
    .invalidTask task (of_decide_eq_true found)
  | none =>
    have bounds (task : Task) : 0 ≤ charges task ∧ charges task ≤ full log task := by
      have valid := List.find?_eq_none.mp bad task (allTasks task)
      dsimp only [invalid] at valid
      have ok : ¬ (charges task < 0 ∨ full log task < charges task) := fun outside => valid (decide_eq_true outside)
      exact ⟨le_of_not_gt (fun negative => ok (.inl negative)), le_of_not_gt (fun excess => ok (.inr excess))⟩
    if total : (∑ task, charges task) = length (allSpans log) then
      let request : Network Task (Cell log) :=
        { network log with need := charges, need_nonnegative := fun task => (bounds task).1 }
      let certificate := request.solveListed tasks (cellKeys log) allTasks (every_cell_is_listed log)
      haveI : Decidable (request.Complete certificate.allocation) := by
        unfold Network.Complete
        infer_instance
      if paid : request.Complete certificate.allocation then
        have admitted : (network log).Admissible certificate.allocation :=
          ⟨paid.1.1, fun task => (paid.2 task).le.trans (bounds task).2, paid.1.2.2⟩
        .paid certificate.allocation (conserving_the_total_pays_each_original_cell log certificate.allocation admitted
          (by simpa only [show ∀ task, Network.rowTotal certificate.allocation task = charges task from paid.2] using total))
          paid.2
      else
        .competingTasks certificate.group (certificate.complete_or_original_shortage.resolve_left paid)
    else .differentTotal total

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare
