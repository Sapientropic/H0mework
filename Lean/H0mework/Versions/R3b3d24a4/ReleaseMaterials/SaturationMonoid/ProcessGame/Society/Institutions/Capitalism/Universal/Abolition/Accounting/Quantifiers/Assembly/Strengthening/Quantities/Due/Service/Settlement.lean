import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Incidence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

def OriginalDemands (ids : Finset TaskId) (task : TaskId → Task) : Prop :=
  ∀ slot : Slot ids task, NonnegativeBundle Good slot.spec.goods

instance (ids : Finset TaskId) (task : TaskId → Task) : Decidable (OriginalDemands ids task) := by
  unfold OriginalDemands
  infer_instance

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq TaskId] in
theorem a_malformed_task_exposes_its_original_negative_lot (ids : Finset TaskId) (task : TaskId → Task)
    (bad : ¬ OriginalDemands ids task) :
    ∃ (slot : Slot ids task) (lot : Good × ℚ), lot ∈ slot.spec.goods ∧ lot.2 < 0 := by
  classical
  unfold OriginalDemands NonnegativeBundle at bad
  push Not at bad
  exact bad

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)}
  {script : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ids : Finset TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Ordinal source script)}

local notation "Net" => network source script ids task reserved

/-- Read the unpaid quantity at the original task, slot and material address. -/
def remaining (receipt : (Net).Certificate) (line : Need ids task) : ℚ :=
  (Net).need line - Network.rowTotal receipt.allocation line

omit [DecidableEq TaskId] in
theorem allocated_and_remaining_are_the_original_quantity
    (receipt : (Net).Certificate) (line : Need ids task)
    (original : OriginalDemands ids task) :
    0 ≤ remaining receipt line ∧
      Network.rowTotal receipt.allocation line + remaining receipt line =
        amount Good line.1.spec.goods line.2.val := by
  have amount := network_reads_nonnegative_original_need source script ids task reserved line (original line.1)
  unfold remaining
  exact ⟨sub_nonneg.mpr (receipt.admitted.2.1 line), by rw [add_sub_cancel, amount]⟩

omit [DecidableEq TaskId] in
theorem a_positive_fragment_is_an_original_signed_use_in_its_window
    (receipt : (Net).Certificate) (line : Need ids task) (item : Supply source script ids task)
    (positive : 0 < receipt.allocation line item) :
    accepts source script reserved line item := by
  apply (network_allows_iff source script ids task reserved line item).mp
  cases allowed : (Net).allows line item
  · exact (positive.ne' ((receipt.admitted.1 line item).2 allowed)).elim
  · rfl

omit [DecidableEq TaskId] in
theorem reserved_original_uses_cannot_be_spent_on_fragments
    (receipt : (Net).Certificate) (line : Need ids task) (item : Supply source script ids task)
    (booked : item.1 ∈ reserved) :
    receipt.allocation line item = 0 := by
  have nonnegative := (receipt.admitted.1 line item).1
  rcases eq_or_lt_of_le nonnegative with zero | positive
  · exact zero.symm
  · exact ((a_positive_fragment_is_an_original_signed_use_in_its_window receipt line item positive).1 booked).elim

/-- Source and service outcomes retain the same submitted script.
A collective shortage carries a maximum allocation and its named original cut. -/
inductive Outcome (receipt : (Net).Certificate) where
  | paid (original : OriginalDemands ids task) (settled : Settled source script)
      (complete : (Net).Complete receipt.allocation)
  | malformed (bad : ¬ OriginalDemands ids task)
  | nativeBlocked (issue : Obstruction source script)
  | shortage (positive : 0 < (Net).gap receipt.group)

/-- A checked allocation acquires settlement only through the actual native
fold, including its original pending work and whole-ledger successor. -/
def finalize (receipt : (Net).Certificate) : Outcome receipt :=
  if original : OriginalDemands ids task then
    if shortage : 0 < (Net).gap receipt.group then .shortage shortage
    else match decideAt source script with
      | .blocked issue => .nativeBlocked issue
      | .feasible paid => .paid original (settle source script paid)
          (receipt.complete_or_original_shortage.resolve_right (fun positive => shortage (sub_pos.mpr positive)))
  else .malformed original

theorem a_shortage_rules_out_every_complete_allocation_of_this_execution
    (receipt : (Net).Certificate) (positive : 0 < (Net).gap receipt.group)
    (other : Need ids task → Supply source script ids task → ℚ) :
    ¬ (Net).Complete other := by
  intro paid
  have bounded := (Net).allocation_is_bounded_by_every_original_cut paid.1 receipt.group
  have full := ((Net).full_quantity_iff_total_is_exact paid.1).mp paid
  unfold Network.cut at bounded
  linarith only [bounded, full, positive]

theorem the_amount_and_shortage_share_the_original_rows_and_next
    (receipt : (Net).Certificate) :
    Recorded source script ∧
      (∀ row : Execution.RowAt source,
        (Execution.rowAt source script row).claim = Execution.claimAt source script row.claim ∧
          (Execution.rowAt source script row).progressBudget ≤ row.progressBudget) ∧
      (∀ other, (Net).Admissible other → Network.total other ≤ Network.total receipt.allocation) ∧
      (∀ group, (Net).gap group ≤ (Net).gap receipt.group) ∧
      Network.total receipt.allocation + (Net).gap receipt.group = (Net).demandOf Finset.univ :=
  ⟨record source script, Execution.rowAt_exact source script, receipt.optimal⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service
