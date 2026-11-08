import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Native
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Settlement
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement

open scoped BigOperators
open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

def address {ids : Finset TaskId} {task : TaskId → Task} (line : Service.Need ids task) : Party × Good :=
  (line.1.spec.bearer, line.2.val)

def deadline {ids : Finset TaskId} {task : TaskId → Task} (line : Service.Need ids task) : ℚ :=
  (task line.1.1.val).deadline

def originalUnit {ids : Finset TaskId} {task : TaskId → Task} (line : Service.Need ids task) :
    { good // good ∈ Service.goods ids task } :=
  ⟨line.2.val, Finset.mem_biUnion.mpr ⟨line.1, Finset.mem_univ _, line.2.property⟩⟩

def paidAt {source : C} {script : Script} {ids : Finset TaskId} {task : TaskId → Task}
    (allocation : Service.Need ids task → Service.Supply source script ids task → ℚ)
    (line : Service.Need ids task) (ordinal : Service.Ordinal source script) : ℚ :=
  allocation line (ordinal, originalUnit line)

/-- Same original due rows, same material ordinals, and the allocation
selected by the original quantity solver. -/
def profile (source : C) (script : Script) (ids : Finset TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script))
    (allocation : Service.Need ids task → Service.Supply source script ids task → ℚ) :=
  Liquidity.profile source script address deadline (Service.network source script ids task reserved).need
    (paidAt allocation)

theorem a_positive_original_allocation_has_its_original_use {source : C} {script : Script}
    {ids : Finset TaskId} {task : TaskId → Task} {reserved : Finset (Service.Ordinal source script)}
    {allocation : Service.Need ids task → Service.Supply source script ids task → ℚ}
    (admitted : (Service.network source script ids task reserved).Admissible allocation)
    (line : Service.Need ids task) (item : Service.Supply source script ids task)
    (positive : 0 < allocation line item) : Service.accepts source script reserved line item := by
  apply (Service.network_allows_iff source script ids task reserved line item).mp
  cases allowed : (Service.network source script ids task reserved).allows line item
  · exact (positive.ne' ((admitted.1 line item).2 allowed)).elim
  · rfl

theorem only_the_original_unit_can_pay_its_due_row {source : C} {script : Script}
    {ids : Finset TaskId} {task : TaskId → Task} {reserved : Finset (Service.Ordinal source script)}
    {allocation : Service.Need ids task → Service.Supply source script ids task → ℚ}
    (admitted : (Service.network source script ids task reserved).Admissible allocation)
    (line : Service.Need ids task) (item : Service.Supply source script ids task)
    (other : item.2 ≠ originalUnit line) : allocation line item = 0 := by
  rcases eq_or_lt_of_le (admitted.1 line item).1 with zero | positive
  · exact zero.symm
  · exact (other (Subtype.ext (a_positive_original_allocation_has_its_original_use admitted line item positive).2.1.symm)).elim

theorem the_original_ordinals_sum_to_the_full_due_allocation {source : C} {script : Script}
    {ids : Finset TaskId} {task : TaskId → Task} {reserved : Finset (Service.Ordinal source script)}
    {allocation : Service.Need ids task → Service.Supply source script ids task → ℚ}
    (admitted : (Service.network source script ids task reserved).Admissible allocation)
    (line : Service.Need ids task) :
    (∑ ordinal : Service.Ordinal source script, paidAt allocation line ordinal) =
      Network.rowTotal allocation line := by
  unfold Network.rowTotal
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ordinal _
  symm
  apply Finset.sum_eq_single (originalUnit line)
  · intro good _ other
    exact only_the_original_unit_can_pay_its_due_row admitted line (ordinal, good) other
  · simp

theorem the_original_timed_payments_sum_to_the_same_due_allocation {source : C} {script : Script}
    {ids : Finset TaskId} {task : TaskId → Task} {reserved : Finset (Service.Ordinal source script)}
    {allocation : Service.Need ids task → Service.Supply source script ids task → ℚ}
    (admitted : (Service.network source script ids task reserved).Admissible allocation)
    (line : Service.Need ids task) (time : ℚ) (due : deadline line ≤ time) :
    (profile source script ids task reserved allocation).paidThrough time line =
      Network.rowTotal allocation line := by
  have timely (ordinal : Service.Ordinal source script) :
      (if (Execution.timedAt source script ordinal).2 ≤ time ∧
          (Execution.timedAt source script ordinal).2 ≤ deadline line
        then paidAt allocation line ordinal else 0) = paidAt allocation line ordinal := by
    rcases eq_or_lt_of_le (admitted.1 line (ordinal, originalUnit line)).1 with zero | positive
    · change 0 = paidAt allocation line ordinal at zero
      simp [← zero]
    · have inWindow :=
        (a_positive_original_allocation_has_its_original_use admitted line (ordinal, originalUnit line) positive).2.2.2.1
      exact if_pos ⟨inWindow.trans due, inWindow⟩
  change (∑ ordinal : Service.Ordinal source script,
    if (Execution.timedAt source script ordinal).2 ≤ time ∧
        (Execution.timedAt source script ordinal).2 ≤ deadline line
      then paidAt allocation line ordinal else 0) = Network.rowTotal allocation line
  simp_rw [timely]
  exact the_original_ordinals_sum_to_the_full_due_allocation admitted line

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement
