import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Profile
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.NativeHolding
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Deadline.Capacity

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

def stockView (source : C) (script : Script) (ids : Finset TaskId) (task : TaskId → Task) :
    Liquidity.Profile (Party × Good) (Service.Need ids task) (Service.Ordinal source script) :=
  Liquidity.profile source script address deadline (fun _ => 0) (fun _ _ => 0)

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)}
  {script : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ids : Finset TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Service.Ordinal source script)}
  {allocation : Service.Need ids task → Service.Supply source script ids task → ℚ}

local notation "Net" => Service.network source script ids task reserved
local notation "View" => profile source script ids task reserved allocation
local notation "Stock" => stockView source script ids task

theorem timely_full_service_clears_due_quantities_through_the_same_cut
    (admitted : (Net).Admissible allocation) {horizon : ℚ}
    (paid : ∀ line, deadline line ≤ horizon → Network.rowTotal allocation line = (Net).need line)
    (time : ℚ) (within : time ≤ horizon) (key : Party × Good) :
    (View).outstandingDue time key = 0 ∧ (View).pastDue time key = 0 := by
  have zero (line : Service.Need ids task) (mature : deadline line ≤ time) :
      (View).required line - (View).paidThrough time line = 0 := by
    change (Net).need line - (View).paidThrough time line = 0
    rw [the_original_timed_payments_sum_to_the_same_due_allocation admitted line time mature,
      paid line (mature.trans within), sub_self]
  constructor
  · unfold Liquidity.Profile.outstandingDue
    apply Finset.sum_eq_zero
    intro line _
    split
    · rename_i current
      exact zero line current.2
    · rfl
  · unfold Liquidity.Profile.pastDue
    apply Finset.sum_eq_zero
    intro line _
    split
    · rename_i current
      exact zero line current.2.le
    · rfl

theorem the_stock_view_has_no_due_rows (time : ℚ) (key : Party × Good) :
    (Stock).outstandingDue time key = 0 ∧ (Stock).pastDue time key = 0 := by
  have noPayment (line : Service.Need ids task) : (Stock).paidThrough time line = 0 := by
    unfold Liquidity.Profile.paidThrough
    apply Finset.sum_eq_zero
    intro item _
    split <;> rfl
  constructor
  · unfold Liquidity.Profile.outstandingDue
    apply Finset.sum_eq_zero
    intro line _
    rw [noPayment line]
    split
    · exact sub_self (0 : ℚ)
    · rfl
  · unfold Liquidity.Profile.pastDue
    apply Finset.sum_eq_zero
    intro line _
    rw [noPayment line]
    split
    · exact sub_self (0 : ℚ)
    · rfl

/-- Once the original due prefix is actually served, the reserve checks
reduce to that same physical ledger before and after its commits. -/
theorem timely_service_uses_the_same_tight_stock_reserve
    (admitted : (Net).Admissible allocation) {horizon : ℚ}
    (paid : ∀ line, deadline line ≤ horizon → Network.rowTotal allocation line = (Net).need line)
    (key : Party × Good) (additional : ℚ) :
    (View).rollingReserveThrough (Liquidity.beforeStock source script) horizon key ≤ additional ↔
      (Stock).rollingReserveThrough (Liquidity.beforeStock source script) horizon key ≤ additional := by
  rw [Liquidity.Profile.rollingReserveThrough_fits_iff, Liquidity.Profile.rollingReserveThrough_fits_iff]
  have sameAfter (time : ℚ) (within : time ≤ horizon) : (View).gap time key = (Stock).gap time key := by
    unfold Liquidity.Profile.gap
    rw [(timely_full_service_clears_due_quantities_through_the_same_cut admitted paid time within key).1,
      (the_stock_view_has_no_due_rows (source := source) (script := script) (ids := ids) (task := task) time key).1]
    rfl
  have sameBefore (item : Service.Ordinal source script) (within : (View).commit item ≤ horizon) :
      (View).pastDue ((View).commit item) key = (Stock).pastDue ((Stock).commit item) key :=
    (timely_full_service_clears_due_quantities_through_the_same_cut admitted paid _ within key).2.trans
      (the_stock_view_has_no_due_rows _ key).2.symm
  constructor
  · rintro ⟨nonnegative, after, before⟩
    refine ⟨nonnegative, fun time start within => (sameAfter time within) ▸ after time start within, ?_⟩
    intro item within
    have fit := before item within
    rw [sameBefore item within] at fit
    exact fit
  · rintro ⟨nonnegative, after, before⟩
    refine ⟨nonnegative, fun time start within => (sameAfter time within).symm ▸ after time start within, ?_⟩
    intro item within
    have fit := before item within
    rw [← sameBefore item within] at fit
    exact fit

/-- Simultaneous service and stock safety, with one selected allocation on
the original material execution. -/
def JointThrough (source : C) (script : Script) (ids : Finset TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script))
    (watch : List (Party × Good)) (additional : Party × Good → ℚ) (horizon : ℚ) : Prop :=
  ∃ allocation, (Service.network source script ids task reserved).Admissible allocation ∧
    (∀ line, deadline line ≤ horizon →
      Network.rowTotal allocation line = (Service.network source script ids task reserved).need line) ∧
    ∀ key ∈ watch,
      (profile source script ids task reserved allocation).rollingReserveThrough
        (Liquidity.beforeStock source script) horizon key ≤ additional key

theorem the_joint_due_domain_is_exactly_the_original_service_and_stock_domain
    (source : C) (script : Script) (ids : Finset TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) (watch : List (Party × Good))
    (additional : Party × Good → ℚ) (horizon : ℚ) :
    JointThrough source script ids task reserved watch additional horizon ↔
      Deadline.ServedThrough (Service.network source script ids task reserved) deadline horizon ∧
        ∀ key ∈ watch, (stockView source script ids task).rollingReserveThrough
          (Liquidity.beforeStock source script) horizon key ≤ additional key := by
  constructor
  · rintro ⟨chosen, admitted, paid, reserve⟩
    refine ⟨⟨chosen, admitted, fun line due => paid line (of_decide_eq_true due)⟩, fun key present => ?_⟩
    exact (timely_service_uses_the_same_tight_stock_reserve admitted paid key (additional key)).mp (reserve key present)
  · rintro ⟨⟨chosen, admitted, served⟩, reserve⟩
    have paid := fun line due => served line (decide_eq_true due)
    refine ⟨chosen, admitted, paid, fun key present => ?_⟩
    exact (timely_service_uses_the_same_tight_stock_reserve admitted paid key (additional key)).mpr (reserve key present)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement
