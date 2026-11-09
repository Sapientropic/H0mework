import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Allocate

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Reparation Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Row" => Reparation.Actual.Occurrence seed community × Balance
local notation "ClaimKey" => Key Party Good

private def dueWhere (read : ClaimKey → Prop) [DecidablePred read] (rows : List Row) : ℚ :=
  (rows.map fun row => if read row.1.key then row.2.remaining else 0).sum

/-- All outstanding original balances at this victim, debtor and good. -/
def dueFor (key : ClaimKey) (rows : List Row) : ℚ := dueWhere (· = key) rows

theorem dueFor_is_the_keyed_sum (key : ClaimKey) (rows : List Row) :
    dueFor key rows = (rows.map fun row => if row.1.key = key then row.2.remaining else 0).sum := rfl

theorem dueFor_nonnegative (key : ClaimKey) (rows : List Row) : 0 ≤ dueFor key rows := by
  apply List.sum_nonneg
  rintro value listed
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp listed
  split
  · exact row.2.nonnegative
  · exact le_rfl

theorem every_original_row_is_cleared_when_its_key_has_zero_due (key : ClaimKey) (rows : List Row)
    (zero : dueFor key rows = 0) (row : Row) (listed : row ∈ rows) (same : row.1.key = key) :
    row.2.remaining = 0 := by
  unfold dueFor dueWhere at zero
  apply List.all_zero_of_le_zero_le_of_sum_eq_zero ?_ zero
  · simpa only [same, if_true] using List.mem_map_of_mem
      (f := fun row : Row => if row.1.key = key then row.2.remaining else 0) listed
  · intro amount source
    obtain ⟨balance, _, rfl⟩ := List.mem_map.mp source
    split
    · exact balance.2.nonnegative
    · exact le_rfl

private theorem dueWhere_is_the_sum_of_the_filtered_rows (read : ClaimKey → Prop) [DecidablePred read]
    (rows : List Row) :
    dueWhere read rows = ((rows.filter fun row => decide (read row.1.key)).map fun row => row.2.remaining).sum := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    unfold dueWhere at ih ⊢
    by_cases selected : read row.1.key <;> simp [selected, ih]

theorem dueFor_is_the_sum_of_the_original_rows_of_the_key (key : ClaimKey) (rows : List Row) :
    dueFor key rows = ((rows.filter fun row => decide (row.1.key = key)).map fun row => row.2.remaining).sum :=
  dueWhere_is_the_sum_of_the_filtered_rows (· = key) rows

private abbrev otherSameGood (key other : ClaimKey) : Prop := other.2.2 = key.2.2 ∧ other ≠ key

private theorem outstanding_splits_at_the_key (key : ClaimKey) (rows : List Row) :
    Settlement.outstanding key.2.2 rows = dueFor key rows + dueWhere (otherSameGood key) rows := by
  induction rows with
  | nil => simp [Settlement.outstanding, dueFor, dueWhere]
  | cons row rest ih =>
    change ((if row.1.key.2.2 = key.2.2 then row.2.remaining else 0) + Settlement.outstanding key.2.2 rest) =
      ((if row.1.key = key then row.2.remaining else 0) + dueFor key rest) +
      ((if otherSameGood key row.1.key then row.2.remaining else 0) + dueWhere (otherSameGood key) rest)
    rw [ih]
    by_cases same : row.1.key = key
    · have good := congrArg (fun read : ClaimKey => read.2.2) same
      have notOther : ¬ otherSameGood key row.1.key := fun other => other.2 same
      simp only [if_pos good, if_pos same, if_neg notOther, zero_add, add_assoc]
    · by_cases good : row.1.key.2.2 = key.2.2
      · have other : otherSameGood key row.1.key := ⟨good, same⟩
        simp only [if_pos good, if_neg same, if_pos other, zero_add]
        ac_rfl
      · have notOther : ¬ otherSameGood key row.1.key := fun other => good other.1
        simp only [if_neg good, if_neg same, if_neg notOther, zero_add]

private theorem balance_ext {left right : Balance} (same : left.remaining = right.remaining) : left = right := by
  cases left
  cases right
  cases same
  rfl

variable (offer : Settlement.JointOffer seed) (limit : Good → ℚ)
  (backed : ∀ key (receipt : JointReceipt seed key), offer key = some receipt → limit key.2.2 ≤ receipt.quantity)
  {N J : WorldRelationNetwork} (before : Stack seed community N J) (available : Settlement.Available limit)

/-- Filtering keeps the exact balances and order of all selected old rows
when their keys have no receipt or no material budget at this position. -/
theorem allocation_keeps_every_unfunded_row (read : ClaimKey → Prop) [DecidablePred read]
    (closed : ∀ key, read key → offer key = none ∨ limit key.2.2 = 0) :
    (Settlement.allocate offer limit backed before available).after.balances.filter (fun row => decide (read row.1.key)) =
      before.balances.filter (fun row => decide (read row.1.key)) := by
  induction before with
  | base => rfl
  | add prior origin balance view earlier =>
    let paidPrior := Settlement.allocate offer limit backed prior available
    let room := paidPrior.left.balance origin.key.2.2
    let current := Settlement.allocateRow offer origin balance room.remaining room.nonnegative
      (fun receipt selected => (paidPrior.left.within origin.key.2.2).trans (backed origin.key receipt selected))
    change (paidPrior.after.balances ++ [(origin, current.after)]).filter (fun row => decide (read row.1.key)) =
      (prior.balances ++ [(origin, balance)]).filter (fun row => decide (read row.1.key))
    rw [List.filter_append, List.filter_append, earlier]
    by_cases selected : read origin.key
    · have noCharge : current.amount = 0 := by
        rw [current.exactAmount]
        rcases closed origin.key selected with absent | noStock
        · have due : Settlement.rowDemand offer origin balance = 0 := by simp [Settlement.rowDemand, absent]
          rw [due, min_eq_right room.nonnegative]
        · have noRoom : room.remaining = 0 := le_antisymm
            ((paidPrior.left.within origin.key.2.2).trans_eq noStock) room.nonnegative
          rw [noRoom, min_eq_left (Settlement.rowDemand_nonnegative offer origin balance)]
      have unchanged : current.after = balance := balance_ext (by rw [current.afterExact, noCharge, sub_zero])
      rw [unchanged]
    · simp [selected]

/-- At a good that can be allocated to only one key, all its actual debit
reduces that key. Any other key of this good keeps its own balances. -/
theorem the_unique_key_of_a_good_consumes_its_entire_booked_debit (key : ClaimKey)
    (only : ∀ other, other.2.2 = key.2.2 → other ≠ key → offer other = none) :
    let applied := Settlement.allocate offer limit backed before available
    dueFor key applied.after.balances +
      ((available.balance key.2.2).remaining - (applied.left.balance key.2.2).remaining) =
      dueFor key before.balances := by
  let applied := Settlement.allocate offer limit backed before available
  have untouched := allocation_keeps_every_unfunded_row offer limit backed before available (otherSameGood key)
    (fun other selected => Or.inl (only other selected.1 selected.2))
  have same : dueWhere (otherSameGood key) applied.after.balances = dueWhere (otherSameGood key) before.balances := by
    simp only [dueWhere_is_the_sum_of_the_filtered_rows]
    rw [untouched]
  have conserved := applied.conservation key.2.2
  rw [outstanding_splits_at_the_key, outstanding_splits_at_the_key, same] at conserved
  dsimp only
  linarith only [conserved]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
