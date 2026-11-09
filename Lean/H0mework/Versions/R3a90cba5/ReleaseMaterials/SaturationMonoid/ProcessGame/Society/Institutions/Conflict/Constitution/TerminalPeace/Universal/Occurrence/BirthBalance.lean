import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Monotone

/-!
The original tick may already have paid part of its own loss at a later
item. Compare the processed balance with the exact material filing.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation.Actual Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Loss" => Reparation.Actual.Occurrence seed community
local notation "Row" => Loss × Balance

private theorem old_position_keeps_each_row {rows : List Row} (changes : Changes rows)
    (loss : Loss) (before : Balance) (listed : (loss, before) ∈ rows) :
    ∃ after, (loss, after) ∈ changes.result ∧ after.remaining ≤ before.remaining := by
  induction changes with
  | nil => exact (List.not_mem_nil listed).elim
  | cons head tail ih =>
    rcases List.mem_cons.mp listed with here | later
    · cases here
      refine ⟨head.after, List.mem_cons_self, ?_⟩
      rw [head.after_exact]
      exact sub_le_self _ head.amount_nonnegative
    · obtain ⟨after, actual, amount⟩ := ih later
      exact ⟨after, List.mem_cons_of_mem _ actual, amount⟩

private theorem old_tick_keeps_each_row
    {past : Reparation.Actual.Script Party Good Port Technology Instrument}
    {input : Reparation.Actual.Input Party Good Port Technology Instrument}
    {positions : List (Position seed past input)} {rows : List Row}
    (trace : ItemWrites past input positions rows) (loss : Loss) (before : Balance)
    (listed : (loss, before) ∈ rows) :
    ∃ after, (loss, after) ∈ trace.result ∧ after.remaining ≤ before.remaining := by
  induction trace generalizing before with
  | nil => exact ⟨before, listed, le_rfl⟩
  | @next position _ rows tail ih =>
    obtain ⟨remaining, nextRow, first⟩ :=
      old_position_keeps_each_row (atItem seed past input position rows).changes loss before listed
    obtain ⟨after, actual, later⟩ := ih remaining nextRow
    exact ⟨after, actual, later.trans first⟩

theorem the_processed_birth_contains_the_original_row_with_its_actual_balance (loss : Loss) :
    ∃ amount, (loss, amount) ∈ (originState loss).stack.balances ∧ amount.remaining ≤ loss.quantity := by
  let prior := run seed community loss.past
  have starts := the_original_row_starts_at_the_actual_loss_quantity loss
  change (loss, opening loss) ∈ (posted prior loss.input).stack.balances at starts
  rw [posted_balances] at starts
  change ∃ amount, (loss, amount) ∈ (run seed community (history loss)).stack.balances ∧
    amount.remaining ≤ loss.quantity
  rw [history, run_snoc, written_balances]
  exact old_tick_keeps_each_row (atInput loss.past loss.input _) loss (opening loss) starts

theorem the_original_loss_bounds_every_later_balance (answers : ReceiptAnswers seed) (loss : Loss)
    (suffix : Reparation.Actual.Script Party Good Port Technology Instrument) :
    (balance answers loss suffix).remaining ≤ loss.quantity := by
  obtain ⟨initial, listed, bound⟩ := the_processed_birth_contains_the_original_row_with_its_actual_balance loss
  have atBirth : (loss, initial) ∈ (reached answers loss []).stack.balances := by
    change (loss, initial) ∈ (writeAfter answers (originState loss) []).stack.balances
    rwa [writeAfter_nil_balances]
  have same := an_address_has_only_its_original_balance _ (reached_has_one_row_per_original_address
    answers loss []) loss (balance_is_in_the_reached_rows answers loss []) atBirth
  have decreases := a_finite_original_suffix_cannot_increase_the_original_balance answers loss [] suffix
  rw [List.nil_append, same] at decreases
  exact decreases.trans bound

theorem a_blocked_original_balance_reports_a_bounded_exact_shortfall
    (answers : ReceiptAnswers seed) (loss : Loss)
    (suffix : Reparation.Actual.Script Party Good Port Technology Instrument)
    (blocked : Obstruction (.live (balance answers loss suffix))) :
    let named := residual answers loss suffix
    named.1 = loss.key.1 ∧ named.2.1 = loss.key.2.2 ∧
      0 < named.2.2 ∧ named.2.2 ≤ loss.quantity ∧
      ∃ row, (reached answers loss suffix).read row = .inr (loss, balance answers loss suffix) :=
  ⟨rfl, rfl, blocked.down, the_original_loss_bounds_every_later_balance answers loss suffix,
    reached_reads_exact_origin answers loss suffix⟩

#print axioms the_original_loss_bounds_every_later_balance
#print axioms a_blocked_original_balance_reports_a_bounded_exact_shortfall

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence
