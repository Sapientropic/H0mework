import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Residual

/-!
Every old row follows its actual stack motion. Native postings may append
new rows; receipt positions can only reduce the balance of an old row.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Loss" => Reparation.Actual.Occurrence seed community

private theorem live_motion_never_increases (loss : Loss) {before after : Balance}
    (move : Reparation.Transport.Motion (law loss) (.live before) (.live after)) :
    after.remaining ≤ before.remaining := by
  change Step loss (.live before) (.live after) ⊕ Carry loss (.live before) (.live after) at move
  rcases move with payment | transport
  · cases payment with
    | final _ share _ _ | jointFinal _ share _ _ => exact sub_le_self _ share.positive.le
  · cases transport with
    | wait => exact le_rfl
    | partPaid _ share _ _ | jointPartPaid _ share _ _ => exact sub_le_self _ share.positive.le

theorem a_stack_motion_retains_each_old_row_and_never_increases_it
    {N J : WorldRelationNetwork} {before after : Stack seed community N J} (move : Stack.Move before after)
    (loss : Loss) (amount : Balance) (listed : (loss, amount) ∈ before.balances) :
    ∃ next, (loss, next) ∈ after.balances ∧ next.remaining ≤ amount.remaining := by
  induction move with
  | base => exact (List.not_mem_nil listed).elim
  | add prior origin view motion ih =>
    rw [Stack.balances, List.mem_append, List.mem_singleton] at listed
    rcases listed with earlier | here
    · obtain ⟨next, present, amountBound⟩ := ih earlier
      exact ⟨next, List.mem_append_left _ present, amountBound⟩
    · cases here
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), live_motion_never_increases _ motion⟩

variable (answers : ReceiptAnswers seed)
  {past : Reparation.Actual.Script Party Good Port Technology Instrument}
  {input : Reparation.Actual.Input Party Good Port Technology Instrument}

local notation "Posted" => StateAt seed community (Quantities.Execution.next
    (Quantities.Execution.endAt seed past) input)

private theorem positions_keep_each_old_row (loss : Loss)
    (positions : List (Reparation.Actual.Allocation.Position seed past input))
    (state : Posted) (amount : Balance) (listed : (loss, amount) ∈ state.stack.balances) :
    ∃ next, (loss, next) ∈ (Settlement.writePositions answers past input positions state).stack.balances ∧
      next.remaining ≤ amount.remaining := by
  induction positions generalizing state amount with
  | nil => exact ⟨amount, listed, le_rfl⟩
  | cons position tail ih =>
    let plan := Settlement.atPosition answers past input position state
    let after := Settlement.writePosition answers past input position state
    obtain ⟨remainder, original, first⟩ :=
      a_stack_motion_retains_each_old_row_and_never_increases_it plan.move loss amount listed
    have member : (loss, remainder) ∈ after.stack.balances := by
      unfold after
      rw [Settlement.writePosition_balances]
      exact original
    obtain ⟨next, present, later⟩ := ih after remainder member
    exact ⟨next, present, later.trans first⟩

theorem one_original_input_cannot_increase_or_erase_an_old_row (state : State seed community past)
    (loss : Loss) (amount : Balance) (listed : (loss, amount) ∈ state.stack.balances) :
    ∃ next, (loss, next) ∈ (Settlement.writeTick answers state input).stack.balances ∧
      next.remaining ≤ amount.remaining := by
  have postedRow : (loss, amount) ∈ (posted state input).stack.balances := by
    rw [posted_balances]
    exact List.mem_append_left _ listed
  rw [Settlement.writeTick_balances]
  exact positions_keep_each_old_row answers loss _ (posted state input) amount postedRow

theorem balance_never_increases_at_an_actual_successor (loss : Loss)
    (front : Reparation.Actual.Script Party Good Port Technology Instrument)
    (input : Reparation.Actual.Input Party Good Port Technology Instrument) :
    (balance answers loss (front ++ [input])).remaining ≤ (balance answers loss front).remaining := by
  have prior := balance_is_in_the_reached_rows answers loss front
  obtain ⟨next, exactNext, noIncrease⟩ := one_original_input_cannot_increase_or_erase_an_old_row
    (input := input) answers (reached answers loss front) loss (balance answers loss front) prior
  have atReached : (loss, next) ∈ (reached answers loss (front ++ [input])).stack.balances := by
    change (loss, next) ∈ (writeAfter answers (originState loss) (front ++ [input])).stack.balances
    rw [writeAfter_snoc_balances]
    exact exactNext
  have same := an_address_has_only_its_original_balance _ (reached_has_one_row_per_original_address
    answers loss (front ++ [input])) loss (balance_is_in_the_reached_rows answers loss (front ++ [input])) atReached
  rw [same]
  exact noIncrease

theorem a_finite_original_suffix_cannot_increase_the_original_balance (loss : Loss)
    (front tail : Reparation.Actual.Script Party Good Port Technology Instrument) :
    (balance answers loss (front ++ tail)).remaining ≤ (balance answers loss front).remaining := by
  induction tail using List.reverseRecOn with
  | nil => simp only [List.append_nil, le_refl]
  | append_singleton tail input ih =>
    rw [← List.append_assoc]
    exact (balance_never_increases_at_an_actual_successor answers loss (front ++ tail) input).trans ih

theorem a_paid_original_address_never_refills (loss : Loss)
    (front tail : Reparation.Actual.Script Party Good Port Technology Instrument)
    (cleared : (balance answers loss front).remaining = 0) :
    (balance answers loss (front ++ tail)).remaining = 0 :=
  le_antisymm
    ((a_finite_original_suffix_cannot_increase_the_original_balance answers loss front tail).trans_eq cleared)
    (balance answers loss (front ++ tail)).nonnegative

#print axioms a_paid_original_address_never_refills

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence
