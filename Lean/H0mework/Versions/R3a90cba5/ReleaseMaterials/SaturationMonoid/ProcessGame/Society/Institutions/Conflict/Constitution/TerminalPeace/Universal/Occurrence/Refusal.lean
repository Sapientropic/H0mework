import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Monotone

/-!
An original party can withhold the receipt without removing the actual
transfer or the old row. This tracks the exact balance across every position.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation Reparation.Actual
open Reparation.Actual.Allocation (Position itemPositions)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Loss" => Reparation.Actual.Occurrence seed community

private theorem balance_ext {left right : Balance} (same : left.remaining = right.remaining) : left = right := by
  cases left
  cases right
  cases same
  rfl

private theorem allocate_keeps_a_row_with_no_offer
    (offer : Settlement.JointOffer seed) (limit : Good → ℚ)
    (backed : ∀ key (receipt : JointReceipt seed key), offer key = some receipt → limit key.2.2 ≤ receipt.quantity)
    {N J : WorldRelationNetwork} (stack : Stack seed community N J) (available : Settlement.Available limit)
    (loss : Loss) (amount : Balance) (listed : (loss, amount) ∈ stack.balances) (absent : offer loss.key = none) :
    (loss, amount) ∈ (Settlement.allocate offer limit backed stack available).after.balances := by
  induction stack with
  | base => exact (List.not_mem_nil listed).elim
  | add prior origin before view ih =>
    rw [Stack.balances, List.mem_append, List.mem_singleton] at listed
    let earlier := Settlement.allocate offer limit backed prior available
    let supply := earlier.left.balance origin.key.2.2
    let head := Settlement.allocateRow offer origin before supply.remaining supply.nonnegative
      (fun receipt selected => (earlier.left.within origin.key.2.2).trans (backed origin.key receipt selected))
    change (loss, amount) ∈ earlier.after.balances ++ [(origin, head.after)]
    rcases listed with older | here
    · exact List.mem_append_left _ (ih older)
    · cases here
      have due : Settlement.rowDemand offer loss amount = 0 := by simp [Settlement.rowDemand, absent]
      have zero : head.amount = 0 := by
        rw [head.exactAmount, due, min_eq_right supply.nonnegative]
      have same : head.after = amount := balance_ext (by rw [head.afterExact, zero, sub_zero])
      rw [same]
      exact List.mem_append_right _ (List.mem_singleton_self _)

variable (answers : ReceiptAnswers seed)
  {past : Reparation.Actual.Script Party Good Port Technology Instrument}
  {input : Reparation.Actual.Input Party Good Port Technology Instrument}

local notation "Posted" => StateAt seed community (Quantities.Execution.next
    (Quantities.Execution.endAt seed past) input)

private theorem no_position_books_an_unoffered_row
    (loss : Loss) (amount : Balance) (positions : List (Position seed past input))
    (state : Posted) (listed : (loss, amount) ∈ state.stack.balances)
    (absent : ∀ position ∈ positions, Settlement.jointOffer answers past input position loss.key = none) :
    (loss, amount) ∈ (Settlement.writePositions answers past input positions state).stack.balances := by
  induction positions generalizing state with
  | nil => exact listed
  | cons position tail ih =>
    let after := Settlement.writePosition answers past input position state
    have kept : (loss, amount) ∈ after.stack.balances := by
      unfold after
      rw [Settlement.writePosition_balances]
      exact allocate_keeps_a_row_with_no_offer _ _ _ state.stack _ loss amount listed
        (absent position List.mem_cons_self)
    exact ih after kept (fun position member => absent position (List.mem_cons_of_mem _ member))

/-- Even if material is actually delivered, any original party's refusal
at each of the item's positions retains the exact old balance. -/
theorem an_actual_tick_cannot_book_the_old_row_over_either_original_partys_refusal
    (state : State seed community past) (loss : Loss) (amount : Balance)
    (listed : (loss, amount) ∈ state.stack.balances)
    (refused : ∀ position : Position seed past input,
      answers past input position loss.key.1 = false ∨ answers past input position loss.key.2.1 = false) :
    (loss, amount) ∈ (Settlement.writeTick answers state input).stack.balances := by
  have postedRow : (loss, amount) ∈ (posted state input).stack.balances := by
    rw [posted_balances]
    exact List.mem_append_left _ listed
  rw [Settlement.writeTick_balances]
  apply no_position_books_an_unoffered_row answers loss amount _ (posted state input) postedRow
  intro position _
  rcases refused position with victim | payer
  · exact Settlement.the_original_victims_refusal_prevents_a_receipt _ _ _ _ _ victim
  · exact Settlement.the_original_payers_refusal_prevents_a_receipt _ _ _ _ _ payer

theorem either_original_partys_refusal_keeps_the_exact_balance_on_the_successor
    (loss : Loss) (front : Reparation.Actual.Script Party Good Port Technology Instrument)
    (input : Reparation.Actual.Input Party Good Port Technology Instrument)
    (refused : ∀ position : Position seed (history loss ++ front) input,
      answers (history loss ++ front) input position loss.key.1 = false ∨
        answers (history loss ++ front) input position loss.key.2.1 = false) :
    balance answers loss (front ++ [input]) = balance answers loss front := by
  have kept := an_actual_tick_cannot_book_the_old_row_over_either_original_partys_refusal
    answers (reached answers loss front) loss (balance answers loss front)
    (balance_is_in_the_reached_rows answers loss front) refused
  have written : (loss, balance answers loss front) ∈
      (reached answers loss (front ++ [input])).stack.balances := by
    change (loss, balance answers loss front) ∈
      (writeAfter answers (originState loss) (front ++ [input])).stack.balances
    rw [writeAfter_snoc_balances]
    exact kept
  exact an_address_has_only_its_original_balance _ (reached_has_one_row_per_original_address
    answers loss (front ++ [input])) loss (balance_is_in_the_reached_rows answers loss (front ++ [input])) written

theorem either_original_party_can_keep_the_old_balance_through_any_actual_suffix
    (loss : Loss) (suffix : Reparation.Actual.Script Party Good Port Technology Instrument)
    (refused : ∀ (front later : Reparation.Actual.Script Party Good Port Technology Instrument)
      (input : Reparation.Actual.Input Party Good Port Technology Instrument),
      suffix = front ++ input :: later → ∀ position : Position seed (history loss ++ front) input,
      answers (history loss ++ front) input position loss.key.1 = false ∨
        answers (history loss ++ front) input position loss.key.2.1 = false) :
    balance answers loss suffix = balance answers loss [] := by
  induction suffix using List.reverseRecOn with
  | nil => rfl
  | append_singleton front input ih =>
    have atEnd := either_original_partys_refusal_keeps_the_exact_balance_on_the_successor
      answers loss front input (refused front [] input rfl)
    apply atEnd.trans
    apply ih
    intro earlier later attempt listed position
    exact refused earlier (later ++ [input]) attempt
      (by rw [listed, List.append_assoc]; rfl) position

#print axioms either_original_partys_refusal_keeps_the_exact_balance_on_the_successor
#print axioms either_original_party_can_keep_the_old_balance_through_any_actual_suffix

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence
