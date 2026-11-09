import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Receipts.Writer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Receipts

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation Reparation.Actual Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument}
  {community : Party → Community}

local notation "History" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Proposal" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Row" => Occurrence seed community × Balance

def victimRows (person : Party) (rows : List Row) : List Row :=
  rows.filter fun row => decide (row.1.key.1 = person)

theorem changes_without_an_offer_keep_every_row_of_the_victim (person : Party)
    {offer : Offer seed} {rows : List Row} (moves : Changes rows) (actual : moves.uses offer)
    (none : ∀ key : Key Party Good, key.1 = person → offer key = none) :
    victimRows person moves.result = victimRows person rows := by
  induction moves with
  | nil => rfl
  | @cons row _ head tail prior =>
    have use : head.uses offer ∧ tail.uses offer := actual
    have inherited := prior use.2
    by_cases victim : row.1.key.1 = person
    · have keep : head = .keep := by
        cases head with
        | keep => rfl
        | pay share within =>
          have offered : offer row.1.key = some share.receipt := use.1
          rw [none _ victim] at offered
          cases offered
      rw [keep]
      simpa [victimRows, Changes.result, Change.after, victim] using
        congrArg ((row.1, row.2) :: ·) inherited
    · simpa [victimRows, Changes.result, victim] using inherited

theorem consumePositions_keep_victim_without_receipts (answers : OwnerAnswers seed) (person : Party)
    (past : History) (input : Proposal) (positions : List (Position seed past input))
    (state : StateAt seed community (Quantities.Execution.next (Quantities.Execution.endAt seed past) input))
    (none : ∀ position ∈ positions, ∀ key : Key Party Good, key.1 = person →
      personalOffer answers past input position key = none) :
    victimRows person (consumePositions answers past input positions state).stack.balances =
      victimRows person state.stack.balances := by
  induction positions generalizing state with
  | nil => rfl
  | cons position later prior =>
    rw [consumePositions, prior _ (fun item listed => none item (List.mem_cons_of_mem _ listed)),
      StateAt.consume_balances]
    exact changes_without_an_offer_keep_every_row_of_the_victim person _
      (atPersonalItem answers past input position state.stack.balances).original (none position List.mem_cons_self)

theorem consumePositions_keep_the_withholding_victim (answers : OwnerAnswers seed) (person : Party)
    (past : History) (input : Proposal) (positions : List (Position seed past input))
    (state : StateAt seed community (Quantities.Execution.next (Quantities.Execution.endAt seed past) input)) :
    victimRows person (consumePositions (withhold answers person) past input positions state).stack.balances =
      victimRows person state.stack.balances :=
  consumePositions_keep_victim_without_receipts (withhold answers person) person past input positions state
    (fun position _ => a_withheld_lane_has_no_receipt answers past input position person)

/-- All older balances of this person retain their complete disposition.
Any new damage in the same visit is appended at its original opening. -/
theorem a_withheld_tick_preserves_the_victims_exact_old_rows (answers : OwnerAnswers seed) (person : Party)
    (past : History) (input : Proposal) (prior : State seed community past) :
    victimRows person (writeTick (withhold answers person) prior input).stack.balances =
      victimRows person prior.stack.balances ++
        victimRows person ((openings seed community past input).map fun origin => (origin, opening origin)) := by
  rw [writeTick_balances, consumePositions_keep_the_withholding_victim, posted_balances]
  exact List.filter_append _ _

theorem history_cast_preserves_balances {before after : History} (same : before = after)
    (state : State seed community before) :
    (same ▸ state : State seed community after).stack.balances = state.stack.balances := by
  cases same
  rfl

theorem a_withheld_balance_survives_every_later_input (answers : OwnerAnswers seed) (person : Party)
    (past suffix : History) (prior : State seed community past) :
    (victimRows person prior.stack.balances).IsPrefix
      (victimRows person (writeAfter (withhold answers person) prior suffix).stack.balances) := by
  induction suffix using List.reverseRecOn with
  | nil =>
    rw [writeAfter, List.reverseRecOn_nil, history_cast_preserves_balances]
  | append_singleton earlier input inherited =>
    rw [writeAfter_snoc, history_cast_preserves_balances, a_withheld_tick_preserves_the_victims_exact_old_rows]
    exact inherited.trans (List.prefix_append _ _)

theorem the_exact_withheld_balance_is_read_on_the_original_successor (answers : OwnerAnswers seed)
    (past suffix : History) (prior : State seed community past)
    (origin : Occurrence seed community) (balance : Balance)
    (old : (origin, balance) ∈ prior.stack.balances) :
    let reached := writeAfter (withhold answers origin.key.1) prior suffix
    ∃ row, reached.read row = .inr (origin, balance) := by
  let reached := writeAfter (withhold answers origin.key.1) prior suffix
  have originally : (origin, balance) ∈ victimRows origin.key.1 prior.stack.balances :=
    List.mem_filter.mpr ⟨old, by simp⟩
  have retained : (origin, balance) ∈ victimRows origin.key.1 reached.stack.balances :=
    (a_withheld_balance_survives_every_later_input answers origin.key.1 past suffix prior).subset originally
  exact reached.every_balance_is_a_row_of_the_current _ (List.mem_filter.mp retained).1

theorem writeAfter_origins (answers : OwnerAnswers seed) (past suffix : History) (prior : State seed community past)
    (literal : prior.stack.balances.map Prod.fst = originalLosses seed community past) :
    (writeAfter answers prior suffix).stack.balances.map Prod.fst =
      originalLosses seed community (past ++ suffix) := by
  induction suffix using List.reverseRecOn with
  | nil =>
    rw [writeAfter, List.reverseRecOn_nil, history_cast_preserves_balances, List.append_nil]
    exact literal
  | append_singleton earlier input inherited =>
    rw [writeAfter_snoc, history_cast_preserves_balances, writeTick_origins, inherited,
      ← List.append_assoc, losses_snoc]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Receipts
