import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalTrial

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Reparation.Actual (Balance)
open Joint.OriginalExchange (claim)
open private original_need_cut from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalSource

noncomputable section

abbrev payerCut := actualTrial.actual.period.next

def signed (victim : Bool) : DeliveryAnswers Bool Bool Bool Unit Unit :=
  fun _ _ _ _ person => person || victim

def cells : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

theorem allCells (address : Bool × Bool) : address ∈ cells := by
  rcases address with ⟨person, good⟩
  cases person <;> cases good <;> decide

theorem the_original_six_survive_the_new_production :
    payerCut.ledger.stack.balances = [(loss, Original.balance)] ∧ liveBalance payerCut claim = 6 := by
  have same := actualTrial.actual.period.rows.trans actualTrial.originalDebt
  refine ⟨same, ?_⟩
  unfold liveBalance
  rw [same, dueFor_is_the_keyed_sum]
  change (if loss.key = claim then Original.balance.remaining else 0) + 0 = 6
  rw [if_pos (show loss.key = claim from rfl), add_zero, Original.balance_six]

theorem fullyFunded : Funding payerCut (signed true) claim 6 := by
  refine ⟨Bool.false_ne_true, by norm_num, ?_, ?_, rfl, rfl, ?_⟩
  · exact the_original_six_survive_the_new_production.2.ge
  · unfold request purpose
    rw [actualTrial.revisedProgramme, actualTrial.revisedStock]
    decide +kernel
  · intro person good
    unfold requiredAt
    rw [actualTrial.revisedProgramme, actualTrial.revisedStock, original_need_cut]
    cases person <;> cases good <;> decide +kernel

/-- The original payer draws six units from the revised mill and the
carried stock. The victim’s original address remains in the cleared ledger. -/
theorem the_new_interpreter_clears_the_original_six :
    ∃ paid, pay payerCut (signed true) claim 6 cells allCells = .inr paid ∧
      paid.receipt.quantity = 6 ∧ paid.receipt.item.before = afterTrial ∧
      paid.next.ledger.stack.balances.map Prod.fst = [loss] ∧
      (∀ row ∈ paid.next.ledger.stack.balances, row.2.remaining = 0) ∧
      paid.next.physical.raw.clock = 5 ∧
      paid.next.physical.raw.claims = payerCut.physical.raw.claims ∧
      ∀ item ∈ paid.visit.read.effect.execution.items, ∀ key,
        Reparation.loss payerCut.programme.law Original.community item key = 0 := by
  obtain ⟨paid, actual⟩ := (pays_exactly_at_a_funded_position payerCut (signed true) claim 6 cells allCells).mpr fullyFunded
  have receipt := congrArg (fun item : ExecutionItem Bool Bool Bool Unit Unit => item.before) paid.item
  have ids := Settlement.consumePosted_keeps_the_original_addresses
    (anchor loss front) paid.visit paid.ordered paid.accepted paid.position
  rw [← paid.allocated, paid.exactVisit, Installation.Core.publish_preserves_the_entire_stack] at ids
  have exactOrigins : paid.next.ledger.stack.balances.map Prod.fst = [loss] :=
    ids.trans (congrArg (List.map Prod.fst) the_original_six_survive_the_new_production.1)
  refine ⟨paid, actual, paid.amount, receipt.trans actualTrial.revisedStock, exactOrigins, ?_, ?_, ?_, paid.noDamage⟩
  · have zero := paid.balances claim
    rw [if_pos rfl, the_original_six_survive_the_new_production.2, sub_self] at zero
    intro row listed
    have origin : row.1 = loss := List.mem_singleton.mp (exactOrigins ▸ List.mem_map_of_mem (f := Prod.fst) listed)
    exact every_original_row_is_cleared_when_its_key_has_zero_due claim _ zero row listed
      (congrArg (fun origin => origin.key) origin)
  · rw [paid.stock, actualTrial.revisedStock]
    rfl
  · rw [paid.stock]
    rfl

theorem the_victims_refusal_preserves_the_new_stock_and_original_six :
    ∃ refused, pay payerCut (signed false) claim 6 cells allCells = .inl refused ∧
      refused.next.physical.raw = afterTrial ∧ liveBalance refused.next claim = 6 ∧
      ∃ vote, refused.visit.read = .victimRefused vote := by
  let attempt := checkFunding payerCut (signed false) claim 6 cells allCells
  have notSigned : signAt payerCut (signed false) claim 6 false = false := rfl
  have debtor : signAt payerCut (signed false) claim 6 true = true := rfl
  cases checked : attempt with
  | ok proof =>
    have victim := proof.down.victim
    change signAt payerCut (signed false) claim 6 false = true at victim
    exact (Bool.false_ne_true (notSigned.symm.trans victim)).elim
  | error issue =>
    have actual : pay payerCut (signed false) claim 6 cells allCells = .inl (refuse payerCut issue) := by
      unfold pay
      have exactCheck : checkFunding payerCut (signed false) claim 6 cells allCells = .error issue := checked
      rw [exactCheck]
    refine ⟨refuse payerCut issue, actual, actualTrial.revisedStock, the_original_six_survive_the_new_production.2, ?_⟩
    change ∃ vote, issue = .victimRefused vote
    cases issue with
    | sameParty same => exact (fullyFunded.distinct same).elim
    | nonpositive bad => exact (bad.not_gt fullyFunded.positive).elim
    | overclaim bad => exact (bad.not_ge fullyFunded.within).elim
    | notAuthorized bad => exact (bad fullyFunded.legal).elim
    | payerRefused bad => exact (Bool.false_ne_true (bad.symm.trans debtor)).elim
    | victimRefused vote => exact ⟨vote, rfl⟩
    | shortage person good short => exact (short.not_ge (fullyFunded.reserve person good)).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
