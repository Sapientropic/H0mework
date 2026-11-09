import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

variable (current : Current (seed := seed) (cut := cut) (community := community) origin people quantum)
  (bid : ReviewBid Party Good Port Technology Instrument)

local notation "Expense" =>
  reviewItem current.programme current.physical.raw current.move.word bid.payer bid.port bid.expenses

/-- The physical charge and the ordinary production are posted together.
The protected review reads this paid write rather than a presented bid. -/
structure PaidReview where
  private mk ::
  round : Round current
  chargedAt : round.visit.read.effect.execution.items[current.move.word.length]? = some Expense
  debit : round.visit.read.programme.law.actualDebit (Expense).before (Expense).request = locate bid.payer bid.expenses
  credit : round.visit.read.programme.law.actualCredit (Expense).before (Expense).request = []
  positive : ∃ good, 0 < amount Good bid.expenses good
  programme : round.next.programme = current.programme
  settledClock : round.next.physical.raw.clock = current.move.next.clock
  stock : ∀ person good, round.next.physical.raw.stock person good - current.move.next.stock person good =
    -(bid.fee person good)

/-- Read the positive expense from the actual original material position.
This construction needs no answer to the protected review. -/
def writePaidReview (legal : ReviewLegal current bid) (fits : ReviewFits current.recipe bid.fee)
    (surplus : ∃ person good, bid.fee person good < current.recipe.gain person good)
    (positive : ∃ good, 0 < amount Good bid.expenses good) : PaidReview current bid := by
  let round := paidReviewRound current bid legal fits surplus
  have paid := paidReviewRound_reads_the_payers_whole_cost current bid legal fits surplus
  have charge := charged_actual_debit legal
  have programme := round.programmeNext.trans paid.2.1
  refine ⟨round, paidReviewRound_charges_the_actual_last_item current bid legal fits surplus, ?_, ?_,
    positive, paid.2.1, paid.2.2.2.2.1, paid.2.2.2.2.2.2⟩
  · rw [programme]
    exact charge.1
  · rw [programme]
    exact charge.2

variable {current bid}

namespace PaidReview

variable (paid : PaidReview current bid)

private def assess : Bool := by
  classical
  exact decide (DemandsAggression (community := community) paid.round.visit.read.programme.law
    paid.round.visit.read.before.raw bid)

/-- The assessment is published from the charged successor of the same
ledger. Its semantic write carries no second material debit. -/
def publication : Installation.Core.Landed seed community cut Bool :=
  Installation.Core.publish paid.round.next.ledger paid.assess true

def answer : Bool := paid.publication.read

def next : Current (seed := seed) (cut := cut) (community := community) origin people quantum :=
  { paid.round.next with ledger := paid.publication.state }

theorem answer_iff :
    paid.answer = true ↔ DemandsAggression (community := community) current.programme.law current.physical.raw bid := by
  classical
  change decide (DemandsAggression (community := community) paid.round.visit.read.programme.law
    paid.round.visit.read.before.raw bid) = true ↔ _
  rw [decide_eq_true_eq, paid.round.before, paid.round.programmeNext, paid.programme]

theorem original_expense :
    ∃ item, paid.round.visit.read.effect.execution.items[current.move.word.length]? = some item ∧
      item.request.signer = bid.payer ∧
      paid.round.visit.read.programme.law.actualDebit item.before item.request = locate bid.payer bid.expenses ∧
      paid.round.visit.read.programme.law.actualCredit item.before item.request = [] := by
  exact ⟨Expense, paid.chargedAt, rfl, paid.debit, paid.credit⟩

theorem expense_belongs_to_the_payer {lot : (Party × Good) × ℚ}
    (listed : lot ∈ paid.round.visit.read.programme.law.actualDebit (Expense).before (Expense).request) :
    lot.1.1 = bid.payer := by
  rw [paid.debit] at listed
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp listed
  rfl

theorem wholeNext :
    (⟨paid.round.next.ledger.world,
      (Installation.Core.action paid.round.next.ledger paid.answer true).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = paid.next.ledger.resident.erase :=
  Installation.Core.the_canonical_write_is_the_published_whole_state _ _ _

theorem rows : paid.next.ledger.stack.balances = current.ledger.stack.balances :=
  paid.round.rows

theorem clock : current.physical.raw.clock + quantum ≤ paid.next.physical.raw.clock :=
  paid.round.clock

theorem keepsPublicTerms : KeepsPublicTerms current.programme paid.next.programme := by
  change KeepsPublicTerms current.programme paid.round.next.programme
  rw [paid.programme]
  exact .refl _

end PaidReview

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe
