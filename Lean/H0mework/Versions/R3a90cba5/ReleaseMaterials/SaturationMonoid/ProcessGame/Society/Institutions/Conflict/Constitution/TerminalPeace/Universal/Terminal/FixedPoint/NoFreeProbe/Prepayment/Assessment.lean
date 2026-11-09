import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.PaidWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

open private assess from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.PaidWrite

noncomputable section

inductive Verdict
  | ineligible
  | reviewed (demandsAggression : Bool)
  deriving DecidableEq

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}
  {current : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)}
  {bid : ReviewBid Party Good Port Technology Instrument}

variable (replies : Replies Party Good Port Technology Instrument) (paid : PaidReview current bid)

private def eligible : Bool :=
  replies.review current.ledger.resident.erase paid.round.visit.read.before.raw bid bid.payer

private def verdict : Verdict :=
  if eligible replies paid then .reviewed (assess paid) else .ineligible

/-- Eligibility reads the original cut through the already posted physical
receipt. Both dispositions inherit the exact ledger of that payment. -/
def assessment : Installation.Live.Landed seed community cut Verdict :=
  Installation.Live.publish paid.round.next.ledger (verdict replies paid) true

def assessmentNext : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase) :=
  { paid.round.next with ledger := (assessment replies paid).state }

theorem assessment_ineligible_iff :
    (assessment replies paid).read = .ineligible ↔
      replies.review current.ledger.resident.erase current.physical.raw bid bid.payer = false := by
  simp only [assessment, Installation.Live.publish_reads_the_exact_payload, verdict, eligible, paid.round.before]
  cases replies.review current.ledger.resident.erase current.physical.raw bid bid.payer <;> simp

theorem assessment_reviewed_iff (result : Bool) :
    (assessment replies paid).read = .reviewed result ↔
      replies.review current.ledger.resident.erase current.physical.raw bid bid.payer = true ∧
        paid.answer = result := by
  have answer : assess paid = paid.answer := rfl
  simp only [assessment, Installation.Live.publish_reads_the_exact_payload, verdict, eligible,
    paid.round.before, answer]
  cases replies.review current.ledger.resident.erase current.physical.raw bid bid.payer <;> simp

theorem assessment_canonical_next :
    (⟨paid.round.next.ledger.world,
      (Installation.Live.action paid.round.next.ledger (assessment replies paid).read
        true).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      (assessmentNext replies paid).ledger.resident.erase :=
  Installation.Live.the_canonical_write_is_the_published_whole_state _ _ _

theorem assessment_retains_prior_projection
    (projection : paid.round.next.ledger.resident.root.source.base.projectionLaw.Projection) :
    let arrived := (assessment replies paid).state.resident
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (paid.round.next.ledger.resident.root.source.base.projectionLaw.outcomeAt projection
        (paid.round.next.ledger.resident.root.emitted paid.round.next.ledger.resident.visit.current)) :=
  Installation.Live.earlier_reads_are_kept_at_the_landing _ _ _ projection

theorem assessment_stack :
    (assessmentNext replies paid).ledger.stack = paid.round.next.ledger.stack :=
  Installation.Live.publish_preserves_the_entire_stack _ _ _

theorem assessment_rows :
    (assessmentNext replies paid).ledger.stack.balances = current.ledger.stack.balances :=
  paid.round.rows

theorem assessment_original_expense :
    (assessmentNext replies paid).physical = paid.round.visit.read.effect.next ∧
    ∃ item, paid.round.visit.read.effect.execution.items[current.move.word.length]? = some item ∧
      item.request.signer = bid.payer ∧
      paid.round.visit.read.programme.law.actualDebit item.before item.request = locate bid.payer bid.expenses ∧
      paid.round.visit.read.programme.law.actualCredit item.before item.request = [] :=
  ⟨paid.round.physicalNext.symm, paid.original_expense⟩

theorem assessment_physical :
    (assessmentNext replies paid).physical = paid.round.next.physical :=
  rfl

theorem assessment_stock (person : Party) (good : Good) :
    (assessmentNext replies paid).physical.raw.stock person good - current.move.next.stock person good =
      -(bid.fee person good) :=
  paid.stock person good

theorem assessment_clock :
    current.physical.raw.clock + quantum ≤ (assessmentNext replies paid).physical.raw.clock :=
  paid.round.clock

theorem assessment_exact_clock :
    (assessmentNext replies paid).physical.raw.clock = current.move.next.clock :=
  paid.settledClock

theorem assessment_keeps_public_terms :
    KeepsPublicTerms current.programme (assessmentNext replies paid).programme :=
  paid.keepsPublicTerms

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment
