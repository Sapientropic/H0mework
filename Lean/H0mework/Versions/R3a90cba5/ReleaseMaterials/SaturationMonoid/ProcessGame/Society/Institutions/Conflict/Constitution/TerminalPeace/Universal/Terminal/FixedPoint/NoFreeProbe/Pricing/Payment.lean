import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Budget
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Registered

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Prepayment

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

variable {deskLaw : RawLaw Party Good Port Technology Instrument}
  {deskCut : RawCurrent Party Good Technology Instrument} {worker : Party}
  (desk : Desk deskLaw deskCut worker) (ready : desk.filingCheck = true)

local notation "Quote" => desk.tariff ready
local notation "Packet" => Wire Party Good Port Technology Instrument
local notation "Now" => Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)

variable (current : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
  (wire : Wire Party Good Port Technology Instrument)

omit [DecidableEq Port] in
private theorem bill_nonnegative : ∀ person good, 0 ≤ (bill Quote wire).fee person good := by
  intro person good
  change 0 ≤ if person = wire.payer then amount Good (bill Quote wire).expenses good else 0
  split
  · exact (Quote).amount_nonnegative wire.attempted good
  · exact le_rfl

/-- Check spendability on the published productive base before reading
any private qualification or opening an extra material slot. -/
def inspect :=
  inspectBudget current.programme.law reserveBase current.recipe.move.word (bill Quote wire)
    (bill_nonnegative desk ready wire)

theorem original_cost_is_funded_exactly_when_the_scan_passes :
    (∃ accepted, inspect desk ready current wire = .inr accepted) ↔
    BaseBudget current.programme.law reserveBase current.recipe.move.word (bill Quote wire) :=
  inspection_finds_the_exact_original_budget _ _ _ _ _

variable {current wire}

theorem actual_paid_work_has_one_original_debit (paid : PaidReview current (bill Quote wire)) :
    (∀ good, amount Good (bill Quote wire).expenses good = desk.actualCost wire.attempted good) ∧
    paid.round.next.physical.raw.clock = current.move.next.clock ∧
    (∀ good, current.move.next.stock wire.payer good - paid.round.next.physical.raw.stock wire.payer good =
      desk.actualCost wire.attempted good) ∧
    paid.round.next.ledger.stack.balances = current.ledger.stack.balances ∧
    ∃ item, paid.round.visit.read.effect.execution.items[current.move.word.length]? = some item ∧
      item.request.signer = wire.payer ∧
      paid.round.visit.read.programme.law.actualDebit item.before item.request =
        locate wire.payer (desk.filing.bundle ++ wire.attempted.flatMap (fun req => (desk.review req).bundle)) ∧
      paid.round.visit.read.programme.law.actualCredit item.before item.request = [] := by
  have cost (good : Good) : amount Good (bill Quote wire).expenses good = desk.actualCost wire.attempted good :=
    desk.exact_quote ready _ good
  refine ⟨cost, paid.settledClock, ?_, paid.round.rows, ?_⟩
  · intro good
    have paidAt := paid.stock wire.payer good
    change paid.round.next.physical.raw.stock wire.payer good - current.move.next.stock wire.payer good =
      -(if wire.payer = wire.payer then amount Good (bill Quote wire).expenses good else 0) at paidAt
    rw [if_pos rfl, cost good] at paidAt
    linarith only [paidAt]
  · obtain ⟨item, indexed, signer, debit, credit⟩ := paid.original_expense
    have zero : wire.attempted.flatMap (fun (_ : Request Party Good Port Technology Instrument) => ([] : Bundle Good)) = [] := by
      induction wire.attempted with
      | nil => rfl
      | cons req rest previous => simp [previous]
    refine ⟨item, indexed, signer, ?_, credit⟩
    simpa only [bill, ReviewBid.expenses, Tariff.parts, Desk.tariff, ChargeParts.bundle, zero, List.append_nil] using debit

/-- The existing charge is appended after the literal productive word.
No productive action or physical clock is displaced by this review. -/
theorem the_original_metered_write_keeps_the_productive_slot
    (funded : BaseBudget current.programme.law reserveBase current.recipe.move.word (bill Quote wire)) :
    let paid := funded.write ((Quote).positive wire.attempted)
    paid.round.visit.read.commands.take current.move.word.length = current.move.word ∧
      paid.round.next.physical.raw.clock = current.move.next.clock := by
  refine ⟨?_, (funded.write ((Quote).positive wire.attempted)).settledClock⟩
  change (chargedWord current.move.word wire.payer (bill Quote wire).port (bill Quote wire).expenses).take
    current.move.word.length = current.move.word
  rw [chargedWord, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing
