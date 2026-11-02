import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Posting
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting.Balance

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.FinancialBalance

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration.Posting

noncomputable section

def positions (packet : Packet) (side : Side) (party : Bool) (good : Good) :=
  Balance.position sources packet.2.finance.current side party good

def issues {first last : Packet} (path : Evolution first last) :=
  Balance.newIssues sources (Future.Expiry.Progress.Response.financeAlong path)

def assignments {first last : Packet} (path : Evolution first last) :=
  Balance.assignments sources (Future.Expiry.Progress.Response.financeAlong path)

theorem financial_balance {first last : Packet} (path : Evolution first last) (side : Side) (party : Bool) (good : Good) :
    positions last side party good + Posting.actual path side party good =
      positions first side party good + issues path side party good + assignments path side party good :=
  Balance.run_balance sources (Future.Expiry.Progress.Response.financeAlong path) side party good

theorem debt_balance {first last : Packet} (path : Evolution first last) (party : Bool) (good : Good) :
    positions last .debit party good - positions first .debit party good =
      issues path .debit party good - Costs.cost path party (.debtPayment good) := by
  have result := Balance.debtor_balance sources (Future.Expiry.Progress.Response.financeAlong path) party good
  change _ = issues path .debit party good - Posting.actual path .debit party good at result
  rw [Posting.debit_is_the_same_material_payment] at result
  exact result

/-- Actual non-settlement credits, generated from the same original raw items.
This retains production and transfers without counting a payment credit twice. -/
def otherAt (entry : PublicFunction.Costs.Visits.Window sources) (party : Bool) (good : Good) : ℚ :=
  (((sources entry.1).law.rawItems (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
    (ProgrammeSource.rawEvent (sources entry.1) entry.2.current)).map fun item =>
      if PublicFunction.Costs.isDebtPayment item.request then 0 else
        flowAt ((sources entry.1).law.actualCredit item.before item.request) party good).sum

def otherTotal : List (PublicFunction.Costs.Visits.Window sources) → Bool → Good → ℚ
  | [], _, _ => 0
  | entry :: rest, party, good => otherAt entry party good + otherTotal rest party good

def otherCredits {first last : Packet} (path : Evolution first last) := otherTotal (Costs.records path)

theorem otherAt_partition (entry : PublicFunction.Costs.Visits.Window sources) (party : Bool) (good : Good) :
    PublicFunction.Costs.Visits.creditAt sources entry party good =
      atVisit sources entry .credit party good + otherAt entry party good := by
  unfold PublicFunction.Costs.Visits.creditAt RawLaw.totalCredit atVisit rawTotal otherAt
  induction (sources entry.1).law.rawItems
      (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
      (ProgrammeSource.rawEvent (sources entry.1) entry.2.current) with
  | nil => simp only [List.map_nil, List.sum_nil, add_zero]
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have first : flowAt ((sources entry.1).law.actualCredit item.before item.request) party good =
          rawAmount sources entry.1 item .credit party good +
            (if PublicFunction.Costs.isDebtPayment item.request then 0 else
              flowAt ((sources entry.1).law.actualCredit item.before item.request) party good) := by
        cases operation : item.request.operation <;> simp [rawAmount, PublicFunction.Costs.isDebtPayment, operation]
      linarith

theorem otherTotal_partition (entries : List (PublicFunction.Costs.Visits.Window sources)) (party : Bool) (good : Good) :
    PublicFunction.Costs.Visits.credits sources entries party good =
      Financial.Family.Migration.Posting.total sources entries .credit party good + otherTotal entries party good := by
  induction entries with
  | nil => simp only [PublicFunction.Costs.Visits.credits, Financial.Family.Migration.Posting.total, otherTotal, add_zero]
  | cons entry rest ih =>
      change PublicFunction.Costs.Visits.creditAt sources entry party good +
        PublicFunction.Costs.Visits.credits sources rest party good =
          (atVisit sources entry .credit party good + Financial.Family.Migration.Posting.total sources rest .credit party good) +
            (otherAt entry party good + otherTotal rest party good)
      rw [otherAt_partition, ih]
      ring

theorem credits_partition {first last : Packet} (path : Evolution first last) (party : Bool) (good : Good) :
    Costs.credits path party good = Posting.actual path .credit party good + otherCredits path party good := by
  rw [Posting.exact_amount]
  exact otherTotal_partition (Costs.records path) party good

/-- A quoted financial position is not a promise of future convertibility.
Material stock, original outstanding assets and liabilities remain separate
inputs, all read from this actual packet. -/
def quotedNet (packet : Packet) (party : Bool) (good : Good) : ℚ :=
  (current packet.1 packet.2.inputs).stock party good +
    positions packet .credit party good - positions packet .debit party good

/-- Settlement moves cash and cancels the same outstanding claim. It does not
create a second net financing cost. New issues and assignments stay explicit. -/
theorem actual_net_balance {first last : Packet} (path : Evolution first last) (party : Bool) (good : Good) :
    quotedNet last party good + Costs.cost path party (.operating good) =
      quotedNet first party good + otherCredits path party good + issues path .credit party good -
        issues path .debit party good + assignments path .credit party good := by
  have material := Costs.material_balance path party good
  have debts := debt_balance path party good
  have assets := financial_balance path .credit party good
  have splitCredit := credits_partition path party good
  unfold quotedNet
  linarith

theorem otherAt_nonnegative (entry : PublicFunction.Costs.Visits.Window sources) (party : Bool) (good : Good) :
    0 ≤ otherAt entry party good := by
  unfold otherAt
  apply List.sum_nonneg
  intro value inside
  obtain ⟨item, member, rfl⟩ := List.mem_map.mp inside
  split
  · exact le_rfl
  · by_cases accepted : (sources entry.1).law.Valid item.before item.request
    · simpa only [RawLaw.actualCredit, if_pos accepted, flowAt] using
        amount_nonnegative ((sources entry.1).law.credit item.before item.request) accepted.2.2.2.2.1 (party, good)
    · simp [RawLaw.actualCredit, accepted, flowAt, Institutions.Capitalism.Universal.Source.Program.amount]

theorem otherTotal_nonnegative (entries : List (PublicFunction.Costs.Visits.Window sources)) (party : Bool) (good : Good) :
    0 ≤ otherTotal entries party good := by
  induction entries with
  | nil => exact le_rfl
  | cons entry rest ih => exact add_nonneg (otherAt_nonnegative entry party good) ih

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.FinancialBalance
