import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook.Posting
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.AssignedFinancing.Cohort

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.FinancingBook
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration
noncomputable section
variable {first last : Packet} (actual : Evolution first last)

def before (packet : Packet) := FinancingBook.generated sources packet.2.finance

def flow := FinancingBook.fold sources (Future.Expiry.Progress.Response.financeAlong actual) (before first)

def charge := FinancingBook.Posting.nativeCharge sources (flow actual)

structure Receipt where
  original_slots : (flow actual).after.cells.map FinancingBook.Cell.slot = last.2.finance.current.slots
  original_events : (flow actual).rows.map FinancingBook.Row.native =
    (Future.Expiry.Progress.Response.financeAlong actual).events
  all_positions : ∀ side party good,
    FinancingBook.Posting.position sources (flow actual).after true side party good +
      FinancingBook.Posting.position sources (flow actual).after false side party good =
        FinancialBalance.positions last side party good
  payments : ∀ side party good window,
    FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.payment sources) true side party good window +
      FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.payment sources) false side party good window =
        FinancingBook.Posting.actual sources (Future.Expiry.Progress.Response.financeAlong actual)
          (Financial.Family.Migration.Posting.amount sources) side party good window
  issues : ∀ side party good window,
    FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.issued sources) true side party good window +
      FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.issued sources) false side party good window =
        FinancingBook.Posting.actual sources (Future.Expiry.Progress.Response.financeAlong actual)
          (Financial.Family.Migration.Posting.Balance.issued sources) side party good window
  assignments : ∀ side party good window,
    FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.assigned sources) true side party good window +
      FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.assigned sources) false side party good window =
        FinancingBook.Posting.actual sources (Future.Expiry.Progress.Response.financeAlong actual)
          (Financial.Family.Migration.Posting.Balance.assigned sources) side party good window
  balance : ∀ selected side party good,
    FinancingBook.Posting.position sources (flow actual).after selected side party good +
      FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.payment sources) selected side party good (fun _ => true) =
    FinancingBook.Posting.position sources (before first) selected side party good +
      FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.issued sources) selected side party good (fun _ => true) +
      FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.assigned sources) selected side party good (fun _ => true)
  charge_balance : ∀ selected party good, charge actual selected party good =
    FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.issued sources) selected .debit party good (fun _ => true) -
    FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.issued sources) selected .credit party good (fun _ => true) +
    FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.assigned sources) selected .debit party good (fun _ => true) -
    FinancingBook.Posting.tally sources (flow actual).rows (FinancingBook.Posting.assigned sources) selected .credit party good (fun _ => true)
  native_net : ∀ party good, charge actual true party good + charge actual false party good =
    Posting.actual actual .debit party good - Posting.actual actual .credit party good +
    FinancialBalance.positions last .debit party good - FinancialBalance.positions first .debit party good -
    FinancialBalance.positions last .credit party good + FinancialBalance.positions first .credit party good

theorem receive : Receipt actual where
  original_slots := (flow actual).after.slots_exact
  original_events := (flow actual).events_exact
  all_positions := FinancingBook.Posting.position_partition sources (flow actual).after
  payments := FinancingBook.Posting.tally_partition sources (flow actual)
    (FinancingBook.Posting.payment sources) (Financial.Family.Migration.Posting.amount sources)
    (FinancingBook.Posting.payment_partition sources)
  issues := FinancingBook.Posting.tally_partition sources (flow actual)
    (FinancingBook.Posting.issued sources) (Financial.Family.Migration.Posting.Balance.issued sources)
    (FinancingBook.Posting.issued_partition sources)
  assignments := FinancingBook.Posting.tally_partition sources (flow actual)
    (FinancingBook.Posting.assigned sources) (Financial.Family.Migration.Posting.Balance.assigned sources)
    (FinancingBook.Posting.assigned_partition sources)
  balance := FinancingBook.Posting.run_balance sources _ (before first)
  charge_balance := FinancingBook.Posting.nativeCharge_balance sources _ (before first)
  native_net := FinancingBook.Posting.nativeCharge_partition sources (flow actual)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.FinancingBook
