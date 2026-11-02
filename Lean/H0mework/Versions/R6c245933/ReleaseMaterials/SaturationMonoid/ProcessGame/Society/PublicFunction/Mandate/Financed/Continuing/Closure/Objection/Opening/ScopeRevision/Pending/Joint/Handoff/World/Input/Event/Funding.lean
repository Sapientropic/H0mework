import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Funding.Cash
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.FinancingBook.Cash

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Funding
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration.Posting
noncomputable section
variable {first last : Packet} (actual : Evolution first last)

def before (packet : Packet) := Financial.Family.Migration.Funding.generated sources packet.2.finance

def flow := Financial.Family.Migration.Funding.fold sources
  (Future.Expiry.Progress.Response.financeAlong actual) (before first)

def charge := Financial.Family.Migration.FinancingBook.Posting.nativeCharge sources (flow actual)

def total (entries : List (VisitReceipt sources)) (selected credit : Bool) (party : Bool) (good : Good) : ℚ :=
  (entries.map fun receipt => Financial.Family.Migration.Funding.Cash.cash sources receipt selected credit party good).sum

theorem debit_partition (entries : List (VisitReceipt sources)) (party : Bool) (good : Good) :
    total entries true false party good + total entries false false party good =
      PublicFunction.Costs.Visits.total sources (entries.map (VisitReceipt.window sources)) party (.operating good) := by
  induction entries with
  | nil => simp only [total,List.map_nil,List.sum_nil,PublicFunction.Costs.Visits.total,Pi.zero_apply,add_zero]
  | cons receipt rest ih =>
      have head := Financial.Family.Migration.Funding.Cash.cash_partition sources receipt false party good
      change _ = PublicFunction.Costs.Visits.atVisit sources (receipt.window sources) party (.operating good) at head
      simp only [total,List.map_cons,List.sum_cons,PublicFunction.Costs.Visits.total,Pi.add_apply] at ih ⊢
      linarith

theorem credit_partition (entries : List (VisitReceipt sources)) (party : Bool) (good : Good) :
    total entries true true party good + total entries false true party good =
      FinancialBalance.otherTotal (entries.map (VisitReceipt.window sources)) party good := by
  induction entries with
  | nil => simp only [total,List.map_nil,List.sum_nil,FinancialBalance.otherTotal,add_zero]
  | cons receipt rest ih =>
      have head := Financial.Family.Migration.Funding.Cash.cash_partition sources receipt true party good
      change _ = FinancialBalance.otherAt (receipt.window sources) party good at head
      simp only [total,List.map_cons,List.sum_cons,FinancialBalance.otherTotal] at ih ⊢
      linarith

def account (selected : Bool) (party : Bool) (good : Good) : ℚ :=
  total (Posting.receipts actual) selected false party good - total (Posting.receipts actual) selected true party good +
    charge actual selected party good

theorem actual_net_position_change (party : Bool) (good : Good) :
    account actual true party good + account actual false party good =
      FinancialBalance.quotedNet first party good - FinancialBalance.quotedNet last party good := by
  have debit := debit_partition (Posting.receipts actual) party good
  have credit := credit_partition (Posting.receipts actual) party good
  rw [Posting.keys actual] at debit credit
  change _ = Costs.cost actual party (.operating good) at debit
  change _ = FinancialBalance.otherCredits actual party good at credit
  have native := Financial.Family.Migration.FinancingBook.Posting.nativeCharge_partition sources (flow actual) party good
  change charge actual true party good + charge actual false party good =
    Posting.actual actual .debit party good - Posting.actual actual .credit party good +
    FinancialBalance.positions last .debit party good - FinancialBalance.positions first .debit party good -
    FinancialBalance.positions last .credit party good + FinancialBalance.positions first .credit party good at native
  have debitBalance := FinancialBalance.financial_balance actual .debit party good
  have creditBalance := FinancialBalance.financial_balance actual .credit party good
  have noAssignmentDebt : FinancialBalance.assignments actual .debit party good = 0 := by
    unfold FinancialBalance.assignments Balance.assignments
    simp only [Balance.assignment_debit,List.map_const',List.sum_replicate,nsmul_zero]
  have original := FinancialBalance.actual_net_balance actual party good
  unfold account
  linarith only [debit,credit,native,debitBalance,creditBalance,noAssignmentDebt,original]

theorem selected_cash_keeps_its_same_actual_native_event
    (receipt : VisitReceipt sources) (visited : receipt ∈ Posting.receipts actual) (index : Nat)
    (selected : Financial.Family.Migration.Funding.Cash.selected sources receipt index = true) :
    ∃ row ∈ (Financial.Family.Migration.Funding.Cash.flow sources receipt).rows,
      Financial.Family.Migration.Funding.Cash.Checked sources row index ∧
      row.native ∈ (Future.Expiry.Progress.Response.financeAlong actual).events ∧
      ∃ item ∈ Financial.Family.Migration.DelayedFinancing.Cash.rawItems sources receipt, item.index = index := by
  obtain ⟨row,member,checked,native,original⟩ :=
    Financial.Family.Migration.Funding.Cash.selected_has_its_original_native_event_and_cash sources receipt index selected
  refine ⟨row,member,checked,?_,original⟩
  have inWindow : row.native ∈ ((Posting.receipts actual).map (fun entry => (entry.native sources).events)).flatten :=
    List.mem_flatten.mpr ⟨(receipt.native sources).events,List.mem_map.mpr ⟨receipt,visited,rfl⟩,native⟩
  rw [Posting.events actual] at inWindow
  exact inWindow

structure Receipt where
  original_slots : (flow actual).after.cells.map Financial.Family.Migration.FinancingBook.Cell.slot = last.2.finance.current.slots
  original_events : (flow actual).rows.map Financial.Family.Migration.FinancingBook.Row.native =
    (Future.Expiry.Progress.Response.financeAlong actual).events
  branch_balance : ∀ selected side party good,
    Financial.Family.Migration.FinancingBook.Posting.position sources (flow actual).after selected side party good +
      Financial.Family.Migration.FinancingBook.Posting.tally sources (flow actual).rows
        (Financial.Family.Migration.FinancingBook.Posting.payment sources) selected side party good (fun _ => true) =
    Financial.Family.Migration.FinancingBook.Posting.position sources (before first) selected side party good +
      Financial.Family.Migration.FinancingBook.Posting.tally sources (flow actual).rows
        (Financial.Family.Migration.Funding.Posting.issued sources) selected side party good (fun _ => true) +
      Financial.Family.Migration.FinancingBook.Posting.tally sources (flow actual).rows
        (Financial.Family.Migration.FinancingBook.Posting.assigned sources) selected side party good (fun _ => true)
  actual_acquisitions : ∀ link ∈ Financial.Family.Migration.Funding.links sources (flow actual).rows,
    link.native ∈ (Future.Expiry.Progress.Response.financeAlong actual).events ∧
      0 < link.acquisition.funding.advance ∧
      0 < Financial.Family.Migration.AssignedFinancing.quantity sources link.entry.boundary ∧
      link.entry.boundary.receipt.recipient = link.acquisition.funding.controller
  complete_net : ∀ party good, account actual true party good + account actual false party good =
    FinancialBalance.quotedNet first party good - FinancialBalance.quotedNet last party good
  original_cash : ∀ receipt ∈ Posting.receipts actual, ∀ index,
    Financial.Family.Migration.Funding.Cash.selected sources receipt index = true →
    ∃ row ∈ (Financial.Family.Migration.Funding.Cash.flow sources receipt).rows,
      Financial.Family.Migration.Funding.Cash.Checked sources row index ∧
      row.native ∈ (Future.Expiry.Progress.Response.financeAlong actual).events ∧
      ∃ item ∈ Financial.Family.Migration.DelayedFinancing.Cash.rawItems sources receipt, item.index = index

theorem receive : Receipt actual where
  original_slots := (flow actual).after.slots_exact
  original_events := (flow actual).events_exact
  branch_balance := Financial.Family.Migration.Funding.Posting.run_balance sources _ (before first)
  actual_acquisitions := by
    intro link member
    have original := Financial.Family.Migration.Funding.every_link_is_its_original_actual_event sources (flow actual).rows link member
    rw [(flow actual).events_exact] at original
    exact ⟨original,link.acquisition.funding.advance_positive,link.acquisition.actual.2.2.2.2,link.acquisition.actual.2.2.1⟩
  complete_net := actual_net_position_change actual
  original_cash := selected_cash_keeps_its_same_actual_native_event actual

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Funding
