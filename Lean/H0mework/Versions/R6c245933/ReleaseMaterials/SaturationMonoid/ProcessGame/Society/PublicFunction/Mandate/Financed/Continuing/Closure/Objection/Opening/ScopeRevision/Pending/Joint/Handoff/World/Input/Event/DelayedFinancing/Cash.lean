import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.DelayedFinancing.Cash
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.DelayedFinancing

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.DelayedFinancing.Cash
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration.Posting
noncomputable section
variable {first last : Packet} (actual : Evolution first last)

def selected (receipt : VisitReceipt sources) :=
  Financial.Family.Migration.DelayedFinancing.Cash.selected sources receipt (DelayedFinancing.marked actual)

def total (entries : List (VisitReceipt sources)) (selected credit : Bool) (party : Bool) (good : Good) : ℚ :=
  (entries.map fun receipt => Financial.Family.Migration.DelayedFinancing.Cash.cash sources receipt
    (DelayedFinancing.marked actual) selected credit party good).sum

theorem debit_partition (entries : List (VisitReceipt sources)) (party : Bool) (good : Good) :
    total actual entries true false party good + total actual entries false false party good =
      PublicFunction.Costs.Visits.total sources (entries.map (VisitReceipt.window sources)) party (.operating good) := by
  induction entries with
  | nil => simp only [total,List.map_nil,List.sum_nil,PublicFunction.Costs.Visits.total,Pi.zero_apply,add_zero]
  | cons receipt rest ih =>
      have head := Financial.Family.Migration.DelayedFinancing.Cash.cash_partition sources receipt (DelayedFinancing.marked actual) false party good
      change _ = PublicFunction.Costs.Visits.atVisit sources (receipt.window sources) party (.operating good) at head
      simp only [total,List.map_cons,List.sum_cons,PublicFunction.Costs.Visits.total,Pi.add_apply] at ih ⊢
      linarith

theorem credit_partition (entries : List (VisitReceipt sources)) (party : Bool) (good : Good) :
    total actual entries true true party good + total actual entries false true party good =
      FinancialBalance.otherTotal (entries.map (VisitReceipt.window sources)) party good := by
  induction entries with
  | nil => simp only [total,List.map_nil,List.sum_nil,FinancialBalance.otherTotal,add_zero]
  | cons receipt rest ih =>
      have head := Financial.Family.Migration.DelayedFinancing.Cash.cash_partition sources receipt (DelayedFinancing.marked actual) true party good
      change _ = FinancialBalance.otherAt (receipt.window sources) party good at head
      simp only [total,List.map_cons,List.sum_cons,FinancialBalance.otherTotal] at ih ⊢
      linarith

def account (selected : Bool) (party : Bool) (good : Good) : ℚ :=
  total actual (Posting.receipts actual) selected false party good -
    total actual (Posting.receipts actual) selected true party good + DelayedFinancing.nativeCharge actual selected party good

theorem complete_actual_partition (party : Bool) (good : Good) :
    account actual true party good + account actual false party good =
      Costs.cost actual party (.operating good) - FinancialBalance.otherCredits actual party good -
        FinancialBalance.issues actual .credit party good + FinancialBalance.issues actual .debit party good -
          FinancialBalance.assignments actual .credit party good := by
  have debit := debit_partition actual (Posting.receipts actual) party good
  have credit := credit_partition actual (Posting.receipts actual) party good
  rw [Posting.keys actual] at debit credit
  have native := DelayedFinancing.actual_native_partition actual party good
  unfold account Costs.cost FinancialBalance.otherCredits
  linarith

theorem actual_net_position_change (party : Bool) (good : Good) :
    account actual true party good + account actual false party good =
      FinancialBalance.quotedNet first party good - FinancialBalance.quotedNet last party good := by
  rw [complete_actual_partition]
  have original := FinancialBalance.actual_net_balance actual party good
  linarith

theorem selected_cash_has_its_same_original_native_birth
    (receipt : VisitReceipt sources) (visited : receipt ∈ Posting.receipts actual) (index : Nat)
    (chosen : selected actual receipt index = true) :
    ∃ issue ∈ Financial.Family.Migration.DelayedFinancing.Cash.entries sources receipt,
      ∃ origin ∈ Financial.Family.Migration.DelayedFinancing.origins sources issue.original,
        origin.access.access.val.index = index ∧
        origin.access.access.val ∈ Financial.Family.Migration.DelayedFinancing.Cash.rawItems sources receipt ∧
        ∃ birth ∈ DelayedFinancing.births actual, birth.index = issue.slot ∧ birth.claim = issue.original ∧
          Nonempty (Financial.Family.Migration.DelayedFinancing.Returned sources birth) := by
  obtain ⟨issue,member,marked,origin,listed,same⟩ :=
    (Financial.Family.Migration.DelayedFinancing.Cash.selected_exact sources receipt _ index).mp chosen
  refine ⟨issue,member,origin,listed,same,
    Financial.Family.Migration.DelayedFinancing.Cash.original_advance_is_in_this_actual_receipt sources receipt issue member origin,?_⟩
  have localEvent := Financial.Family.Migration.DelayedFinancing.Cash.issued_event_is_actual sources _ _ issue
    (Financial.Family.Migration.DelayedFinancing.Cash.entry_record_is_actual sources receipt issue member)
  have inWindow : issue.admitted ∈ ((Posting.receipts actual).map (fun entry => (entry.native sources).events)).flatten :=
    List.mem_flatten.mpr ⟨(receipt.native sources).events,List.mem_map.mpr ⟨receipt,visited,rfl⟩,localEvent⟩
  rw [Posting.events actual] at inWindow
  have inFull : issue.admitted ∈ (DelayedFinancing.fullRun actual).events := by
    rw [DelayedFinancing.fullRun,NativeResponsibilityProcess.Run.events_concatRuns]
    exact List.mem_append_right _ inWindow
  obtain ⟨original,originalMember,originalIndex,originalClaim⟩ :=
    Financial.Family.Migration.DelayedFinancing.Cash.issued_event_has_its_original_birth sources (DelayedFinancing.fullRun actual) issue inFull
  obtain ⟨birth,inside,sameIndex,returned⟩ := DelayedFinancing.classified_slot_has_its_actual_original_return actual issue.slot marked
  have located : last.2.finance.current.slots[birth.index]? = some original.follow.slot := by
    rw [sameIndex,← originalIndex]; exact original.actual_slot
  have slots : birth.follow.slot = original.follow.slot := Option.some.inj (birth.actual_slot.symm.trans located)
  have claims : birth.claim = issue.original := birth.original_claim.symm.trans
    ((congrArg (Financial.Family.slotClaim sources) slots).trans (original.original_claim.trans originalClaim))
  exact ⟨birth,inside,sameIndex,claims,returned⟩
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.DelayedFinancing.Cash
