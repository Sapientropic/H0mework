import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Accounting
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Financial
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch

/-! The actual joint response explains each original financial slot by its
own allocated payments, preserving the complete original claim and source. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Finance
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def run := Progress.Response.financeAlong (native inventory)

def originalSlot (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :=
  finance inventory index slot present

def paid (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :=
  (originalSlot inventory index slot present).path.paid sources

def census : List (Sigma fun index : Fin inventory.finance.current.slots.length =>
    Financial.Family.Migration.Follow sources (run inventory) index.val (inventory.finance.current.slots.get index)) :=
  (List.finRange _).map fun index =>
    ⟨index,originalSlot inventory index.val (inventory.finance.current.slots.get index)
      (List.getElem?_eq_getElem index.isLt)⟩

theorem every_original_slot_is_accounted (index : Fin inventory.finance.current.slots.length) :
    (⟨index,originalSlot inventory index.val (inventory.finance.current.slots.get index)
      (List.getElem?_eq_getElem index.isLt)⟩ : Sigma fun index : Fin inventory.finance.current.slots.length =>
        Financial.Family.Migration.Follow sources (run inventory) index.val (inventory.finance.current.slots.get index)) ∈ census inventory :=
  List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩

theorem exact_original_principal_disposition (index : Nat)
    (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :
    Financial.Family.Migration.principal sources (originalSlot inventory index slot present).slot + paid inventory index slot present =
      Financial.Family.Migration.principal sources slot ∧
    Financial.Family.Migration.identity sources (originalSlot inventory index slot present).slot =
      Financial.Family.Migration.identity sources slot ∧
    paid inventory index slot present =
      (((run inventory).events.filter (fun event => event.slot == index)).map
        (fun event => Financial.Family.Migration.retired sources (Financial.Family.Migration.sourceEvent sources event))).sum :=
  ⟨(originalSlot inventory index slot present).path.conservation sources,
    (originalSlot inventory index slot present).path.preserves_identity sources,
    (originalSlot inventory index slot present).payment_is_exactly_the_actual_slot_records sources⟩

theorem positive_retirement_has_an_actual_original_slot_receipt (index : Nat)
    (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot)
    (positive : 0 < paid inventory index slot present) :
    ∃ event ∈ (run inventory).events, event.slot = index ∧
      0 < Financial.Family.Migration.retired sources (Financial.Family.Migration.sourceEvent sources event) ∧
      (Financial.Family.Migration.sourceEvent sources event).claim sources = Financial.Family.slotClaim sources slot := by
  let moved := originalSlot inventory index slot present
  obtain ⟨event,member,amount⟩ := moved.path.positive_paid_has_an_actual_payment sources positive
  have mapped : event ∈ (moved.path.records sources index).map (Financial.Family.Migration.sourceEvent sources) := by
    rw [moved.path.records_sources sources index]
    exact member
  obtain ⟨actual,recorded,same⟩ := List.mem_map.mp mapped
  rw [moved.recorded] at recorded
  obtain ⟨inRun,atSlot⟩ := List.mem_filter.mp recorded
  refine ⟨actual,inRun,?_,?_,?_⟩
  · simpa only [beq_iff_eq] using atSlot
  · rw [same]; exact amount
  · rw [same]; exact moved.path.events_preserve_original_claim sources event member

def originalAtRepayment (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :=
  Financial.Family.Migration.follow sources (World.financialRun inventory (word inventory)) index slot present

theorem the_saved_repayment_slot_is_the_original_claim (index : Nat)
    (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :
    Financial.Family.slotClaim sources (originalAtRepayment inventory index slot present).slot =
      Financial.Family.slotClaim sources slot :=
  (originalAtRepayment inventory index slot present).path.preserves_claim sources

def repaymentIndex (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :
    Fin (Input.staged inventory (intent inventory)).finance.current.slots.length := by
  refine ⟨index,?_⟩
  have saved := (originalAtRepayment inventory index slot present).present
  exact (List.getElem?_eq_some_iff.mp saved).1

def originalShareSlice (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot)
    (obligation : AdmittedObligation (Financial.Family.vocabulary sources)) (creditor : Bool)
    (survives : (originalAtRepayment inventory index slot present).slot = .live obligation)
    (positive : 0 < Financial.BalanceConservation.shareAt
      (sources obligation.content.1) obligation.residual creditor) :=
  Input.Financial.ownSlice inventory (intent inventory) (repaymentIndex inventory index slot present)
    obligation creditor (by
      have saved := (originalAtRepayment inventory index slot present).present
      rw [survives] at saved
      exact (List.getElem?_eq_some_iff.mp saved).2) positive


structure ShareReceipt (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) where
  private mk ::
  obligation : AdmittedObligation (Financial.Family.vocabulary sources)
  creditor : Bool
  survives : (originalAtRepayment inventory index slot present).slot = .live obligation
  positive : 0 < Financial.BalanceConservation.shareAt
    (sources obligation.content.1) obligation.residual creditor

def shares (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) : List (ShareReceipt inventory index slot present) :=
  match survives : (originalAtRepayment inventory index slot present).slot with
  | .terminal _ => []
  | .live obligation => [false,true].attach.filterMap fun creditor =>
      if positive : 0 < Financial.BalanceConservation.shareAt
          (sources obligation.content.1) obligation.residual creditor.val then
        some ⟨obligation,creditor.val,survives,positive⟩ else none

def ShareReceipt.slice {index : Nat} {slot : ObligationSlot (Financial.Family.vocabulary sources)}
    {present : inventory.finance.current.slots[index]? = some slot}
    (receipt : ShareReceipt inventory index slot present) :=
  originalShareSlice inventory index slot present receipt.obligation receipt.creditor receipt.survives receipt.positive

theorem every_positive_original_share_is_in_the_actual_repayment_menu (index : Nat)
    (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot)
    (obligation : AdmittedObligation (Financial.Family.vocabulary sources)) (creditor : Bool)
    (survives : (originalAtRepayment inventory index slot present).slot = .live obligation)
    (positive : 0 < Financial.BalanceConservation.shareAt
      (sources obligation.content.1) obligation.residual creditor) :
    ∃ receipt ∈ shares inventory index slot present,
      receipt.obligation = obligation ∧ receipt.creditor = creditor := by
  refine ⟨⟨obligation,creditor,survives,positive⟩,?_,rfl,rfl⟩
  unfold shares
  split
  next archive same => cases same.symm.trans survives
  next old same =>
    have equal : old = obligation := ObligationSlot.live.inj (same.symm.trans survives)
    cases equal
    cases creditor <;> simp [positive]


def repaymentActual := OutstandingSource.History.actualExecution epoch.source (trace inventory).finalInputs
  ((Input.staged inventory (intent inventory)).inputs.length+1)

theorem the_original_root_executes_this_own_repayment :
    (repaymentActual inventory).submitted = Input.repayment inventory (intent inventory) ∧
    (repaymentActual inventory).before = current epoch (Input.staged inventory (intent inventory)).inputs := by
  have seen : (Input.staged inventory (intent inventory)).inputs ++ [Input.repayment inventory (intent inventory)] <+:
      (trace inventory).finalInputs := (trace inventory).saved_inputs_are_in_the_final_source
  obtain ⟨suffix,same⟩ := seen
  unfold repaymentActual
  rw [← same]
  constructor
  · rw [OutstandingSource.History.scheduled_input_is_actual epoch.source _
      (Input.staged inventory (intent inventory)).inputs.length (by simp)]
    simp
  · change OutstandingSource.History.currentAt epoch.source
      (((Input.staged inventory (intent inventory)).inputs ++ [Input.repayment inventory (intent inventory)]) ++ suffix)
      ((Input.staged inventory (intent inventory)).inputs.length+2) = _
    rw [(OutstandingSource.History.actual_frame _ _ _).1,List.append_assoc,
      OutstandingSource.History.extending_inputs_preserves_its_executed_prefix epoch.source
        (Input.staged inventory (intent inventory)).inputs ([Input.repayment inventory (intent inventory)] ++ suffix) _ (Nat.le_refl _)]
    exact (OutstandingSource.History.actual_frame epoch.source (Input.staged inventory (intent inventory)).inputs _).1.symm


namespace ShareReceipt
variable {index : Nat} {slot : ObligationSlot (Financial.Family.vocabulary sources)}
  {present : inventory.finance.current.slots[index]? = some slot}
  (receipt : ShareReceipt inventory index slot present)

def position := Input.Financial.sharePosition receipt.obligation receipt.creditor

def response := Repayment.respond (Mandate.law base epoch.scope) (position inventory receipt)
  (slice inventory receipt).before

theorem positive_at_its_own_actual_cut :
    0 < Repayment.balance (position inventory receipt) (slice inventory receipt).before :=
  Input.Financial.ownSlice_positive inventory (intent inventory) (repaymentIndex inventory index slot present)
    receipt.obligation receipt.creditor (by
      have saved := (originalAtRepayment inventory index slot present).present
      rw [receipt.survives] at saved
      exact (List.getElem?_eq_some_iff.mp saved).2) receipt.positive

theorem the_payment_attempt_is_in_the_original_final_source :
    ∃ item ∈ (Mandate.law base epoch.scope).rawItems (repaymentActual inventory).before
        (repaymentActual inventory).submitted,
      item.before = Repayment.readyCurrent (Mandate.law base epoch.scope) (position inventory receipt)
        (slice inventory receipt).before ∧
      item.request = Repayment.payment (Mandate.law base epoch.scope) (position inventory receipt)
        (slice inventory receipt).before := by
  have actual := Input.Financial.positive_slice_payment_is_an_actual_item inventory (intent inventory)
    (position inventory receipt) (slice inventory receipt) (positive_at_its_own_actual_cut inventory receipt)
  rw [(Input.actual_repayment_word_and_cut inventory (intent inventory)).1,
    (Input.actual_repayment_word_and_cut inventory (intent inventory)).2] at actual
  rw [(the_original_root_executes_this_own_repayment inventory).1,
    (the_original_root_executes_this_own_repayment inventory).2]
  exact actual

theorem the_ready_payment_is_accepted_in_the_original_final_source
    (ready : Repayment.Ready (Mandate.law base epoch.scope) (position inventory receipt)
      (slice inventory receipt).before) :
    ∃ item ∈ (Mandate.law base epoch.scope).rawItems (repaymentActual inventory).before
        (repaymentActual inventory).submitted,
      item.before = Repayment.readyCurrent (Mandate.law base epoch.scope) (position inventory receipt)
        (slice inventory receipt).before ∧
      item.request = Repayment.payment (Mandate.law base epoch.scope) (position inventory receipt)
        (slice inventory receipt).before ∧ (Mandate.law base epoch.scope).Valid item.before item.request := by
  rw [(the_original_root_executes_this_own_repayment inventory).1,
    (the_original_root_executes_this_own_repayment inventory).2]
  exact (slice inventory receipt).ready_payment_is_in_the_whole_trace _ ready

theorem a_failed_own_slice_has_its_own_source_obstruction
    (failed : ¬ Repayment.Ready (Mandate.law base epoch.scope) (position inventory receipt)
      (slice inventory receipt).before) :
    Repayment.quantity (Mandate.law base epoch.scope) (position inventory receipt) (slice inventory receipt).before ≤ 0 ∨
      ∃ item ∈ (Mandate.law base epoch.scope).rawItems (repaymentActual inventory).before
          (repaymentActual inventory).submitted,
        ¬ (Mandate.law base epoch.scope).Valid item.before item.request := by
  have actual := Input.Financial.positive_slice_has_a_typed_obstruction inventory (intent inventory)
    (position inventory receipt) (slice inventory receipt) (positive_at_its_own_actual_cut inventory receipt) failed
  rw [(Input.actual_repayment_word_and_cut inventory (intent inventory)).1,
    (Input.actual_repayment_word_and_cut inventory (intent inventory)).2] at actual
  rw [(the_original_root_executes_this_own_repayment inventory).1,
    (the_original_root_executes_this_own_repayment inventory).2]
  exact actual

theorem actual_paid_or_typed_blocker :
    (∃ item ∈ (Mandate.law base epoch.scope).rawItems (repaymentActual inventory).before
        (repaymentActual inventory).submitted,
      item.before = Repayment.readyCurrent (Mandate.law base epoch.scope) (position inventory receipt)
        (slice inventory receipt).before ∧
      item.request = Repayment.payment (Mandate.law base epoch.scope) (position inventory receipt)
        (slice inventory receipt).before ∧ (Mandate.law base epoch.scope).Valid item.before item.request) ∨
    Repayment.quantity (Mandate.law base epoch.scope) (position inventory receipt) (slice inventory receipt).before ≤ 0 ∨
      ∃ item ∈ (Mandate.law base epoch.scope).rawItems (repaymentActual inventory).before
          (repaymentActual inventory).submitted,
        ¬ (Mandate.law base epoch.scope).Valid item.before item.request := by
  by_cases ready : Repayment.Ready (Mandate.law base epoch.scope) (position inventory receipt)
      (slice inventory receipt).before
  · exact Or.inl (the_ready_payment_is_accepted_in_the_original_final_source inventory receipt ready)
  · exact Or.inr (a_failed_own_slice_has_its_own_source_obstruction inventory receipt ready)

theorem every_generated_shortage_and_repair_is_in_the_original_final_source
    (failed : ¬ Repayment.Ready (Mandate.law base epoch.scope) (position inventory receipt)
      (slice inventory receipt).before)
    (order : Repayment.Portfolio.Repair.Order (Mandate.law base epoch.scope) (position inventory receipt)
      (slice inventory receipt).before)
    (member : order ∈ Repayment.Portfolio.Repair.orders (Mandate.law base epoch.scope)
      (position inventory receipt) (slice inventory receipt).before) :
    Repayment.Portfolio.shifted (slice inventory receipt).front.length order.failed ∈
      (Mandate.law base epoch.scope).rawItems (repaymentActual inventory).before (repaymentActual inventory).submitted ∧
    ¬ (Mandate.law base epoch.scope).Valid order.failed.before order.failed.request ∧
    0 < order.debit.2 - order.failed.before.stock order.debit.1.1 order.debit.1.2 ∧
    order.request ∈ (repaymentActual inventory).submitted := by
  have actual := (slice inventory receipt).failed_candidate_and_generated_repair_are_actual _
    (positive_at_its_own_actual_cut inventory receipt) failed order member
  rw [(the_original_root_executes_this_own_repayment inventory).1,
    (the_original_root_executes_this_own_repayment inventory).2]
  exact ⟨actual.1,order.refused,order.shortfall,actual.2.2⟩

end ShareReceipt

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Finance
