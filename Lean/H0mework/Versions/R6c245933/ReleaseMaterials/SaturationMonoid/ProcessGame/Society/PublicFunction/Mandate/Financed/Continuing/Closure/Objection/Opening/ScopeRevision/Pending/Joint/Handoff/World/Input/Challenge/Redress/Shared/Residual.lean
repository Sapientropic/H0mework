import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Service
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Finance

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Residual
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Input.Event Input.Event.Future.Expiry.Progress.Responsibility
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev staged := Dispatch.after (after inventory)

def serviceResponse (index : epoch.source.Slot) := Future.Service.response (staged inventory) index

def serviceFinal (index : epoch.source.Slot) :=
  Future.Expiry.Progress.Service.original (staged inventory) (Runtime.answer inventory) index

private theorem follow_cast_append {first middle last target : Packet} {origin : Origin}
    (earlier : Evolution first middle) (suffix : Evolution middle last) (same : last = target)
    (position : Located origin first) :
    follow (Eq.mp (congrArg (Evolution first) same) (Evolution.append earlier suffix)) position =
      follow (Eq.mp (congrArg (Evolution middle) same) suffix) (follow earlier position) := by
  cases same
  rfl

private theorem trace_service_tail (saved : Inventory epoch) (trace : Future.Expiry.Progress.Trace saved)
    (index : epoch.source.Slot) :
    (Future.Expiry.Progress.Service.original saved trace index).state =
      (transport trace.native (.currentService index)).state := by
  cases trace with
  | finish saved answer exact verdict =>
    cases exact
    rfl
  | advance saved answer exact next same included tail =>
    cases exact
    let position : Located (Row.currentService (packet := ⟨epoch,saved⟩) index).origin ⟨epoch,saved⟩ :=
      ⟨.currentService index,rfl⟩
    exact congrArg (fun location => (follow tail.native location).state)
      (follow_cast_append (.submit saved (Future.ownWord saved))
        (completionEvolution (Event.response saved (Future.ownWord saved)).original.decision) same position).symm

private theorem service_final_is_the_original_row (index : epoch.source.Slot) :
    (serviceFinal inventory index).state = (Runtime.originalRow inventory (.currentService index)).state := by
  exact trace_service_tail (staged inventory) (Runtime.answer inventory) index

theorem every_live_service_event_is_in_its_original_final_row (index : epoch.source.Slot)
    (live : ((staged inventory).services index).state.current.LiveAt 0) :
    Future.Service.image (staged inventory) index ∈ (Runtime.originalRow inventory (.currentService index)).state.history := by
  have recorded := Future.Expiry.Progress.Service.the_original_service_event_is_in_the_final_native_history
    (staged inventory) (Runtime.answer inventory) index live
  rw [← service_final_is_the_original_row inventory index]
  exact recorded

structure ServiceReceipt (index : epoch.source.Slot) where
  private mk ::
  response : OutstandingSource.History.NativeService.Response.Disposition epoch.source
    ((staged inventory).services index) (Future.ownWord (staged inventory))
  exact : response = serviceResponse inventory index
  word : (Future.Expiry.Progress.Service.rootActual (staged inventory)).submitted = Future.ownWord (staged inventory)
  cut : (Future.Expiry.Progress.Service.rootActual (staged inventory)).before = current epoch (staged inventory).inputs
  recorded : ((staged inventory).services index).state.current.LiveAt 0 →
    Future.Service.image (staged inventory) index ∈ (Runtime.originalRow inventory (.currentService index)).state.history

def service (index : epoch.source.Slot) : ServiceReceipt inventory index :=
  ⟨serviceResponse inventory index,rfl,
    (Future.Expiry.Progress.Service.actual_source_word_and_original_cut (staged inventory)).1,
    (Future.Expiry.Progress.Service.actual_source_word_and_original_cut (staged inventory)).2,
    every_live_service_event_is_in_its_original_final_row inventory index⟩

variable (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
  (present : inventory.finance.current.slots[index]? = some slot)

def atShared := Financial.Family.Migration.follow sources (World.financialRun inventory (word inventory)) index slot present

def atRepayment := Dispatch.Finance.originalAtRepayment (after inventory) index
  (atShared inventory index slot present).slot (atShared inventory index slot present).present

def shares := Dispatch.Finance.shares (after inventory) index
  (atShared inventory index slot present).slot (atShared inventory index slot present).present

theorem a_nonpositive_original_share_is_exactly_zero
    (obligation : AdmittedObligation (Financial.Family.vocabulary sources))
    (saved : (atRepayment inventory index slot present).slot = .live obligation)
    (creditor : Bool)
    (nonpositive : Financial.BalanceConservation.shareAt (sources obligation.content.1) obligation.residual creditor ≤ 0) :
    Financial.BalanceConservation.shareAt (sources obligation.content.1) obligation.residual creditor = 0 := by
  have atSlot := (atRepayment inventory index slot present).present
  rw [saved] at atSlot
  have member := List.mem_of_getElem? atSlot
  have nonnegative := (Financial.Family.generated_sound sources
    (Input.staged (after inventory) (Dispatch.intent (after inventory))).finance (.live obligation) member).2 creditor
  exact le_antisymm nonpositive nonnegative

inductive FinanceDisposition where
  | private archived (archive : TerminalArchive (Financial.Family.vocabulary sources))
      (saved : (atRepayment inventory index slot present).slot = .terminal archive)
  | private liveQuiet (obligation : AdmittedObligation (Financial.Family.vocabulary sources))
      (saved : (atRepayment inventory index slot present).slot = .live obligation)
      (zero : ∀ creditor : Bool, Financial.BalanceConservation.shareAt
        (sources obligation.content.1) obligation.residual creditor = 0)
  | private liveResponding (obligation : AdmittedObligation (Financial.Family.vocabulary sources))
      (saved : (atRepayment inventory index slot present).slot = .live obligation)
      (creditor : Bool) (positive : 0 < Financial.BalanceConservation.shareAt
        (sources obligation.content.1) obligation.residual creditor)

def financeDisposition : FinanceDisposition inventory index slot present := by
  cases saved : (atRepayment inventory index slot present).slot with
  | terminal archive => exact .archived archive saved
  | live obligation =>
    by_cases first : 0 < Financial.BalanceConservation.shareAt (sources obligation.content.1) obligation.residual false
    · exact .liveResponding obligation saved false first
    · by_cases second : 0 < Financial.BalanceConservation.shareAt (sources obligation.content.1) obligation.residual true
      · exact .liveResponding obligation saved true second
      · exact .liveQuiet obligation saved (by
          intro creditor
          apply a_nonpositive_original_share_is_exactly_zero inventory index slot present obligation saved creditor
          cases creditor <;> exact le_of_not_gt ‹_›)

inductive FinanceKind where
  | archived | liveQuiet | liveResponding
  deriving DecidableEq, Repr

def FinanceDisposition.kind : FinanceDisposition inventory index slot present → FinanceKind
  | .archived .. => .archived | .liveQuiet .. => .liveQuiet | .liveResponding .. => .liveResponding

theorem every_positive_original_share_has_its_own_actual_attempt
    (obligation : AdmittedObligation (Financial.Family.vocabulary sources)) (creditor : Bool)
    (saved : (atRepayment inventory index slot present).slot = .live obligation)
    (positive : 0 < Financial.BalanceConservation.shareAt (sources obligation.content.1) obligation.residual creditor) :
    ∃ receipt ∈ shares inventory index slot present,
      receipt.obligation = obligation ∧ receipt.creditor = creditor :=
  Dispatch.Finance.every_positive_original_share_is_in_the_actual_repayment_menu (after inventory) index
    (atShared inventory index slot present).slot (atShared inventory index slot present).present obligation creditor saved positive

theorem an_empty_live_menu_cannot_erase_the_original_live_slot
    (obligation : AdmittedObligation (Financial.Family.vocabulary sources))
    (saved : (atRepayment inventory index slot present).slot = .live obligation)
    (empty : shares inventory index slot present = []) :
    ∀ creditor : Bool, Financial.BalanceConservation.shareAt (sources obligation.content.1) obligation.residual creditor ≤ 0 := by
  intro creditor
  apply le_of_not_gt
  intro positive
  obtain ⟨receipt,member,_⟩ := every_positive_original_share_has_its_own_actual_attempt
    inventory index slot present obligation creditor saved positive
  rw [empty] at member
  cases member

theorem the_repayment_cut_keeps_the_same_original_claim :
    Financial.Family.slotClaim sources (atRepayment inventory index slot present).slot = Financial.Family.slotClaim sources slot :=
  (atRepayment inventory index slot present).path.preserves_claim sources |>.trans
    ((atShared inventory index slot present).path.preserves_claim sources)

theorem the_complete_original_slot_is_accounted_on_the_same_shared_path :
    Financial.Family.Migration.principal sources (Runtime.finance inventory index slot present).slot +
      (Runtime.finance inventory index slot present).path.paid sources = Financial.Family.Migration.principal sources slot ∧
    (Runtime.finance inventory index slot present).path.paid sources =
      (((Future.Expiry.Progress.Response.financeAlong (Runtime.native inventory)).events.filter (fun event => event.slot == index)).map
        (fun event => Financial.Family.Migration.retired sources (Financial.Family.Migration.sourceEvent sources event))).sum :=
  ⟨(Runtime.finance inventory index slot present).path.conservation sources,
    (Runtime.finance inventory index slot present).payment_is_exactly_the_actual_slot_records sources⟩

abbrev ActualShare := Dispatch.Finance.ShareReceipt (after inventory) index
  (atShared inventory index slot present).slot (atShared inventory index slot present).present

abbrev repaymentActual := Dispatch.Finance.repaymentActual (after inventory)

theorem the_dispatch_tail_reaches_the_same_original_final_slot :
    (Dispatch.Finance.originalSlot (after inventory) index
      (atShared inventory index slot present).slot (atShared inventory index slot present).present).slot =
      (Runtime.finance inventory index slot present).slot := by
  have tail := (Dispatch.Finance.originalSlot (after inventory) index
    (atShared inventory index slot present).slot (atShared inventory index slot present).present).present
  have whole := (Runtime.finance inventory index slot present).present
  exact Option.some.inj (tail.symm.trans whole)

def ActualShare.before (receipt : ActualShare inventory index slot present) :=
  (Dispatch.Finance.ShareReceipt.slice (after inventory) receipt).before

def ActualShare.position (receipt : ActualShare inventory index slot present) :=
  Dispatch.Finance.ShareReceipt.position (after inventory) receipt

def ActualShare.AcceptedOrBlocked (receipt : ActualShare inventory index slot present) : Prop :=
    (∃ item ∈ (Mandate.law base epoch.scope).rawItems (repaymentActual inventory).before (repaymentActual inventory).submitted,
      item.before = Repayment.readyCurrent (Mandate.law base epoch.scope)
        (receipt.position inventory index slot present) (receipt.before inventory index slot present) ∧
      item.request = Repayment.payment (Mandate.law base epoch.scope)
        (receipt.position inventory index slot present) (receipt.before inventory index slot present) ∧
      (Mandate.law base epoch.scope).Valid item.before item.request) ∨
    Repayment.quantity (Mandate.law base epoch.scope)
      (receipt.position inventory index slot present) (receipt.before inventory index slot present) ≤ 0 ∨
    ∃ item ∈ (Mandate.law base epoch.scope).rawItems (receipt.before inventory index slot present)
        (Repayment.candidate (Mandate.law base epoch.scope)
          (receipt.position inventory index slot present) (receipt.before inventory index slot present)),
      Repayment.Portfolio.shifted (Dispatch.Finance.ShareReceipt.slice (after inventory) receipt).front.length item ∈
        (Mandate.law base epoch.scope).rawItems (repaymentActual inventory).before (repaymentActual inventory).submitted ∧
      ¬ (Mandate.law base epoch.scope).Valid item.before item.request

theorem every_original_share_has_its_actual_source_response (receipt : ActualShare inventory index slot present) :
    receipt.AcceptedOrBlocked inventory index slot present := by
  let law := Mandate.law base epoch.scope
  let position := receipt.position inventory index slot present
  let slice := Dispatch.Finance.ShareReceipt.slice (after inventory) receipt
  by_cases ready : Repayment.Ready law position slice.before
  · exact Or.inl (Dispatch.Finance.ShareReceipt.the_ready_payment_is_accepted_in_the_original_final_source
      (after inventory) receipt ready)
  · right
    by_cases quantity : 0 < Repayment.quantity law position slice.before
    · right
      have refusal : ∃ item ∈ law.rawItems slice.before (Repayment.candidate law position slice.before),
          ¬ law.Valid item.before item.request := by
        by_contra absent
        apply ready
        refine ⟨quantity,?_⟩
        intro item member
        by_contra refused
        exact absent ⟨item,member,refused⟩
      obtain ⟨item,member,refused⟩ := refusal
      have positive := Dispatch.Finance.ShareReceipt.positive_at_its_own_actual_cut (after inventory) receipt
      have inRepair : item ∈ law.rawItems slice.before (Repayment.Portfolio.Repair.word law position slice.before) := by
        rw [Repayment.Portfolio.Repair.blocked_word_contains_the_candidate law position slice.before positive ready]
        unfold RawLaw.rawItems
        rw [law.execute_append]
        exact List.mem_append_left _ member
      refine ⟨item,member,?_,refused⟩
      rw [(Dispatch.Finance.the_original_root_executes_this_own_repayment (after inventory)).1,
        (Dispatch.Finance.the_original_root_executes_this_own_repayment (after inventory)).2]
      exact slice.item_is_in_the_whole_trace law item inRepair
    · exact Or.inl (le_of_not_gt quantity)

structure FinancialReceipt where
  private mk ::
  disposition : FinanceDisposition inventory index slot present
  exact : disposition = financeDisposition inventory index slot present
  claim : Financial.Family.slotClaim sources (atRepayment inventory index slot present).slot = Financial.Family.slotClaim sources slot
  finalSlot : (Dispatch.Finance.originalSlot (after inventory) index
      (atShared inventory index slot present).slot (atShared inventory index slot present).present).slot =
      (Runtime.finance inventory index slot present).slot
  conservation : Financial.Family.Migration.principal sources (Runtime.finance inventory index slot present).slot +
      (Runtime.finance inventory index slot present).path.paid sources = Financial.Family.Migration.principal sources slot
  allocation : (Runtime.finance inventory index slot present).path.paid sources =
      (((Future.Expiry.Progress.Response.financeAlong (Runtime.native inventory)).events.filter (fun event => event.slot == index)).map
        (fun event => Financial.Family.Migration.retired sources (Financial.Family.Migration.sourceEvent sources event))).sum
  word : (repaymentActual inventory).submitted = Input.repayment (after inventory) (Dispatch.intent (after inventory))
  cut : (repaymentActual inventory).before = current epoch (Input.staged (after inventory) (Dispatch.intent (after inventory))).inputs
  coverage : ∀ (obligation : AdmittedObligation (Financial.Family.vocabulary sources)) (creditor : Bool),
    (atRepayment inventory index slot present).slot = .live obligation →
    0 < Financial.BalanceConservation.shareAt (sources obligation.content.1) obligation.residual creditor →
    ∃ receipt ∈ shares inventory index slot present, receipt.obligation = obligation ∧ receipt.creditor = creditor
  responses : ∀ receipt : ActualShare inventory index slot present, receipt.AcceptedOrBlocked inventory index slot present

def financial : FinancialReceipt inventory index slot present :=
  ⟨financeDisposition inventory index slot present,rfl,
    the_repayment_cut_keeps_the_same_original_claim inventory index slot present,
    the_dispatch_tail_reaches_the_same_original_final_slot inventory index slot present,
    (the_complete_original_slot_is_accounted_on_the_same_shared_path inventory index slot present).1,
    (the_complete_original_slot_is_accounted_on_the_same_shared_path inventory index slot present).2,
    (Dispatch.Finance.the_original_root_executes_this_own_repayment (after inventory)).1,
    (Dispatch.Finance.the_original_root_executes_this_own_repayment (after inventory)).2,
    every_positive_original_share_has_its_own_actual_attempt inventory index slot present,
    every_original_share_has_its_actual_source_response inventory index slot present⟩

omit index slot present in
structure Receipt where
  private mk ::
  services : ∀ index : epoch.source.Slot, ServiceReceipt inventory index
  financial : ∀ (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot), FinancialReceipt inventory index slot present

omit index slot present in
def produce : Receipt inventory := ⟨service inventory,financial inventory⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Residual
