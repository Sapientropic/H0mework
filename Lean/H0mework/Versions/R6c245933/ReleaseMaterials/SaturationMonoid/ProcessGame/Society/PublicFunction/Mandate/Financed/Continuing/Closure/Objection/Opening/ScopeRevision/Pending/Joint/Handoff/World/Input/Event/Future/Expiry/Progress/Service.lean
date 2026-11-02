import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Service
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Transport

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Service
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Progress.Responsibility
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def afterIncoming (trace : Trace inventory) : Evolution ⟨epoch,World.submit inventory (ownWord inventory)⟩ trace.packet := by
  cases trace with
  | finish inventory answer exact verdict =>
    cases exact
    exact completionEvolution (Event.response inventory (ownWord inventory)).original.decision
  | advance inventory answer exact next same included tail =>
    cases exact
    have first := completionEvolution (Event.response inventory (ownWord inventory)).original.decision
    change Evolution _ (actual inventory).packet at first
    rw [same] at first
    exact .append first tail.native

def firstVisit : Visit (epoch := epoch) := ⟨inventory,actual inventory⟩

theorem first_visit_is_in_the_actual_trace (trace : Trace inventory) : firstVisit inventory ∈ trace.visits := by
  cases trace with
  | finish inventory answer exact verdict => simp only [firstVisit,Trace.visits,exact,List.mem_singleton]
  | advance inventory answer exact next same included tail => simp only [firstVisit,Trace.visits,exact,List.mem_cons_self]

def original (trace : Trace inventory) (index : epoch.source.Slot) :=
  follow (afterIncoming inventory trace)
    ((⟨Row.currentService index,rfl⟩ : Located (Row.currentService (packet := ⟨epoch,inventory⟩) index).origin ⟨epoch,inventory⟩).submit (ownWord inventory))

def response (index : epoch.source.Slot) := Future.Service.response inventory index

def rootActual := (Progress.Runtime.trace inventory).actualIncoming (firstVisit inventory)

theorem the_original_service_event_is_in_the_final_native_history (trace : Trace inventory) (index : epoch.source.Slot)
    (live : (inventory.services index).state.current.LiveAt 0) :
    Future.Service.image inventory index ∈ (original inventory trace index).state.history := by
  let position : Located (Row.currentService (packet := ⟨epoch,inventory⟩) index).origin ⟨epoch,inventory⟩ :=
    ⟨Row.currentService index,rfl⟩
  have retained := follow_retains_the_complete_original_history (afterIncoming inventory trace)
    (position.submit (ownWord inventory))
  have start : (position.submit (ownWord inventory)).state.history =
      ((World.submit inventory (ownWord inventory)).services index).state.current.history := rfl
  rw [start,Future.Service.the_actual_advance_records_the_original_service_event inventory index live] at retained
  obtain ⟨suffix,same⟩ := retained
  change Future.Service.image inventory index ∈ (follow (afterIncoming inventory trace) (position.submit (ownWord inventory))).state.history
  rw [← same]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem actual_source_word_and_original_cut :
    (rootActual inventory).submitted = ownWord inventory ∧
    (rootActual inventory).before = current epoch inventory.inputs :=
  (Progress.Runtime.trace inventory).every_incoming_is_actually_interpreted_by_the_final_source
    (firstVisit inventory) (first_visit_is_in_the_actual_trace inventory _)


theorem actual_native_payment_or_own_blocker (index : epoch.source.Slot)
    (live : (inventory.services index).state.current.LiveAt 0) :
    (epoch.source.SlotPaid (rootActual inventory).before (rootActual inventory).submitted index ∧
      ((World.submit inventory (ownWord inventory)).services index).state.current.TerminalAt 0 ∧
      (Future.Service.image inventory index).kind = .obligationTerminal) ∨
    (¬ epoch.source.SlotPaid (rootActual inventory).before (rootActual inventory).submitted index ∧
      Nonempty (OutstandingSource.History.NativeService.Response.Blocker epoch.source
        (rootActual inventory).before (rootActual inventory).submitted index) ∧
      ((World.submit inventory (ownWord inventory)).services index).state.current.LiveAt 0 ∧
      (Future.Service.image inventory index).kind = .maintained) := by
  have actual := OutstandingSource.History.NativeService.Response.live_paid_or_typed_blocker epoch.source
    (inventory.services index) live (ownWord inventory)
  rw [(OutstandingSource.History.NativeService.Response.actual_word_and_cut epoch.source inventory.inputs (ownWord inventory)).1,
    (OutstandingSource.History.NativeService.Response.actual_word_and_cut epoch.source inventory.inputs (ownWord inventory)).2] at actual
  rw [(actual_source_word_and_original_cut inventory).1,(actual_source_word_and_original_cut inventory).2]
  exact actual

theorem native_disposition_and_same_root_writeback_next (index : epoch.source.Slot)
    (live : (inventory.services index).state.current.LiveAt 0) :
    (rootActual inventory).submitted = ownWord inventory ∧
    (rootActual inventory).before = current epoch inventory.inputs ∧
    Future.Service.image inventory index ∈ (original inventory (Progress.Runtime.trace inventory) index).state.history ∧
    HEq (Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).tick.generated.wholeLedgerWriteBack
      ((Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).current.visit.current) ∧
    (Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).tick.nextCurrent =
      (Progress.Runtime.facade inventory).process.stateAt
        ((Progress.Runtime.facade inventory).process.successor
          (Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).state) := by
  have root := Progress.Runtime.full_source_original_account_writeback_and_next_are_consumed_together inventory
  exact ⟨(actual_source_word_and_original_cut inventory).1,(actual_source_word_and_original_cut inventory).2,
    the_original_service_event_is_in_the_final_native_history inventory _ index live,root.2.2.2.2.2.1,root.2.2.2.2.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Service
