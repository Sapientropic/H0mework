import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Grant
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Input.Event Input.Event.Future.Expiry.Progress.Responsibility
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def answer := Dispatch.trace (after inventory)
def dispatch := Dispatch.produce (after inventory)
def native : Evolution ⟨epoch,inventory⟩ (answer inventory).packet :=
  .append (.submit inventory (word inventory)) (Dispatch.native (after inventory))

def originalRow (row : Input.Event.Future.Expiry.Progress.Responsibility.Row ⟨epoch,inventory⟩) := transport (native inventory) row

def row (record : Record inventory) (member : record ∈ inventory.objections) :=
  (⟨Row.currentChallenge record member,rfl⟩ :
    Located (Row.currentChallenge (packet := ⟨epoch,inventory⟩) record member).origin ⟨epoch,inventory⟩)

def finalOriginal (record : Record inventory) (member : record ∈ inventory.objections) :=
  follow (Dispatch.native (after inventory)) ((row inventory record member).submit (word inventory))

def complete (record : Record inventory) (member : record ∈ inventory.objections) :=
  (finalOriginal inventory record member).complete

theorem the_entire_shared_native_disposition_is_consumed (record : Record inventory) (member : record ∈ inventory.objections) :
    (original inventory record).history.state.current.history <+:
      (finalOriginal inventory record member).state.history :=
  follow_retains_the_complete_original_history (Dispatch.native (after inventory))
    ((row inventory record member).submit (word inventory))

def censusRow (resident : Mandate.Challenge.Cross.Resident epoch.bound (after inventory).inputs)
    (member : resident ∈ (after inventory).objections) :=
  (⟨Row.currentChallenge resident member,rfl⟩ :
    Located (Row.currentChallenge (packet := ⟨epoch,after inventory⟩) resident member).origin ⟨epoch,after inventory⟩)

def finalCensus (resident : Mandate.Challenge.Cross.Resident epoch.bound (after inventory).inputs)
    (member : resident ∈ (after inventory).objections) :=
  follow (Dispatch.native (after inventory)) (censusRow inventory resident member)

def completeCensus (resident : Mandate.Challenge.Cross.Resident epoch.bound (after inventory).inputs)
    (member : resident ∈ (after inventory).objections) := (finalCensus inventory resident member).complete

theorem the_entire_actual_census_history_is_consumed
    (resident : Mandate.Challenge.Cross.Resident epoch.bound (after inventory).inputs)
    (member : resident ∈ (after inventory).objections) :
    resident.history.state.current.history <+: (finalCensus inventory resident member).state.history :=
  follow_retains_the_complete_original_history (Dispatch.native (after inventory)) (censusRow inventory resident member)

theorem every_shared_grant_release_is_in_the_original_final_root_history
    (record : Grant.Record inventory) (member : record ∈ inventory.grants)
    (receipt : record.ReleaseReceipt epoch.bound (word inventory)) :
    Grant.actualEvent inventory record receipt ∈ (originalRow inventory (.currentGrant record member)).state.history ∧
    (Grant.actualEvent inventory record receipt).kind = .bearerRelease := by
  have recorded := Grant.every_receipt_is_recorded_in_the_original_actual_advance inventory record receipt
  let original : Input.Event.Future.Expiry.Progress.Responsibility.Row ⟨epoch,inventory⟩ := .currentGrant record member
  let position : Located original.origin ⟨epoch,inventory⟩ := ⟨original,rfl⟩
  have retained : (record.advance epoch.bound (word inventory)).history.state.history <+:
      (originalRow inventory (.currentGrant record member)).state.history :=
    follow_retains_the_complete_original_history (Dispatch.native (after inventory)) (position.submit (word inventory))
  obtain ⟨tail,same⟩ := retained
  refine ⟨?_,recorded.2.1⟩
  rw [← same]
  exact List.mem_append_left _ recorded.1

def finance (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :=
  Input.Event.Future.Expiry.Progress.Response.financialSlotAlong (native inventory) index slot present

def rootActual := OutstandingSource.History.actualExecution epoch.source (answer inventory).finalInputs (inventory.inputs.length+1)

theorem shared_word_is_in_the_whole_root_source :
    inventory.inputs ++ [word inventory] <+: (answer inventory).finalInputs := by
  have saved : inventory.inputs ++ [word inventory] = (after inventory).inputs := rfl
  rw [saved]
  exact (List.prefix_append _ [Dispatch.word (after inventory)]).trans
    (Dispatch.dispatch_word_is_in_the_whole_root_source (after inventory))

theorem the_original_root_actually_executes_the_shared_disposition :
    (rootActual inventory).submitted = word inventory ∧
    (rootActual inventory).before = current epoch inventory.inputs := by
  obtain ⟨tail,same⟩ := shared_word_is_in_the_whole_root_source inventory
  unfold rootActual
  rw [← same]
  constructor
  · rw [OutstandingSource.History.scheduled_input_is_actual epoch.source _ inventory.inputs.length (by simp)]
    simp
  · change OutstandingSource.History.currentAt epoch.source ((inventory.inputs ++ [word inventory]) ++ tail) (inventory.inputs.length+2) = _
    rw [(OutstandingSource.History.actual_frame _ _ _).1,List.append_assoc,
      OutstandingSource.History.extending_inputs_preserves_its_executed_prefix epoch.source inventory.inputs
        ([word inventory] ++ tail) _ (Nat.le_refl _)]
    exact (OutstandingSource.History.actual_frame epoch.source inventory.inputs _).1.symm

theorem every_initial_native_row_retains_its_origin_and_complete_history (original : Input.Event.Future.Expiry.Progress.Responsibility.Row ⟨epoch,inventory⟩) :
    (originalRow inventory original).row.origin = original.origin ∧
      original.state.history <+: (originalRow inventory original).state.history :=
  every_actual_step_retains_its_original_admission_and_history (native inventory) original

theorem every_initial_financial_slot_is_consumed_on_the_same_actual_path
    (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :
    Financial.Family.Migration.identity sources (finance inventory index slot present).slot =
      Financial.Family.Migration.identity sources slot ∧
    (finance inventory index slot present).path.records sources index =
      (Input.Event.Future.Expiry.Progress.Response.financeAlong (native inventory)).events.filter (fun event => event.slot == index) :=
  Input.Event.Future.Expiry.Progress.Response.every_actual_path_preserves_each_original_financial_address
    (native inventory) index slot present

theorem shared_disposition_all_rows_finance_ledger_and_next_share_the_actual_root :
    (rootActual inventory).submitted = word inventory ∧
    (rootActual inventory).before = current epoch inventory.inputs ∧
    (∀ row : Input.Event.Future.Expiry.Progress.Responsibility.Row ⟨epoch,inventory⟩, (originalRow inventory row).row.origin = row.origin ∧
      row.state.history <+: (originalRow inventory row).state.history) ∧
    (∀ (record : Record inventory) (member : record ∈ inventory.objections),
      (original inventory record).history.state.current.history <+: (finalOriginal inventory record member).state.history) ∧
    Nonempty (Newborn.CensusReceipt inventory) ∧
    (∀ (resident : Mandate.Challenge.Cross.Resident epoch.bound (after inventory).inputs)
      (member : resident ∈ (after inventory).objections),
      resident.history.state.current.history <+: (finalCensus inventory resident member).state.history) ∧
    (∀ (record : Grant.Record inventory) (member : record ∈ inventory.grants),
      Nonempty (Grant.Disposition inventory record) ∧
      (∀ receipt : record.ReleaseReceipt epoch.bound (word inventory),
        Grant.actualEvent inventory record receipt ∈ (originalRow inventory (.currentGrant record member)).state.history ∧
        (Grant.actualEvent inventory record receipt).kind = .bearerRelease)) ∧
    (∀ (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
      (present : inventory.finance.current.slots[index]? = some slot),
      Financial.Family.Migration.identity sources (finance inventory index slot present).slot =
        Financial.Family.Migration.identity sources slot ∧
      (finance inventory index slot present).path.records sources index =
        (Input.Event.Future.Expiry.Progress.Response.financeAlong (native inventory)).events.filter (fun event => event.slot == index)) ∧
    Financial.Family.ledgerClaims sources (answer inventory).packet.2.finance.current =
      (current (answer inventory).packet.1 (answer inventory).packet.2.inputs).claims ∧
    HEq (Input.Event.Future.Expiry.Progress.Runtime.activated (Dispatch.after (after inventory)) (Input.Event.Future.Expiry.Progress.Runtime.ordinal (Dispatch.after (after inventory)))).tick.generated.wholeLedgerWriteBack
      ((Input.Event.Future.Expiry.Progress.Runtime.activated (Dispatch.after (after inventory)) (Input.Event.Future.Expiry.Progress.Runtime.ordinal (Dispatch.after (after inventory)))).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Input.Event.Future.Expiry.Progress.Runtime.activated (Dispatch.after (after inventory)) (Input.Event.Future.Expiry.Progress.Runtime.ordinal (Dispatch.after (after inventory)))).current.visit.current) ∧
    (Input.Event.Future.Expiry.Progress.Runtime.activated (Dispatch.after (after inventory)) (Input.Event.Future.Expiry.Progress.Runtime.ordinal (Dispatch.after (after inventory)))).tick.nextCurrent =
      (Input.Event.Future.Expiry.Progress.Runtime.facade (Dispatch.after (after inventory))).process.stateAt
        ((Input.Event.Future.Expiry.Progress.Runtime.facade (Dispatch.after (after inventory))).process.successor
          (Input.Event.Future.Expiry.Progress.Runtime.activated (Dispatch.after (after inventory)) (Input.Event.Future.Expiry.Progress.Runtime.ordinal (Dispatch.after (after inventory)))).state) := by
  have root := Dispatch.the_same_actual_root_consumes_dispatch_original_rows_and_next (after inventory)
  exact ⟨(the_original_root_actually_executes_the_shared_disposition inventory).1,
    (the_original_root_actually_executes_the_shared_disposition inventory).2,
    every_initial_native_row_retains_its_origin_and_complete_history inventory,
    the_entire_shared_native_disposition_is_consumed inventory,⟨Newborn.receipt inventory⟩,
    the_entire_actual_census_history_is_consumed inventory,
    (fun record member => ⟨⟨Grant.receive inventory record⟩,
      every_shared_grant_release_is_in_the_original_final_root_history inventory record member⟩),
    every_initial_financial_slot_is_consumed_on_the_same_actual_path inventory,(answer inventory).packet.2.matrix,
    root.2.2.2.1,root.2.2.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Runtime
