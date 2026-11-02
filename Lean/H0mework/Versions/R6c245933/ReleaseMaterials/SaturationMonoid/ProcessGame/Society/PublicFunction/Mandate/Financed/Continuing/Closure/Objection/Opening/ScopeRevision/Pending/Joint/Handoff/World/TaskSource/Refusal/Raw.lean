import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Core
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Initial.Failure.Raw

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Refusal
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt Budget.Programme.Debt.Information.Inquiry.Replay
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Initial.Failure
open Input.Challenge.Redress.Shared.Iteration
noncomputable section

variable (state : Iteration.Current)
abbrev Fault := Raw.Fault state.task.model state.task.original state.task.baseline
  state.task.point.point state.task.rival

def source := Raw.source state.task.model state.task.original state.task.baseline
  state.task.point.point state.task.rival

def cursor (count : Nat) : Cursor state.task.model.source.code :=
  let made := source state
  ⟨made.reference,made.reference_generated,made.history,made.original,made.opponent,made.side,
    Future.takeover state.task.point.point.source state.task.point.point.entry state.task.point.point.cut
      (controller state.task.point.point state.task.original state.task.baseline state.task.rival),
    made.feedbackOverrides,state.task.point.point.cut+count,state.task.point.point.ownerStart⟩

def written (count : Nat) := Writeback.append state.ready.2
  (Writeback.words (source state) (depth state.task.point.point) count)
def beforeCursor (fault : Fault state) : Requests.Cursor :=
  ⟨⟨state.ready.1,written state fault.offset.val⟩,state.cursor.pending⟩
def word (fault : Fault state) := (Raw.actual state.task.model state.task.original state.task.baseline
  state.task.point.point state.task.rival fault.offset.val).submitted

theorem initial_current_is_the_same_actual_cut :
    (source state).currentAt (depth state.task.point.point+1) = current state.ready.1 state.ready.2.inputs := by
  have same := Raw.initial_before_is_original state.task.model state.task.original state.task.baseline
    state.task.point.point state.task.rival
  change (source state).currentAt (depth state.task.point.point+0+1) = _ at same
  simpa only [Nat.add_zero] using same.trans state.aligned

theorem written_current_is_source_current (count : Nat) :
    current state.ready.1 (written state count).inputs =
      (source state).currentAt (depth state.task.point.point+count+1) :=
  Writeback.writeback_keeps_the_exact_native_endpoint (source state) state.ready.2
    (depth state.task.point.point) count state.law (initial_current_is_the_same_actual_cut state)

theorem before_refused_word_is_the_original_source_cut (fault : Fault state) :
    current state.ready.1 (written state fault.offset.val).inputs =
      (Raw.actual state.task.model state.task.original state.task.baseline
        state.task.point.point state.task.rival fault.offset.val).before :=
  written_current_is_source_current state fault.offset.val

/-- Earlier complete words are written once. The original failing word then
enters Requests as new input, with every old pending request still before it. -/
structure Result where
  private mk ::
  fault : Fault state
  response : Requests.Result (beforeCursor state fault) (word state fault)
  response_exact : response = Requests.produce (beforeCursor state fault) (word state fault)
  rebuilt : Communication.Rebuilt response.next.saved
  rebuilt_exact : rebuilt = Communication.result response.next.saved response.next.pending state.task
    (cursor state fault.offset.val)

def resume (fault : Fault state) : Result state :=
  let response := Requests.produce (beforeCursor state fault) (word state fault)
  ⟨fault,response,rfl,Communication.result response.next.saved response.next.pending state.task
    (cursor state fault.offset.val),rfl⟩

def produce : Option (Result state) :=
  match Raw.inspect state.task.model state.task.original state.task.baseline state.task.point.point state.task.rival with
  | .legal _ => none
  | .refused fault => some (resume state fault)

namespace Result
variable {state} (made : Result state)

private def rebuiltCurrent : Iteration.Current :=
  Iteration.Current.fromRebuilt state made.response.next.saved made.response.next.pending
    (cursor state made.fault.offset.val) made.rebuilt made.rebuilt_exact

private def readyNative : Input.Event.Evolution state.ready made.rebuilt.target.saved :=
  .append (Writeback.appendNative state.ready.2
    (Writeback.words (source state) (depth state.task.point.point) made.fault.offset.val))
    (.append made.response.native made.rebuilt.native)

def nextOrigin : FutureOrigin made.rebuilt.target.saved :=
  match state.origin with
  | some basis => basis.advance (fun _ => readyNative made)
  | none => (FutureOrigin.receive made.response).advance (fun _ => made.rebuilt.native)

def nextCurrent : Iteration.Current :=
  (rebuiltCurrent made).withOptionalOrigin (some (nextOrigin made))

theorem next_current_has_its_received_basis : made.nextCurrent.origin = some (nextOrigin made) :=
  (rebuiltCurrent made).withOptionalOrigin_has_the_same_basis _

theorem repair_keeps_the_original_received_basis (basis : FutureOrigin state.ready)
    (received : state.origin = some basis) :
    (nextOrigin made).first = basis.first ∧ (nextOrigin made).pending = basis.pending := by
  simp only [nextOrigin,received]
  exact basis.advance_keeps_the_received_basis _

theorem new_basis_is_from_the_same_repair_response (absent : state.origin = none) :
    (nextOrigin made).first = made.response.next.saved ∧
      (nextOrigin made).pending = made.response.report.residual := by
  simp only [nextOrigin,absent]
  exact ⟨rfl,rfl⟩

theorem current_keeps_the_same_generated_requests :
    made.nextCurrent.task.futureRequests = made.rebuilt.task.futureRequests := rfl

theorem current_keeps_the_same_generated_model :
    made.nextCurrent.task.model = made.rebuilt.task.model := rfl

theorem current_keeps_the_same_actual_endpoint : made.nextCurrent.cursor = made.rebuilt.target := rfl

def native : Input.Event.Evolution state.cursor.saved made.rebuilt.target.saved :=
  .append state.opening (.append
    (Writeback.appendNative state.ready.2
      (Writeback.words (source state) (depth state.task.point.point) made.fault.offset.val))
    (.append made.response.native made.rebuilt.native))

/-- The original planner consumes the Task produced at this actual repair endpoint. -/
def nextCall := Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.produce made.nextCurrent.task

theorem old_pending_precedes_the_unmodified_failed_word :
    Requests.submitted (beforeCursor state made.fault) (word state made.fault) =
      state.cursor.pending ++ word state made.fault := rfl

theorem the_original_failed_item_is_received_before_repair
    (empty : state.cursor.pending = []) :
    made.fault.item ∈ (Mandate.law base state.ready.1.scope).rawItems
      (current state.ready.1 (written state made.fault.offset.val).inputs)
      (Requests.submitted (beforeCursor state made.fault) (word state made.fault)) ∧
    ¬ (Mandate.law base state.ready.1.scope).Valid made.fault.item.before made.fault.item.request := by
  have member := made.fault.item_is_original
  have refused := made.fault.refused
  rw [state.law] at member refused
  rw [← before_refused_word_is_the_original_source_cut state made.fault] at member
  simpa only [Requests.submitted,beforeCursor,empty,List.nil_append,word] using And.intro member refused

theorem every_written_word_and_actual_repair_bill_is_retained :
    ∃ suffix,made.response.report.staged.endpoint.saved.inputs =
      state.ready.2.inputs ++ Writeback.words (source state) (depth state.task.point.point) made.fault.offset.val ++
      [state.cursor.pending ++ word state made.fault] ++ suffix := by
  obtain ⟨suffix,kept⟩ := made.response.the_received_word_and_all_actual_repair_bills_are_retained
  refine ⟨suffix,?_⟩
  simpa only [beforeCursor,Requests.submitted,written,Writeback.inputs_are_the_actual_append,List.append_assoc] using kept

def finance := Input.Event.Future.Expiry.Progress.Response.financeAlong made.native
theorem funding : Input.Event.Funding.Receipt made.native := Input.Event.Funding.receive made.native

theorem every_original_position_and_the_complete_baseline_are_carried :
    made.rebuilt.task.domain.length = state.task.domain.length+1 ∧
      made.rebuilt.task.baseline.controls.length = state.task.baseline.controls.length := by
  rw [made.rebuilt_exact]
  change (Communication.task _ _ state.task (cursor state made.fault.offset.val)).domain.length = _ ∧
    (Communication.task _ _ state.task (cursor state made.fault.offset.val)).baseline.controls.length = _
  constructor
  · dsimp only [Communication.task,Communication.domain,Communication.reconstructDomain]
    exact (List.length_map _).trans List.length_cons
  · rw [Communication.complete_original_baseline_is_retained]
    exact List.length_map _

theorem every_original_responsibility_retains_its_actual_history
    (row : Input.Event.Future.Expiry.Progress.Responsibility.Row state.cursor.saved) :
    (Input.Event.Future.Expiry.Progress.Responsibility.transport made.native row).row.origin = row.origin ∧
    row.state.history <+: (Input.Event.Future.Expiry.Progress.Responsibility.transport made.native row).state.history ∧
    Nonempty ((Input.Event.Future.Expiry.Progress.Responsibility.transport made.native row).native.Run row.origin.initial
      (Input.Event.Future.Expiry.Progress.Responsibility.transport made.native row).state) :=
  ⟨(Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history made.native row).1,
    (Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history made.native row).2,
    ⟨Input.Event.Future.Expiry.Progress.Responsibility.completeOriginal made.native row⟩⟩
end Result
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Refusal
