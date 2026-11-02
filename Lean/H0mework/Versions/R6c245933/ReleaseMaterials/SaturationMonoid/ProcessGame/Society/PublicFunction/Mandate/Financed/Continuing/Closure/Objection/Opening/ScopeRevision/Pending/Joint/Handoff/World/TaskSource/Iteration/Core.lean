import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Service.Actual
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Origin

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Input.Challenge.Redress.Shared.Iteration
open Budget.Programme.Debt Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local Owned.PublicTask.Local.Inquiry Owned.PublicTask.Local.Inquiry.Planning
noncomputable section

abbrev task (state : Requests.Cursor) := TaskSource.task state.saved.2 state.pending

def preparedCursor (state : Requests.Cursor) : Requests.Cursor :=
  ⟨⟨state.saved.1,prepared state.saved.2⟩,state.pending⟩

/-- The original input remains observable before its first call. Its preparation
is consumed only when that call enters; subsequent rounds carry their actual Task. -/
structure Current where
  private mk ::
  cursor : Requests.Cursor
  ready : Packet
  opening : Input.Event.Evolution cursor.saved ready
  task : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit)
  input : task.worldInput.map TaskInput.packet = some ready
  pending : task.worldPending = cursor.pending
  law : task.model.source.code.law = Mandate.law base ready.1.scope
  aligned : task.point.point.source.currentAt (depth task.point.point+1) = current ready.1 ready.2.inputs

namespace Current

def initial (state : Requests.Cursor) : Current :=
  ⟨state,(preparedCursor state).saved,TaskSource.preparation _,Iteration.task state,rfl,rfl,rfl,
    TaskSource.the_original_planning_cut_uses_the_exact_source_current state.saved.2 state.pending⟩

/-- A refusal retains the same Task and source. It consumes only the actual
opening already attached to this current, with no fabricated terminal receipt. -/
def opened (state : Current) : Current :=
  ⟨⟨state.ready,state.cursor.pending⟩,state.ready,.same _,state.task,state.input,state.pending,state.law,state.aligned⟩

def origin (state : Current) : Option (FutureOrigin state.ready) :=
  state.task.originAt state.ready state.input

def withOrigin (state : Current) (basis : FutureOrigin state.ready) : Current :=
  ⟨state.cursor,state.ready,state.opening,state.task.withOriginAt state.ready state.input basis,
    state.task.withOriginAt_packet state.ready state.input basis,state.pending,state.law,state.aligned⟩

def withOptionalOrigin (state : Current) (basis : Option (FutureOrigin state.ready)) : Current :=
  ⟨state.cursor,state.ready,state.opening,state.task.withOptionalOriginAt state.ready state.input basis,
    state.task.withOptionalOriginAt_packet state.ready state.input basis,state.pending,state.law,state.aligned⟩

theorem withOrigin_has_the_same_basis (state : Current) (basis : FutureOrigin state.ready) :
    (state.withOrigin basis).origin = some basis :=
  state.task.withOriginAt_origin state.ready state.input basis

theorem withOptionalOrigin_has_the_same_basis (state : Current) (basis : FutureOrigin state.ready) :
    (state.withOptionalOrigin (some basis)).origin = some basis :=
  state.task.withOriginAt_origin state.ready state.input basis

/-- Consume the cached original reconstruction, without restarting from its
bare packet or recomputing its source. -/
def fromRebuilt (prior : Current) (saved : Packet) (pending : List Action)
    (point : Distributed.Recall.Information.Agency.Protocol.Continuation.Cursor prior.task.model.source.code)
    (made : Communication.Rebuilt saved)
    (generated : made = Communication.result saved pending prior.task point) : Current :=
  ⟨made.target,made.target.saved,.same _,made.task,
    by rw [generated];rfl,by rw [generated];rfl,made.law,made.aligned⟩

namespace Incoming

variable (state : Current) (word : List Action)

def cursor : Requests.Cursor := ⟨state.ready,state.cursor.pending⟩

/-- Registration records untrusted raw input for later opportunity checks. It
changes no source, rule, authority, rate or available payment. -/
private def registered : Current :=
  ⟨state.cursor,state.ready,state.opening,
    {state.task with futureRequests := state.task.futureRequests ++ [word]},
    state.input,state.pending,state.law,state.aligned⟩

/-- The original receiving source executes pending ++ incoming before rebuilding
its own Task. The same incoming word then remains in that Task's directory. -/
structure Result where
  private mk ::
  response : Requests.Result (cursor state) word
  response_exact : response = Requests.produce (cursor state) word
  rebuilt : Communication.Rebuilt response.next.saved
  rebuilt_exact : rebuilt = Communication.result response.next.saved response.next.pending
    (registered state word).task state.task.point.point

def produce : Result state word :=
  let response := Requests.produce (cursor state) word
  ⟨response,rfl,Communication.result response.next.saved response.next.pending
    (registered state word).task state.task.point.point,rfl⟩

namespace Result
variable {state word} (made : Result state word)

private def rebuiltCurrent : Current :=
  Current.fromRebuilt (registered state word) made.response.next.saved made.response.next.pending
    state.task.point.point made.rebuilt made.rebuilt_exact

/-- The basis begins after this same response; the completed incoming word is not replayed. -/
def target : Current :=
  (rebuiltCurrent made).withOrigin
    ((FutureOrigin.receiveAfter state.origin made.response).advance (fun _ => made.rebuilt.native))

def native : Input.Event.Evolution state.cursor.saved made.target.cursor.saved :=
  .append state.opening (.append made.response.native made.rebuilt.native)

theorem uses_the_actual_receiver :
    made.response = Requests.produce ⟨state.ready,state.cursor.pending⟩ word := made.response_exact

theorem origin_is_the_same_post_response :
    made.target.origin = some ((FutureOrigin.receiveAfter state.origin made.response).advance (fun _ => made.rebuilt.native)) :=
  (rebuiltCurrent made).withOrigin_has_the_same_basis _

theorem keeps_the_same_rebuilt_task :
    made.target.task = made.rebuilt.task.withOriginAt made.rebuilt.target.saved
      (by rw [made.rebuilt_exact];rfl)
      ((FutureOrigin.receiveAfter state.origin made.response).advance (fun _ => made.rebuilt.native)) := rfl

theorem keeps_the_same_rebuilt_model : made.target.task.model = made.rebuilt.task.model := rfl

theorem keeps_the_same_rebuilt_requests :
    made.target.task.futureRequests = made.rebuilt.task.futureRequests := rfl

theorem old_residual_precedes_the_new_word :
    Requests.submitted (cursor state) word = state.cursor.pending ++ word := rfl

theorem every_received_word_is_registered :
    state.task.futureRequests ++ [word] <+: made.target.task.futureRequests := by
  change _ <+: made.rebuilt.task.futureRequests
  rw [made.rebuilt_exact]
  exact ⟨_,rfl⟩

theorem reconstruction_does_not_increase_the_declared_payment :
    made.target.task.quote = state.task.quote ∧
    HEq made.target.task.recoveryRate state.task.recoveryRate ∧
    HEq made.target.task.accountingRate state.task.accountingRate := by
  change made.rebuilt.task.quote = _ ∧ HEq made.rebuilt.task.recoveryRate _ ∧ HEq made.rebuilt.task.accountingRate _
  rw [made.rebuilt_exact]
  exact ⟨rfl,HEq.rfl,HEq.rfl⟩

def finance := Input.Event.Future.Expiry.Progress.Response.financeAlong made.native

theorem funding : Input.Event.Funding.Receipt made.native := Input.Event.Funding.receive made.native

end Result
end Incoming

variable (state : Current) {cache : Inquiry.Frame state.task}
  (made : GlobalPolicy.Service state.task cache)

private def afterBase : Current :=
  ⟨Service.Actual.target state.ready.2 state.cursor.pending made,
    (Service.Actual.target state.ready.2 state.cursor.pending made).saved,.same _,
    Service.Actual.task state.ready.2 state.cursor.pending made,rfl,rfl,
    (Service.Actual.rebuilt state.ready.2 state.cursor.pending made).law,
    Service.Actual.target_task_cut_is_the_written_world state.ready.2 state.cursor.pending made⟩

def after : Current :=
  (afterBase state made).withOptionalOrigin
    (state.origin.map fun basis => basis.advance
      (fun _ => Service.Actual.reconstructedNative state.ready.2 state.cursor.pending made))

theorem after_carries_the_same_received_basis (basis : FutureOrigin state.ready)
    (received : state.origin = some basis) :
    (after state made).origin =
      some (basis.advance (fun _ => Service.Actual.reconstructedNative state.ready.2 state.cursor.pending made)) := by
  unfold after
  rw [received]
  exact (afterBase state made).withOptionalOrigin_has_the_same_basis _

def afterNative : Input.Event.Evolution state.cursor.saved (after state made).cursor.saved :=
  .append state.opening (Service.Actual.reconstructedNative state.ready.2 state.cursor.pending made)

theorem every_service_writes_its_own_actual_endpoint :
    current state.ready.1 (Writeback.append state.ready.2
      (Writeback.words made.full.source (depth state.task.point.point) (Service.controls made).length)).inputs =
      made.full.source.currentAt (depth made.full+1) :=
  Service.Actual.raw_writeback_reaches_the_same_service_endpoint state.ready.2 made state.law state.aligned

theorem after_keeps_the_generated_requests :
    (after state made).task.futureRequests = (Communication.task
      (Service.Actual.next state.ready.2 state.cursor.pending made).saved.2
      (Service.Actual.next state.ready.2 state.cursor.pending made).pending state.task made.full).futureRequests := rfl

theorem after_keeps_every_original_position (point : Distributed.Recall.Information.Agency.Protocol.Continuation.Cursor
    state.task.model.source.code) (member : point ∈ state.task.domain) :
    Communication.Source.cursor (Service.Actual.next state.ready.2 state.cursor.pending made).saved.2 point ∈
      (after state made).task.domain :=
  Communication.every_original_position_is_reconstructed _ _ _ _ member


def SelectedActualProtection : Prop :=
  match made with
  | .worldCompleted step _ _ _ _ _ _ _ _ selected =>
      ∀ candidate,selected.candidate? state.task = some candidate →
        Commitment.NoWorse state.task state.ready.2 step.path.finish.past step.path.finish.programme candidate.protocol
  | _ => True

theorem every_selected_actual_successor_is_prechecked : SelectedActualProtection state made := by
  cases made with
  | unavailable => trivial
  | completed => trivial
  | worldShort => trivial
  | worldCompleted step generated permit paid input supplied rate declared covered selected =>
      intro candidate chosen
      have protection := (TaskInput.Work.Actual.protection_at_packet input state.task
        step.path.finish.past step.path.finish.programme candidate).mp (selected.actual_protection state.task candidate chosen)
      have packets : input.packet = state.ready := Option.some.inj (by
        calc
          some input.packet = state.task.worldInput.map TaskInput.packet := by rw [supplied];rfl
          _ = some state.ready := state.input)
      have kept := protection.2
      rw [packets] at kept
      exact kept

theorem every_selected_call_uses_its_prechecked_next :
    Service.Actual.SelectedNextIsChecked state.ready.2 state.cursor.pending made :=
  Service.Actual.selected_next_is_the_prechecked_actual_next state.ready.2 state.cursor.pending made state.pending.symm

end Current
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration
