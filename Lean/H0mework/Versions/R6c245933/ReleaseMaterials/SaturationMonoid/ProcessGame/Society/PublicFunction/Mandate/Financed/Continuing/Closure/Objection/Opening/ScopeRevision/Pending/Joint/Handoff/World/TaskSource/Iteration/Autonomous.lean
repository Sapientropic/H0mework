import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Ancestry

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Current.Autonomous
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local.Inquiry.Planning
open Input.Challenge.Redress.Shared
noncomputable section

/-- The next input is emitted by this actual saved source, after all prior effects. -/
def word (state : Current) : List Action := Input.Event.Future.ownWord state.ready.2

def tick (state : Current) : Incoming.Round state (word state) :=
  Incoming.advance state (word state)

/-- A finite observation of the original receiver/planner; a typed block does
not remove the next source-emitted round. -/
inductive Walk : Current → Nat → Type where
  | private observed (state : Current) : Walk state 0
  | private advanced {state : Current} {count : Nat}
      (made : Incoming.Round state (word state)) (generated : made = tick state)
      (later : Walk made.target count) : Walk state (count+1)

def execute (state : Current) : (count : Nat) → Walk state count
  | 0 => .observed state
  | count+1 =>
      let made := tick state
      .advanced made rfl (execute made.target count)

namespace Walk

def finish : {state : Current} → {count : Nat} → Walk state count → Current
  | _,_,.observed state => state
  | _,_,.advanced _ _ later => later.finish

def inputs : {state : Current} → {count : Nat} → Walk state count → List (List Action)
  | _,_,.observed _ => []
  | state,_,.advanced _ _ later => word state :: later.inputs

/-- This is the existing full-task input Run, with the same cached rounds. -/
def received : {state : Current} → {count : Nat} → (walk : Walk state count) → Incoming.Run state walk.inputs
  | _,_,.observed state => .observed state
  | _,_,.advanced made generated later => .entered made (by rw [generated];rfl) later.received

theorem exact_finish {state : Current} {count : Nat} (walk : Walk state count) :
    walk.received.finish = walk.finish := by
  induction walk
  next state => rfl
  next state count made generated later ih => exact ih

def native {state : Current} {count : Nat} (walk : Walk state count) :
    Input.Event.Evolution state.cursor.saved walk.finish.cursor.saved :=
  walk.exact_finish ▸ walk.received.native

theorem every_observed_round_is_received {state : Current} {count : Nat} (walk : Walk state count) :
    walk.inputs.length = count := by
  induction walk
  next state => rfl
  next state count made generated later ih => exact congrArg Nat.succ ih

theorem complete_task_directory_is_retained {state : Current} {count : Nat} (walk : Walk state count) :
    state.task.futureRequests <+: walk.finish.task.futureRequests := by
  have kept := walk.received.keeps_the_complete_old_directory
  exact walk.exact_finish ▸ kept

theorem every_received_basis_is_retained {state : Current} {count : Nat} (walk : Walk state count) :
    KeepsAncestry state walk.finish :=
  walk.exact_finish ▸ walk.received.keeps_every_earlier_received_basis

def finance {state : Current} {count : Nat} (walk : Walk state count) :=
  Input.Event.Future.Expiry.Progress.Response.financeAlong walk.native

theorem funding {state : Current} {count : Nat} (walk : Walk state count) :
    Input.Event.Funding.Receipt walk.native := Input.Event.Funding.receive walk.native

theorem every_original_responsibility_retains_its_actual_history
    {state : Current} {count : Nat} (walk : Walk state count)
    (row : Input.Event.Future.Expiry.Progress.Responsibility.Row state.cursor.saved) :
    (Input.Event.Future.Expiry.Progress.Responsibility.transport walk.native row).row.origin = row.origin ∧
    row.state.history <+: (Input.Event.Future.Expiry.Progress.Responsibility.transport walk.native row).state.history ∧
    Nonempty ((Input.Event.Future.Expiry.Progress.Responsibility.transport walk.native row).native.Run row.origin.initial
      (Input.Event.Future.Expiry.Progress.Responsibility.transport walk.native row).state) :=
  ⟨(Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history walk.native row).1,
    (Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history walk.native row).2,
    ⟨Input.Event.Future.Expiry.Progress.Responsibility.completeOriginal walk.native row⟩⟩

/-- Observation never supplies termination or authority; the next receiver is
still the original one at this exact generated Current. -/
def next {state : Current} {count : Nat} (walk : Walk state count) := tick walk.finish

end Walk

theorem tick_receives_the_actual_own_word (state : Current) :
    (tick state).received.response = Iteration.Requests.produce
      ⟨state.ready,state.cursor.pending⟩ (Input.Event.Future.ownWord state.ready.2) :=
  (tick state).received.uses_the_actual_receiver

theorem tick_calls_the_original_planner (state : Current) :
    (tick state).step.original = GlobalPolicy.produce (tick state).received.target.task :=
  (tick state).uses_the_original_planner_at_the_actual_received_task

theorem a_typed_planner_block_keeps_the_next_source_receiver
    {state : Current} {incoming : List Action} (made : Incoming.Round state incoming)
    (_blocked : made.step.blocked = true) :
    (tick made.target).received.response = Iteration.Requests.produce
      ⟨made.target.ready,made.target.cursor.pending⟩ (Input.Event.Future.ownWord made.target.ready.2) :=
  tick_receives_the_actual_own_word _

private theorem response_has_no_final_authority
    {cursor : Iteration.Requests.Cursor} {incoming : List Action}
    (made : Iteration.Requests.Result cursor incoming)
    (active : Input.Event.Future.Expiry.Progress.Responsibility.settled made.report.packet = false)
    (actor : Bool) {later : Packet} (path : Input.Event.Evolution made.next.saved later) :
    ¬ Sovereignty.EffectiveJurisdiction (epoch := made.report.packet.1)
      actor (World.current later.1 later.2.inputs) := by
  have same : made.next.saved = Input.Challenge.Redress.Shared.Iteration.next made.report.packet :=
    congrArg (Input.Challenge.Redress.Shared.Iteration.Step.packet made.report.packet.2) made.disposition_exact
  exact Sovereignty.no_final_authority _ active actor (same ▸ path)

theorem no_original_jurisdiction_returns_in_any_actual_future
    (state : Current)
    (active : Input.Event.Future.Expiry.Progress.Responsibility.settled
      (tick state).received.response.report.packet = false)
    (actor : Bool) {later : Packet}
    (path : Input.Event.Evolution (tick state).received.response.next.saved later) :
    ¬ Sovereignty.EffectiveJurisdiction (epoch := (tick state).received.response.report.packet.1)
      actor (World.current later.1 later.2.inputs) :=
  response_has_no_final_authority (tick state).received.response active actor path

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Current.Autonomous
