import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Planning

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Current
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Input.Challenge.Redress.Shared.Iteration
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local.Inquiry.Planning
noncomputable section

private theorem after_keeps_requests (state : Current) {cache : Owned.PublicTask.Local.Inquiry.Frame state.task}
    (made : GlobalPolicy.Service state.task cache) :
    state.task.futureRequests <+: (after state made).task.futureRequests := by
  rw [after_keeps_the_generated_requests]
  exact List.prefix_append _ _

private theorem repaired_keeps_requests {state : Current} (made : Refusal.Result state) :
    state.task.futureRequests <+: made.nextCurrent.task.futureRequests := by
  rw [Refusal.Result.current_keeps_the_same_generated_requests,made.rebuilt_exact]
  exact ⟨_,rfl⟩

theorem Step.every_generated_successor_keeps_the_request_directory {state : Current} (step : Step state) :
    state.task.futureRequests <+: step.target.task.futureRequests := by
  cases original : step.original <;> cases repaired : step.recovery
  · simp only [Step.target,Step.transition,original,repaired]
    exact ⟨[],by simp only [List.append_nil];rfl⟩
  · simp only [Step.target,Step.transition,original,repaired]
    exact repaired_keeps_requests _
  · simp only [Step.target,Step.transition,original,repaired]
    exact after_keeps_requests _ _
  · simp only [Step.target,Step.transition,original,repaired]
    exact after_keeps_requests _ _

namespace Incoming

/-- Each new input is actually received before the original planner is called.
A typed endogenous block may receive further external input in the next round. -/
structure Round (state : Current) (word : List Action) where
  private mk ::
  received : Result state word
  received_exact : received = produce state word
  step : Step received.target
  step_exact : step = Current.produce received.target

def advance (state : Current) (word : List Action) : Round state word :=
  let received := produce state word
  ⟨received,rfl,Current.produce received.target,rfl⟩

namespace Round
variable {state : Current} {word : List Action} (made : Round state word)

def target : Current := made.step.target

def native : Input.Event.Evolution state.cursor.saved made.target.cursor.saved :=
  .append made.received.native made.step.native

theorem keeps_all_old_and_the_actual_new_request :
    state.task.futureRequests ++ [word] <+: made.target.task.futureRequests :=
  made.received.every_received_word_is_registered.trans
    made.step.every_generated_successor_keeps_the_request_directory

theorem uses_the_original_planner_at_the_actual_received_task :
    made.step.original = GlobalPolicy.produce made.received.target.task := made.step.generated

end Round

inductive Run : Current → List (List Action) → Type where
  | observed (state : Current) : Run state []
  | entered {state : Current} {word : List Action} {later : List (List Action)}
      (made : Round state word) (generated : made = advance state word)
      (tail : Run made.target later) : Run state (word::later)

def receive (state : Current) : (words : List (List Action)) → Run state words
  | [] => .observed state
  | word::later =>
      let made := advance state word
      .entered made rfl (receive made.target later)

namespace Run

def finish : {state : Current} → {words : List (List Action)} → Run state words → Current
  | _,_,.observed state => state
  | _,_,.entered _ _ tail => tail.finish

def native {state : Current} {words : List (List Action)} (run : Run state words) :
    Input.Event.Evolution state.cursor.saved run.finish.cursor.saved := by
  induction run with
  | observed => exact .same _
  | entered made generated tail ih => exact .append made.native ih

theorem keeps_the_complete_old_directory {state : Current} {words : List (List Action)} (run : Run state words) :
    state.task.futureRequests <+: run.finish.task.futureRequests := by
  induction run with
  | observed => exact ⟨[],by simp only [List.append_nil];rfl⟩
  | entered made generated tail ih =>
      exact (List.prefix_append _ _).trans (made.keeps_all_old_and_the_actual_new_request.trans ih)

theorem every_received_word_remains_in_the_final_task {state : Current} {words : List (List Action)}
    (run : Run state words) (word : List Action) (member : word ∈ words) :
    word ∈ run.finish.task.futureRequests := by
  induction run with
  | observed => exact False.elim (List.not_mem_nil member)
  | @entered state head later made generated tail ih =>
      rcases List.mem_cons.mp member with same | inside
      · subst word
        have kept := made.keeps_all_old_and_the_actual_new_request.trans tail.keeps_the_complete_old_directory
        exact kept.subset (List.mem_append_right _ (List.mem_singleton_self _))
      · exact ih inside

def finance {state : Current} {words : List (List Action)} (run : Run state words) :=
  Input.Event.Future.Expiry.Progress.Response.financeAlong run.native

theorem funding {state : Current} {words : List (List Action)} (run : Run state words) :
    Input.Event.Funding.Receipt run.native := Input.Event.Funding.receive run.native

theorem every_original_responsibility_keeps_its_actual_history
    {state : Current} {words : List (List Action)} (run : Run state words)
    (row : Input.Event.Future.Expiry.Progress.Responsibility.Row state.cursor.saved) :
    (Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).row.origin = row.origin ∧
    row.state.history <+: (Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).state.history ∧
    Nonempty ((Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).native.Run row.origin.initial
      (Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).state) :=
  ⟨(Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history run.native row).1,
    (Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history run.native row).2,
    ⟨Input.Event.Future.Expiry.Progress.Responsibility.completeOriginal run.native row⟩⟩

end Run
end Incoming
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Current
