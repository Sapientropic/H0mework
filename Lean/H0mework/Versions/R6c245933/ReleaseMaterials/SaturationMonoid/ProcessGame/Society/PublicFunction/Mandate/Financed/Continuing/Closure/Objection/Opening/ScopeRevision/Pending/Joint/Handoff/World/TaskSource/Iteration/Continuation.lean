import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Autonomous

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Current
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local Owned.PublicTask.Local.Inquiry Owned.PublicTask.Local.Inquiry.Planning
open Input.Challenge.Redress.Shared
noncomputable section

namespace Continuation

/-- The trajectory is generated one actual own-word round causalAt a time. -/
def causalAt (state : Current) : Nat → Current
  | 0 => state
  | n+1 => causalAt (Autonomous.tick state).target n

theorem exact_observed_prefix (state : Current) (n : Nat) :
    (Autonomous.execute state n).finish = causalAt state n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => exact ih _

theorem successive_prefixes (state : Current) (start count : Nat) :
    causalAt state (start+count) = causalAt (causalAt state start) count := by
  induction start generalizing state with
  | zero => simp only [Nat.zero_add,causalAt]
  | succ start ih => simpa only [Nat.succ_add,causalAt] using ih (Autonomous.tick state).target

theorem next_is_the_generated_next (state : Current) (n : Nat) :
    causalAt state (n+1) = (Autonomous.tick (causalAt state n)).target := by
  rw [successive_prefixes]
  rfl

def segment (state : Current) (start count : Nat) :
    Input.Event.Evolution (causalAt state start).cursor.saved (causalAt state (start+count)).cursor.saved := by
  rw [successive_prefixes state start count,← exact_observed_prefix (causalAt state start) count]
  exact (Autonomous.execute (causalAt state start) count).native

theorem every_later_prefix_keeps_the_complete_directory (state : Current) (start count : Nat) :
    (causalAt state start).task.futureRequests <+: (causalAt state (start+count)).task.futureRequests := by
  rw [successive_prefixes state start count,← exact_observed_prefix (causalAt state start) count]
  exact (Autonomous.execute (causalAt state start) count).complete_task_directory_is_retained

theorem every_later_prefix_keeps_every_received_basis (state : Current) (start count : Nat) :
    KeepsAncestry (causalAt state start) (causalAt state (start+count)) := by
  rw [successive_prefixes state start count,← exact_observed_prefix (causalAt state start) count]
  exact (Autonomous.execute (causalAt state start) count).every_received_basis_is_retained

theorem every_later_prefix_keeps_its_financial_history (state : Current) (start count : Nat) :
    Input.Event.Funding.Receipt (segment state start count) :=
  Input.Event.Funding.receive _

theorem every_later_prefix_keeps_original_responsibility
    (state : Current) (start count : Nat)
    (row : Input.Event.Future.Expiry.Progress.Responsibility.Row (causalAt state start).cursor.saved) :
    (Input.Event.Future.Expiry.Progress.Responsibility.transport (segment state start count) row).row.origin = row.origin ∧
    row.state.history <+:
      (Input.Event.Future.Expiry.Progress.Responsibility.transport (segment state start count) row).state.history ∧
    Nonempty ((Input.Event.Future.Expiry.Progress.Responsibility.transport (segment state start count) row).native.Run
      row.origin.initial
      (Input.Event.Future.Expiry.Progress.Responsibility.transport (segment state start count) row).state) :=
  ⟨(Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history
      (segment state start count) row).1,
    (Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history
      (segment state start count) row).2,
    ⟨Input.Event.Future.Expiry.Progress.Responsibility.completeOriginal (segment state start count) row⟩⟩

/-- A selected candidate protects the actual old queries and all carried future
bases in the same paid selection, causalAt its own checked successor. -/
def WorldProtection (state : Current) {cache : Owned.PublicTask.Local.Inquiry.Frame state.task}
    (made : GlobalPolicy.Service state.task cache) : Prop :=
  match made with
  | .worldCompleted step _ _ _ input _ _ _ _ selected =>
      ∀ candidate,selected.candidate? state.task = some candidate →
        TaskInput.Work.Actual.Protection input state.task step.path.finish.past step.path.finish.programme candidate ∧
        TaskInput.Work.Actual.QueryProtection input state.task selected.batch
          step.path.finish.past step.path.finish.programme candidate ∧
        TaskInput.Work.Actual.FutureProtection input state.task step.path.finish.past step.path.finish.programme candidate
  | _ => True

theorem selected_preserves_all_received_capabilities
    (state : Current) {cache : Owned.PublicTask.Local.Inquiry.Frame state.task}
    (made : GlobalPolicy.Service state.task cache) : WorldProtection state made := by
  cases made with
  | unavailable => trivial
  | completed => trivial
  | worldShort => trivial
  | worldCompleted step generated permit paid input supplied rate declared covered selected =>
      intro candidate chosen
      exact ⟨selected.actual_protection state.task candidate chosen,
        selected.original_query_protection state.task candidate chosen,
        selected.received_future_protection state.task candidate chosen⟩

/-- Every inner service branch exposes its actual payment or selection result;
none of the unselected branches is certified through an empty implication. -/
def ServiceReview (state : Current) {cache : Owned.PublicTask.Local.Inquiry.Frame state.task}
    (made : GlobalPolicy.Service state.task cache) : Prop :=
  match made with
  | .unavailable step _ _ => step.ready = none
  | .completed step _ _ _ outcome _ => match outcome with
      | .selected candidate => Selection.Restoration.acceptable
          (tariff := state.task.recoveryPricing) (requested := state.task.futureRequests)
          state.task.model state.task.domain state.task.original step.path.finish.programme candidate.protocol
      | .blocked _ => ∀ tail,
          Nonempty (Prefix.Global.Failure
            (tariff := state.task.recoveryPricing) (requested := state.task.futureRequests)
            state.task.model state.task.domain state.task.original step.path.finish.programme
            (Prefix.Global.proposal state.task.model state.task.domain step.path.finish.past tail))
  | .worldShort _ _ _ _ input _ rate _ _ =>
      ¬ Accounting.covers state.task (Computation.Search.Charge.fee state.task.quote) state.task.model.source.code.actions[rate]
        (1 + Accounting.selectionUnits state.task + GlobalPolicy.World.units state.task input)
  | .worldCompleted _ _ _ _ _ _ _ _ _ selected => selected.Reviewed state.task

theorem every_inner_service_result_is_reviewed
    (state : Current) {cache : Owned.PublicTask.Local.Inquiry.Frame state.task}
    (made : GlobalPolicy.Service state.task cache) : ServiceReview state made := by
  cases made with
  | unavailable step generated missing => exact missing
  | completed step generated permit paid outcome compiled =>
      cases outcome with
      | selected candidate => exact candidate.fullAccepted
      | blocked rejected => exact fun tail => ⟨rejected tail⟩
  | worldShort step generated permit paid input supplied rate declared missing => exact missing
  | worldCompleted step generated permit paid input supplied rate declared covered selected =>
      exact selected.reviewed state.task

/-- Disposition retains the exact original failure or the actual repair/service.
A refusal never supplies success, authority or a terminal future. -/
inductive Disposition {state : Current} (step : Step state) where
  | blocked
      (row : Selection.Rejection state.task.model state.task.domain state.task.original state.task.baseline state.task.baseline)
      (rejected : step.original = .rejected row) (absent : step.recovery = none)
      (kept : step.target.task = state.task ∧ step.blocked = true)
  | repaired
      (row : Selection.Rejection state.task.model state.task.domain state.task.original state.task.baseline state.task.baseline)
      (rejected : step.original = .rejected row)
      (made : Refusal.Result state) (recovered : step.recovery = some made)
      (actual : step.target = made.nextCurrent ∧ step.blocked = false)
  | service (cache : Owned.PublicTask.Local.Inquiry.Frame state.task)
      (made : GlobalPolicy.Service state.task cache) (generated : step.original = .generated cache made)
      (actual : step.target = after state made ∧ step.blocked = false)
      (protection : WorldProtection state made)
      (reviewed : ServiceReview state made)
      (same_next : Service.Actual.SelectedNextIsChecked state.ready.2 state.cursor.pending made)

def dispose {state : Current} (step : Step state) : Disposition step :=
  match original : step.original with
  | .rejected row => match recovery : step.recovery with
      | none => .blocked row original recovery
          (step.an_unrepaired_refusal_keeps_the_original_task row original recovery)
      | some made => .repaired row original made recovery
          ⟨step.repaired_refusal_uses_its_actual_successor row original made recovery,
           step.an_actual_recovery_does_not_stop_recursion made recovery⟩
  | .generated cache made => .service cache made original
      (step.original_services_keep_their_actual_successor made original)
      (selected_preserves_all_received_capabilities state made)
      (every_inner_service_result_is_reviewed state made)
      (every_selected_call_uses_its_prechecked_next state made)

def inspect (state : Current) (n : Nat) := dispose (Autonomous.tick (causalAt state n)).step

theorem even_a_block_has_the_next_source_receiver (state : Current) (n : Nat)
    (_blocked : (Autonomous.tick (causalAt state n)).step.blocked = true) :
    (Autonomous.tick (causalAt state (n+1))).received.response = Iteration.Requests.produce
      ⟨(causalAt state (n+1)).ready,(causalAt state (n+1)).cursor.pending⟩
      (Input.Event.Future.ownWord (causalAt state (n+1)).ready.2) :=
  Autonomous.tick_receives_the_actual_own_word _

end Continuation
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Current
