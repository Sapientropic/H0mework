import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch}

private theorem actual_handoff_is_after_original_deadline (saved : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound saved.inputs) :
    epoch.scope.task.deadline < (World.current (Epoch.ofFresh fresh) (World.handoff saved fresh).inputs).clock :=
  fresh.actual_successor_is_after_the_expired_scope.trans_le
    (World.clock_after_initial (Handoff.source fresh) (World.handoff saved fresh).inputs _)

/-- Fresh service and an actual expired blocker both exhaust the original jurisdiction. -/
theorem Progress.Trace.original_scope_has_actually_expired {inventory : Inventory epoch} (trace : Progress.Trace inventory) :
    epoch.scope.task.deadline < (World.current trace.packet.1 trace.packet.2.inputs).clock := by
  simp only [Progress.Trace.packet]
  generalize trace.ending = final
  rcases final with ⟨saved,answer,verdict⟩
  cases verdict with
  | expired next same kind late =>
    change epoch.scope.task.deadline < (World.current answer.packet.1 answer.packet.2.inputs).clock
    rw [same]
    exact horizon_expires epoch.bound next.inputs _ late
  | crossed kind deadline =>
    cases answer.openness
    next next paid packet facts =>
      change epoch.scope.task.deadline <
        (World.current answer.event.original.original.decision.packet.1 answer.event.original.original.decision.packet.2.inputs).clock
      rw [packet]
      exact actual_handoff_is_after_original_deadline _ next.fresh
    next blocked absent reason packet => exact False.elim (kind blocked)
    next blocked fresh chosen absent actual methods packet =>
      change epoch.scope.task.deadline <
        (World.current answer.event.original.original.decision.packet.1 answer.event.original.original.decision.packet.2.inputs).clock
      rw [packet]
      exact actual_handoff_is_after_original_deadline _ fresh

namespace Jurisdiction
variable (scope : World.Scope)

private theorem step_clock (current : Current) (action : Action) :
    ((Mandate.law base scope).step current action).clock = current.clock := by
  unfold RawLaw.step
  split <;> rfl

private theorem item_clock (current : Current) (index : Nat) (word : List Action)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (member : item ∈ ((Mandate.law base scope).execute current index word).items) : item.before.clock = current.clock := by
  induction word generalizing current index with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons action tail ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same; rfl
    · exact (ih _ _ later).trans (step_clock scope _ _)

theorem expired_task_use_is_refused (current : Current) (expired : scope.task.deadline < current.clock)
    (word : List Action) (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (member : item ∈ (Mandate.law base scope).rawItems current word)
    (bearer : Bool) (goods : Bundle Good) (purpose : Use)
    (operation : item.request.operation = .use bearer goods purpose) (taskUse : Mandate.TaskUse scope item.request) :
    ¬ (Mandate.law base scope).Valid item.before item.request := by
  intro accepted
  have window := (Mandate.protected_use_requires_current_holder base scope _ _ bearer goods purpose operation taskUse accepted).2.2
  rw [item_clock scope current 0 word item member] at window
  exact (not_lt_of_ge window) expired

theorem expired_scope_cannot_generate_acceptance_renewal_or_proposal
    (current : Current) (expired : scope.task.deadline < current.clock) (word : List Action)
    (event : Mandate.ActualCommand base scope current word) :
    event.command ≠ .accept ∧ event.command ≠ .renew ∧ ∀ candidate, event.command ≠ .propose candidate := by
  have clock := item_clock scope current 0 word event.item.val event.item.property
  have permitted := event.authorization.2.2.2.2.2
  constructor
  · intro same
    rw [same] at permitted
    exact (not_lt_of_ge (clock ▸ permitted.2)) expired
  constructor
  · intro same
    rw [same] at permitted
    exact (not_lt_of_ge (clock ▸ permitted.2.2)) expired
  · intro candidate same
    rw [same] at permitted
    exact (not_lt_of_ge (clock ▸ permitted.2)) expired

end Jurisdiction
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry
