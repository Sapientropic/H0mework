import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.EpochRuntime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
noncomputable section

def first := Renewal.Regression.first
def ready := (choose first).get (by decide +kernel)

theorem actual_paid_review_and_historical_signature_generate_a_new_scope_member :
    (advance first).cut.past.frame.raw.technology.holder = none ∧
    ready.actor = true ∧ ready.actor ∉ Delegation.members task ∧
    ready.actor ∈ Delegation.members ready.scope.task ∧ participants first = [true, false] ∧
    ready.task.slots.length = 4 ∧ ready.task.earliest = 6 ∧ ready.task.deadline = 7 := by decide +kernel

theorem the_generated_scope_is_used_by_real_commands_and_services :
    (select ready (epochBefore ready)).map Paid.method = some .productive ∧
    (commandsAt base ready.scope (epochExecution ready).before (epochExecution ready).submitted).map (fun event => event.command) =
      [.propose true, .accept, .revoke, .review] ∧
    (∀ item ∈ (epochLaw ready).rawItems (epochExecution ready).before (epochExecution ready).submitted,
      (epochLaw ready).Valid item.before item.request) ∧
    ServiceAdequate (epochLaw ready) (epochExecution ready).before ready.task (epochExecution ready).submitted := by decide +kernel

theorem the_new_member_really_produces_and_pays_all_costs :
    (epochCurrent ready 3).stock true .service = 0 ∧ (epochCurrent ready 3).stock false .service = 1 ∧
    (epochCurrent ready 3).stock false .feedstock = 1 ∧ (epochCurrent ready 3).stock true .feedstock = 0 ∧
    (epochCurrent ready 3).technology.holder = none ∧
    (epochCurrent ready 3).claims () false true = 7 ∧ (epochCurrent ready 3).claims () true false = 0 := by decide +kernel

theorem all_four_new_services_have_real_native_settlement :
    ∀ index, (epochServices ready index).state.TerminalAt 0 :=
  (OutstandingSource.History.NativeService.task_complete_iff_all_native_terminal
    (epochSource ready) (epochInputs ready) 2).mp (by decide +kernel)

theorem new_grant_has_one_real_release_and_keeps_its_original_responsibility :
    (grantRecords ready).length = 1 ∧
    (grantRecords ready).map (fun record => record.history.state.history.map LifecycleEvent.kind) =
      [[.admitted, .bearerRelease, .maintained]] := by decide +kernel

theorem the_entire_old_native_grant_is_retained_at_the_actual_handoff :
    (legacy ready).mandates.length = 1 ∧
    (legacy ready).mandates.map (fun record => record.2.continuation.state.history.map LifecycleEvent.kind) =
      [[.admitted, .bearerRelease, .maintained]] := by decide +kernel

def late := Renewal.Regression.late
def lateReady := (choose late).get (by decide +kernel)
def lateFunded := ((epochLaw lateReady).execute (epochBefore lateReady) 0
  (Method.front lateReady .productive (epochBefore lateReady))).final

theorem expiration_generates_a_fresh_actual_window_without_rewriting_the_old_scope :
    task.deadline < late.cut.past.frame.raw.clock ∧
    lateReady.task.earliest = (advance late).cut.past.frame.raw.clock + 2 ∧
    (select lateReady (epochBefore lateReady)).isSome = true ∧
    ¬ law.Valid lateFunded (request scope lateFunded true (.propose true)) ∧
    (epochLaw lateReady).Valid lateFunded
      (request lateReady.scope lateFunded true (.propose true)) := by decide +kernel

def blocked := Renewal.Regression.blocked

theorem unpaid_actual_old_review_cannot_generate_new_standing :
    choose blocked = none ∧
    ¬ law.Valid (beforeReview blocked) (reviewItem blocked).request ∧
    (advance blocked).cut.past.frame.raw.technology.holder = some true := by decide +kernel

def burn : Action := ⟨false, [], .resource, [], .use false [(.feedstock, 3)] .external⟩
def dry := Joint.submit first [burn]
def dryReady := (choose dry).get (by decide +kernel)

theorem paid_scope_revision_does_not_forge_unfunded_new_service :
    select dryReady (epochBefore dryReady) = none ∧
    (epochCurrent dryReady 3).claims () false true = 7 ∧
    (epochCurrent dryReady 3).technology.holder = none ∧
    (OutstandingSource.History.trailAt (epochSource dryReady) (epochInputs dryReady) 3).frame.payments
      ⟨0, by decide +kernel⟩ = none ∧ (grantRecords dryReady).isEmpty = true := by decide +kernel

theorem unfunded_new_service_keeps_its_native_live_responsibility :
    (epochServices dryReady ⟨0, by decide +kernel⟩).state.LiveAt 0 :=
  (OutstandingSource.History.NativeService.native_live_iff_unpaid
    (epochSource dryReady) (epochInputs dryReady) ⟨0, by decide +kernel⟩ 2).mpr (by decide +kernel)

abbrev publicScopeRevisionFacade := ScopeRevisionRuntime.facade first
abbrev publicScopeEpochFacade := ScopeEpochRuntime.facade ready
abbrev publicScopeLateFacade := ScopeEpochRuntime.facade lateReady
abbrev publicScopeBlockedFacade := ScopeRevisionRuntime.facade blocked
abbrev publicScopeDryFacade := ScopeEpochRuntime.facade dryReady

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Regression
