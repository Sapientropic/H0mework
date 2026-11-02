import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.ChallengeRegression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 18000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

noncomputable section
abbrev ready := ChallengeRegression.ready
abbrev staged := ChallengeRegression.stagedInputs

def historyKinds (inputs : List (List Action)) := (allResidents ready inputs).map fun resident =>
  resident.history.state.current.history.map LifecycleEvent.kind

def originalKinds (inputs : List (List Action)) := (beforeResidents ready inputs).map fun resident =>
  resident.history.state.current.history.map LifecycleEvent.kind

def burnService : Action := ⟨false, [], .resource, [], .use false [(.service, (current ready staged).stock false .service)] .external⟩
def productive := [ChallengeRegression.staged ++ [burnService]]
def burnFeedstock : Action := ⟨false, [], .resource, [], .use false [(.feedstock, (current ready productive).stock false .feedstock)] .external⟩
def exhausted := [ChallengeRegression.staged ++ [burnService, burnFeedstock]]

theorem pending_selects_another_actual_funded_bearer_and_releases_the_holder :
    (current ready staged).technology.holder = some true ∧
    (current ready staged).stock true .service = 0 ∧
    (emit ready staged).length = 1 ∧
    (afterCurrent ready staged).technology.holder = none ∧
    historyKinds staged = [[.admitted, .deferred, .obligationTerminal]] := by decide +kernel

theorem no_cash_generates_actual_production_then_paid_withdrawal :
    (current ready productive).stock true .service = 0 ∧
    (current ready productive).stock false .service = 0 ∧
    (emit ready productive).length = 2 ∧
    (afterCurrent ready productive).technology.holder = none ∧
    historyKinds productive = [[.admitted, .deferred, .obligationTerminal]] := by decide +kernel

theorem exhausted_material_generates_an_actual_refused_attempt_and_keeps_the_original_live :
    (current ready exhausted).stock true .service = 0 ∧
    (current ready exhausted).stock false .service = 0 ∧
    (current ready exhausted).stock true .feedstock = 0 ∧
    (current ready exhausted).stock false .feedstock = 0 ∧
    (emit ready exhausted).length = 3 ∧
    (afterCurrent ready exhausted).technology.holder = some true ∧
    historyKinds exhausted = [[.admitted, .deferred, .deferred]] := by decide +kernel

theorem snapshot_shift_generates_an_actual_original_signature_and_consumes_old_and_new_duties :
    (preamble ready ChallengeRegression.maintainInputs
      ((request? ready ChallengeRegression.maintainInputs).get (by decide +kernel))).length = 1 ∧
    historyKinds ChallengeRegression.maintainInputs =
      [[.admitted, .deferred, .progressed, .obligationTerminal], [.admitted, .obligationTerminal]] ∧
    (afterCurrent ready ChallengeRegression.maintainInputs).technology.holder = none := by decide +kernel

theorem no_actual_signed_objection_does_not_trigger_a_response :
    (request? ready ChallengeRegression.malformedInputs).isNone = true ∧
    emit ready ChallengeRegression.malformedInputs = [] ∧
    (allResidents ready ChallengeRegression.malformedInputs).isEmpty = true := by decide +kernel

theorem completed_actual_archives_are_carried_without_new_admissions :
    emit ready ChallengeRegression.repairInputs = [] ∧
    historyKinds ChallengeRegression.repairInputs = originalKinds ChallengeRegression.repairInputs ∧
    (newbornResidents ready ChallengeRegression.repairInputs).isEmpty = true := by decide +kernel

def quietWord := [request ready.scope (current ready ChallengeRegression.maintainInputs) false .revoke]
def quietStale := ChallengeRegression.maintainInputs ++ [quietWord]

theorem a_quiet_readout_without_same_snapshot_withdrawal_does_not_settle_old_duty :
    (current ready quietStale).technology.holder = none ∧
    originalKinds quietStale = [[.admitted, .deferred]] ∧
    historyKinds quietStale = [[.admitted, .deferred]] ∧
    (request? ready quietStale).isSome = true := by decide +kernel

theorem actual_grant_history_consumes_the_new_word_and_releases_its_bearer :
    (Mandate.Challenge.Cross.grantContinuations (epochBound ready) staged (emit ready staged)).map
      (fun record => record.after.state.history.getLast? |>.map LifecycleEvent.kind) = [some .bearerRelease] := by decide +kernel

abbrev publicScopePendingFacade := ScopePendingRuntime.facade ready staged
abbrev publicScopePendingProductiveFacade := ScopePendingRuntime.facade ready productive
abbrev publicScopePendingExhaustedFacade := ScopePendingRuntime.facade ready exhausted
abbrev publicScopePendingShiftedFacade := ScopePendingRuntime.facade ready ChallengeRegression.maintainInputs

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Regression
