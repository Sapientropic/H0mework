import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.ChallengeRegression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
noncomputable section

abbrev ready := Regression.ready
abbrev ownBound := epochBound ready

def histories (inputs : List (List Action)) (count : Nat) :=
  (Mandate.Challenge.recordsAt (Mandate.Challenge.fromHistory ownBound) inputs count).map fun record =>
    record.2.state.current.history.map LifecycleEvent.kind

theorem the_new_member_actual_signature_creates_and_settles_its_own_native_request :
    (Mandate.Challenge.claimsAt (Mandate.Challenge.fromHistory ownBound) (epochInputs ready) 2).length = 1 ∧
    (Mandate.Challenge.claimsAt (Mandate.Challenge.fromHistory ownBound) (epochInputs ready) 2).map (fun claim => claim.signer (Mandate.Challenge.fromHistory ownBound) _) = [true] ∧
    histories (epochInputs ready) 3 = [[.admitted, .obligationTerminal]] ∧
    (generateEpoch ready).objections.length = 1 := by decide +kernel

def front := Method.front ready .productive (epochBefore ready)
def pairBefore := ((epochLaw ready).execute (epochBefore ready) 0 front).final
def prelude := front ++ signedPair ready pairBefore ++ [challenge ready]
def beforeBurn := ((epochLaw ready).execute (epochBefore ready) 0 prelude).final

def burn : Action := ⟨true, [], .resource, [], .use true [(.service, beforeBurn.stock true .service)] .external⟩
def beforeWithdrawal := (epochLaw ready).step beforeBurn burn
def staged := prelude ++ [burn, request ready.scope beforeWithdrawal true .revoke]
def stagedInputs := [staged]

abbrev cur (inputs : List (List Action)) (ordinal : Nat) :=
  OutstandingSource.History.currentAt (epochSource ready) inputs ordinal

def maintain := request ready.scope (cur stagedInputs 3) false .review
def maintainInputs := [staged, [maintain]]
def revive := [challenge ready, request ready.scope (cur maintainInputs 4) true .revoke]
def reviveInputs := [staged, [maintain], revive]
def repair := request ready.scope (cur reviveInputs 5) false .review
def repairInputs := [staged, [maintain], revive, [repair]]

theorem refused_withdrawal_and_ordinary_review_keep_the_request_live :
    histories stagedInputs 3 = [[.admitted, .deferred]] ∧
    (cur stagedInputs 3).technology.holder = some true ∧
    (cur stagedInputs 3).stock true .service = 0 ∧
    (epochLaw ready).Valid (cur stagedInputs 3) maintain ∧
    histories maintainInputs 4 = [[.admitted, .deferred]] ∧
    (cur maintainInputs 4).technology.holder = some true := by decide +kernel

theorem the_original_request_retargets_by_real_signature_and_retains_its_admission :
    histories reviveInputs 5 = [[.admitted, .deferred, .progressed, .deferred], [.admitted, .deferred]] ∧
    (cur reviveInputs 5).technology.holder = some true ∧
    (cur reviveInputs 5).claims () false true = 7 := by decide +kernel

theorem expired_review_actually_settles_both_original_and_new_request :
    (epochLaw ready).Valid (cur reviveInputs 5) repair ∧ ready.task.deadline < (cur reviveInputs 5).clock ∧
    histories repairInputs 6 =
      [[.admitted, .deferred, .progressed, .deferred, .obligationTerminal], [.admitted, .deferred, .obligationTerminal]] ∧
    (cur repairInputs 6).technology.holder = none ∧ (cur repairInputs 6).stock false .service = 1 ∧
    (cur repairInputs 6).claims () false true = 7 := by decide +kernel

def original := (Mandate.Challenge.claimsAt (Mandate.Challenge.fromHistory ownBound) repairInputs 2).get ⟨0, by decide +kernel⟩

theorem refused_original_request_is_natively_live_at_its_actual_cut :
    (Mandate.Challenge.through (Mandate.Challenge.fromHistory ownBound) repairInputs original 3).state.current.LiveAt 0 :=
  Mandate.Challenge.History.live_of_pending (Mandate.Challenge.fromHistory ownBound) repairInputs _ (by decide +kernel)

def actualContinuation := Mandate.Challenge.fromActualCut (Mandate.Challenge.fromHistory ownBound) repairInputs original 3 3

theorem continued_native_history_is_the_full_generated_run :
    (Mandate.Challenge.through (Mandate.Challenge.fromHistory ownBound) repairInputs original 6).state.current.history =
      (Mandate.Challenge.through (Mandate.Challenge.fromHistory ownBound) repairInputs original 6).state.generated.events :=
  Mandate.Challenge.actual_native_history (Mandate.Challenge.fromHistory ownBound) repairInputs original 6

def malformedInputs := [front ++ signedPair ready pairBefore ++
  [{challenge ready with gates := []}, {challenge ready with consents := [false]},
    {challenge ready with purpose := .service}]]

theorem matching_present_shapes_do_not_create_a_signed_objection :
    (cur malformedInputs 3).technology.holder = some true ∧
    (Mandate.Challenge.claimsAt (Mandate.Challenge.fromHistory ownBound) malformedInputs 2).isEmpty = true ∧
    ¬ Mandate.Challenge.Withdrawal (scope := ready.scope) (cur maintainInputs 4)
      (request ready.scope beforeWithdrawal true .revoke) ∧
    (Mandate.Challenge.recordsAt (Mandate.Challenge.fromHistory (epochBound Regression.dryReady)) (epochInputs Regression.dryReady) 3).isEmpty = true := by decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.ChallengeRegression
