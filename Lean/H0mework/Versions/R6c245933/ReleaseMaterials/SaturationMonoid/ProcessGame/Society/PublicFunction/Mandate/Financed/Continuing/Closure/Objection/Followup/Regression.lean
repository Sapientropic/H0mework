import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

noncomputable section

def changedPrefix : List Action := [Objection.Regression.fundTwo, Objection.Regression.review]
def changed := afterInput Objection.Regression.challenged changedPrefix
def original := Response.Regression.firstPending changed (by decide +kernel)
def renewed := FollowupRuntime.transfer changed original

def kinds {fuel : ℚ} {inputs : List (List Action)} {claim : Claim fuel inputs} (history : History fuel inputs claim) :=
  history.state.current.history.map LifecycleEvent.kind

def residualVersion {fuel : ℚ} {inputs : List (List Action)} {claim : Claim fuel inputs} : History fuel inputs claim → Option Nat
  | .pending target _ _ => some ((target.claim fuel inputs).snapshot fuel inputs).version
  | .closed .. => none

theorem actual_new_signature_continues_the_original_slot :
    changed.past.frame.raw.technology.holder = some true ∧
    (Response.emit changed) = [submission] ∧
    original.claim.snapshot.version = 2 ∧ changed.past.frame.raw.technology.version = 3 ∧
    kinds renewed.before = [.admitted] ∧ kinds renewed.after = [.admitted, .progressed] ∧
    renewed.after.state.current.slots.length = 1 ∧
    renewed.after.isPending 3 (Response.nextInputs changed) = true ∧ residualVersion renewed.after = some 3 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  have shifted : Response.Regression.isShifted (Response.decideAt changed) = true := by decide +kernel
  cases selected : Response.decideAt changed with
  | ordinary => rw [selected] at shifted; cases shifted
  | current original same => rw [selected] at shifted; cases shifted
  | shifted original different => rw [Response.emit, selected]; rfl

def signedWord : List Action := changedPrefix ++ [submission, request scope changed.past.frame.raw false .revoke]
def signedClaim : Claim 3 (branchInputs Objection.Regression.challenged signedWord) :=
  (claimsAt 3 (branchInputs Objection.Regression.challenged signedWord) 2).get ⟨0, by decide +kernel⟩
def signedHistory := through 3 (branchInputs Objection.Regression.challenged signedWord) signedClaim 4

theorem actual_reconfirmation_then_paid_revoke_settles_the_original_slot :
    (law.rawItems Objection.Regression.challenged.past.frame.raw signedWord).all
      (fun item => decide (law.Valid item.before item.request)) = true ∧
    kinds signedHistory = [.admitted, .progressed, .obligationTerminal] ∧
    signedHistory.state.current.slots.length = 1 ∧
    signedHistory.isPending 3 (branchInputs Objection.Regression.challenged signedWord) = false ∧
    (afterInput Objection.Regression.challenged signedWord).past.frame.raw.technology.holder = none := by decide +kernel

def unsignedClaim := Objection.Regression.changedClaim
def unsignedHistory := through 3 (branchInputs Objection.Regression.challenged Objection.Regression.changedSnapshotWord) unsignedClaim 4

theorem version_change_and_valid_revoke_without_reconfirmation_keep_the_old_duty :
    kinds unsignedHistory = [.admitted] ∧
    unsignedHistory.isPending 3 (branchInputs Objection.Regression.challenged Objection.Regression.changedSnapshotWord) = true ∧
    residualVersion unsignedHistory = some 2 := by decide +kernel

def wrongWord (action : Action) : List Action := changedPrefix ++ [action, request scope changed.past.frame.raw false .revoke]
def wrongClaim (action : Action) : Claim 3 (branchInputs Objection.Regression.challenged (wrongWord action)) :=
  Response.replacement Objection.Regression.challenged (wrongWord action)
    Response.Regression.productivePending.claim Response.Regression.productivePending.inside

def wrongHistory (action : Action) :=
  through 3 (branchInputs Objection.Regression.challenged (wrongWord action)) (wrongClaim action) 4

theorem wrong_signer_or_challenge_shape_cannot_retarget_the_original :
    kinds (wrongHistory {submission with signer := true}) = [.admitted] ∧
    kinds (wrongHistory {submission with gates := []}) = [.admitted] := by decide +kernel

def refusedWord : List Action := changedPrefix ++ [submission, Response.Regression.drain changed.past.frame.raw,
  request scope (law.step changed.past.frame.raw (Response.Regression.drain changed.past.frame.raw)) false .revoke]
def refusedClaim : Claim 3 (branchInputs Objection.Regression.challenged refusedWord) :=
  (claimsAt 3 (branchInputs Objection.Regression.challenged refusedWord) 2).get ⟨0, by decide +kernel⟩
def refusedHistory := through 3 (branchInputs Objection.Regression.challenged refusedWord) refusedClaim 4

theorem refusal_after_retarget_keeps_original_responsibility_live :
    kinds refusedHistory = [.admitted, .progressed, .deferred] ∧
    refusedHistory.isPending 3 (branchInputs Objection.Regression.challenged refusedWord) = true ∧
    residualVersion refusedHistory = some 3 := by decide +kernel

abbrev publicObjectionFollowupFacade := FollowupRuntime.facade changed

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Regression
