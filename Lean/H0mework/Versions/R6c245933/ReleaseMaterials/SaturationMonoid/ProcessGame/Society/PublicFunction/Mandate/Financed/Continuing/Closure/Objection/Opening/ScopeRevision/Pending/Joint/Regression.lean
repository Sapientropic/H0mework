import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.ServiceRegression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
noncomputable section

def exhausted := initial ready Pending.Regression.exhausted

theorem repeated_material_failure_consumes_the_saved_old_native_state :
    kinds (run ready exhausted 2) = [[.admitted, .deferred, .deferred, .deferred]] ∧
    (run ready exhausted 2).objections.length = 1 ∧ terminalFlags (run ready exhausted 2) = [false, false, false, false] := by decide +kernel

def signedInput := [challenge ready]
def withNewborn := alternate ready exhausted [signedInput]
def bothRefused := advance ready withNewborn

theorem a_real_interleaved_signature_adds_its_own_admission_and_both_requests_continue :
    kinds withNewborn = [[.admitted, .deferred, .deferred, .progressed], [.admitted]] ∧
    kinds bothRefused = [[.admitted, .deferred, .deferred, .progressed, .deferred], [.admitted, .deferred]] ∧
    bothRefused.objections.map (fun resident => resident.originInputs.length) = [1, 3] := by decide +kernel

def staged := initial ready Pending.Regression.staged
def shifted := submit ready staged [ChallengeRegression.maintain]

theorem a_real_snapshot_change_is_reconfirmed_from_the_saved_original_request :
    kinds shifted = [[.admitted, .deferred]] ∧
    kinds (advance ready shifted) = [[.admitted, .deferred, .progressed, .obligationTerminal], [.admitted, .obligationTerminal]] ∧
    (advance ready shifted).objections.map (fun resident => resident.originInputs.length) = [1, 3] := by decide +kernel

def quietWord := ChallengeRegression.prelude ++ [request ready.scope ChallengeRegression.beforeBurn true .revoke]
def quiet := submit ready initialInventory quietWord

def readmissionWord :=
  let before := current ready quiet.inputs
  let pair := signedPair ready before
  let after := ((epochLaw ready).execute before 0 pair).final
  pair ++ [challenge ready, request ready.scope after true .revoke]
def readmitted := submit ready quiet readmissionWord

theorem later_actual_double_signing_creates_a_new_grant_and_keeps_the_original :
    quiet.grants.length = 1 ∧ readmitted.grants.length = 2 ∧
    kinds readmitted = [[.admitted, .obligationTerminal], [.admitted, .obligationTerminal]] ∧
    readmitted.grants.map (fun record => record.birth.val) = [1, 2] := by decide +kernel

abbrev publicScopeJointFacade := ScopeJointRuntime.facade ready shifted
abbrev publicScopeJointExhaustedFacade := ScopeJointRuntime.facade ready withNewborn
abbrev publicScopeJointPaidFacade := ScopeJointRuntime.facade ready served
abbrev publicScopeJointReadmittedFacade := ScopeJointRuntime.facade ready readmitted

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Regression
