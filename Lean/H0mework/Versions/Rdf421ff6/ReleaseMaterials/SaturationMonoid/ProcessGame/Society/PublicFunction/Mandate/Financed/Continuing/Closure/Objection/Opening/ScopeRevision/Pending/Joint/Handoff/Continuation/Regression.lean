import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.ChallengeRegression

/-! Actual capture, a fresh signed input, a second autonomous iteration,
and paid original service archives exercise the joint saved-state loop. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
abbrev authority := Handoff.Regression.authority
abbrev capturedFresh := Handoff.Challenge.Regression.dryFresh
def captured := Runtime.fromEpoch authority Handoff.Challenge.Regression.dry capturedFresh
def afterCapture := advance captured

theorem actual_capture_emits_a_native_refusal_and_keeps_the_original_challenge :
    (currentAt capturedFresh captured.inputs).technology.holder = some true ∧
    (currentAt capturedFresh captured.inputs).stock true .service = 0 ∧
    (request? captured).isSome = true ∧ (emit captured).length = 1 ∧
    afterCapture.inputs.length = 4 ∧
    afterCapture.oldChallenges.map (fun entry =>
      (entry.2.state.current.history.drop (entry.1.history.state.current.history.length + 2)).map LifecycleEvent.kind) = [[.deferred]] := by
  decide +kernel

def signedInput : List Action := [⟨false,[],capturedFresh.scope.challenge,[capturedFresh.scope.challenge],.present⟩]
def newlySigned := submit captured signedInput

theorem actual_new_signed_challenge_is_added_to_the_same_inventory :
    newlySigned.objections.length = captured.objections.length + 1 ∧
    (actual captured signedInput).submitted = signedInput ∧
    newlySigned.oldChallenges.length = captured.oldChallenges.length := by
  exact ⟨by decide +kernel,(actual_word_and_cut captured signedInput).1,by decide +kernel⟩

theorem a_second_actual_iteration_continues_the_saved_original_state :
    (evolve captured 2).inputs.length = 6 ∧
    (evolve captured 2).oldChallenges.map (fun entry =>
      (entry.2.state.current.history.drop (entry.1.history.state.current.history.length + 2)).map LifecycleEvent.kind) = [[.deferred,.deferred]] := by
  decide +kernel

abbrev archivedFresh := Handoff.Service.Regression.archivedFresh
def archived := Runtime.fromEpoch authority Handoff.Service.Regression.archivedLate archivedFresh

theorem actual_joint_updates_leave_paid_original_service_archives_literal :
    (List.finRange (Pending.B authority).source.seed.task.slots.length).map (fun index =>
      ((advance archived).oldServices index).state.current.history.length -
        (archived.oldServices index).state.current.history.length) = [0,0,0,0] := by decide +kernel

abbrev publicScopeJointCrossCapturedFacade := Runtime.facade captured
abbrev publicScopeJointCrossSecondFacade := Runtime.facade afterCapture
abbrev publicScopeJointCrossArchivedFacade := Runtime.facade archived

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Regression
