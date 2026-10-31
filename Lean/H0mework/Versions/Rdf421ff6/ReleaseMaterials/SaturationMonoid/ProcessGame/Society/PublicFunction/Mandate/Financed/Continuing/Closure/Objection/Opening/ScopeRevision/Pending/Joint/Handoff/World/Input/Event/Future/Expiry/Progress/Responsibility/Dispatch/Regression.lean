import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

theorem exhausted_capture_emits_a_real_exit_refusal_and_repair :
    needsResponse World.Regression.captured = true ∧
    intent World.Regression.captured = .exit ∧
    (Input.choose World.Regression.capturedEpoch .exit
      (current World.Regression.capturedEpoch World.Regression.captured.inputs)).isNone = true ∧
    (word World.Regression.captured).length = 3 ∧
    (Input.demands World.Regression.capturedEpoch .exit
      (current World.Regression.capturedEpoch World.Regression.captured.inputs)).length = 1 := by decide +kernel

theorem quiet_liabilities_pay_an_actual_public_review :
    needsResponse World.Regression.paid = true ∧
    intent World.Regression.paid = .revision ∧
    (Input.choose (Epoch.ofFresh World.Regression.firstFresh) .revision
      (current (Epoch.ofFresh World.Regression.firstFresh) World.Regression.paid.inputs)).isSome = true := by decide +kernel

def overrideWord : List Action := [Input.signature (Epoch.ofFresh World.Regression.firstFresh) true]
def overridden := World.submit World.Regression.paid overrideWord

theorem a_real_override_keeps_the_original_liability_trigger :
    overridden.inputs = World.Regression.paid.inputs ++ [overrideWord] ∧
    needsResponse overridden = true := by
  constructor
  · rfl
  · decide +kernel

theorem every_real_old_grant_causes_redress_after_arbitrary_actual_inputs (history : List (List Action)) :
    ∃ (entry : GrantCohort) (_member : entry ∈ (Event.run
      ⟨Epoch.ofFresh World.Regression.secondFresh,World.Regression.second⟩ history).2.pastGrants),
      needsResponse (Event.run ⟨Epoch.ofFresh World.Regression.secondFresh,World.Regression.second⟩ history).2 = true := by
  obtain ⟨entry,member⟩ := Responsibility.Regression.the_actual_second_scope_has_a_retained_original_grant
  let moved := (Event.runEvolution ⟨Epoch.ofFresh World.Regression.secondFresh,World.Regression.second⟩ history).grant entry member
  refine ⟨moved.row,moved.member,?_⟩
  have pending := a_past_grant_remains_live_after_actual_authority_withdrawal moved.row moved.member
  simp only [needsResponse,pending,Bool.not_false]

abbrev publicResidualDispatchCapturedFacade := Progress.Runtime.facade (after World.Regression.captured)
abbrev publicResidualDispatchQuietFacade := Progress.Runtime.facade (after World.Regression.paid)
abbrev publicResidualDispatchOverrideFacade := Progress.Runtime.facade (after overridden)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Regression
