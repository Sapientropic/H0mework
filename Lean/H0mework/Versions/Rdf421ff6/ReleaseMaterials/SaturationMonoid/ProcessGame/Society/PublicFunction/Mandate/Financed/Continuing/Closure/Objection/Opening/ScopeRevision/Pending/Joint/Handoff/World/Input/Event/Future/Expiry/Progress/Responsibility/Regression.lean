import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Regression
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

theorem the_actual_second_scope_has_a_retained_original_grant :
    ∃ entry : GrantCohort, entry ∈ World.Regression.second.pastGrants := by
  cases same : World.Regression.second.pastGrants with
  | nil =>
    have length := World.Regression.actual_second_scope_keeps_old_arrears_paid_archives_and_new_born_responsibilities.1
    rw [same] at length
    cases length
  | cons entry tail => exact ⟨entry,List.mem_cons_self⟩

theorem actual_service_and_challenge_archives_do_not_forge_full_settlement :
    settled ⟨Epoch.ofFresh World.Regression.secondFresh,World.Regression.second⟩ = false := by
  obtain ⟨entry,member⟩ := the_actual_second_scope_has_a_retained_original_grant
  exact a_past_grant_remains_live_after_actual_authority_withdrawal entry member

theorem the_same_original_grant_survives_arbitrary_actual_overrides (history : List (List Action)) :
    fromRoot (Event.run ⟨Epoch.ofFresh World.Regression.secondFresh,World.Regression.second⟩ history).2 = false := by
  obtain ⟨entry,member⟩ := the_actual_second_scope_has_a_retained_original_grant
  exact arbitrary_actual_events_do_not_erase_the_original_grant World.Regression.second entry member history

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Regression
