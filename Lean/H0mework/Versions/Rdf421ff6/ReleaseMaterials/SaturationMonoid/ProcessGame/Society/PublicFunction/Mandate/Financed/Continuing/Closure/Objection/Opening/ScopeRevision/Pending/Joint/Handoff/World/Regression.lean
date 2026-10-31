import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Witness

/-! Real second-scope arrears/archives, exhausted capture, and the exact
source-selected cycle use the already checked review witness. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Regression
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
def serviceLive {clock : ℚ} (entry : ServiceCohort clock) : Bool :=
  match entry.saved.state.current.slots with | [.live _] => true | _ => false
def challengeLive {scope : Scope} (entry : ChallengeCohort scope) : Bool :=
  match entry.saved.state.current.slots with | [.live _] => true | _ => false

theorem actual_second_scope_keeps_old_arrears_paid_archives_and_new_born_responsibilities :
    second.pastGrants.length = 1 ∧ second.pastChallenges.length = 1 ∧ second.pastServices.length = 8 ∧
    second.pastServices.map serviceLive = [true,true,true,true,false,false,false,false] ∧
    second.pastChallenges.map challengeLive = [false] := by decide +kernel

theorem exhausted_capture_cannot_forge_a_review_or_a_new_epoch :
    (current capturedEpoch captured.inputs).technology.holder = some true ∧
    (current capturedEpoch captured.inputs).stock true .service = 0 ∧
    (chooseReview captured).isNone = true ∧
    (Handoff.choose capturedEpoch.bound (reviewed captured).inputs).isNone = true ∧
    (next captured).2.inputs.length = 4 ∧ (next captured).2.pastServices.length = 4 := by decide +kernel

theorem the_zero_choice_source_cycle_executes_its_actual_generated_second_epoch :
    next paid = ⟨Epoch.ofFresh secondFresh,second⟩ := by
  change (generate (reviewed paid)).packet _ = _
  apply generated_packet_of_selected
  exact (Option.some_get the_saved_actual_cut_pays_review_and_generates_a_second_scope.2).symm

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Regression
