import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Signal.Current
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.Code

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem the_actual_paid_trial_signal_submits_the_same_roots_code
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (actualPublicVisit (Control.Scenario.discovery version) 7).snapshot = Physical.Prefix.cursor
      (submittedInputs (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past (Control.Scenario.discovery version)) := by
  let nature := Control.Scenario.discovery version
  let oldPast := (firstRaw nature).germ.snapshot.past
  have earlier := the_same_actual_trial_root_itself_requests_and_consumes_the_read version
  have source : selected nature ((firstOrigin nature).germ.snapshot.past ++
      (actualPublicVisit nature 6).snapshot.past) = .code ⟨observedCode oldPast nature⟩ := by
    have projected := congrArg (fun snapshot : CursorAt => selected nature
      ((firstOrigin nature).germ.snapshot.past ++ snapshot.past)) earlier
    have sourcePast := congrArg (fun past : List InputAt => selected nature
      ((firstOrigin nature).germ.snapshot.past ++ past)) (Physical.Prefix.past_readback (readInputs nature))
    exact projected.trans (sourcePast.trans (the_source_paid_read_generates_its_own_submitted_code oldPast version
      (the_original_first_prefix_has_no_unperformed_public_execution nature)
      (the_original_first_prefix_contains_no_submitted_trial_code nature)
      (the_original_current_pays_and_learns_its_own_trial_observation version tested).1))
  have next := the_actual_code_visit_has_its_same_next_source_cursor nature (actualAdmission nature)
    (the_first_admission_is_the_actual_source_compiler_choice nature) 6 (observedCode oldPast nature) source
  exact next.trans ((congrArg (fun cursor : CursorAt => Physical.next (Physical.receive cursor (.code ⟨observedCode oldPast nature⟩)))
    earlier).trans (Physical.Prefix.cursor_append _ _).symm)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
