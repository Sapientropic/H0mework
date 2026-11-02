import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.PreRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.Observation

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem the_original_first_prefix_contains_no_submitted_trial_code (nature : RequestAt) :
    ∀ raw ∈ (firstRaw nature).germ.snapshot.past, NonCode raw := by
  rw [the_first_completed_prefix_is_the_original_mandatory_opcode]
  intro raw original
  obtain rfl := List.mem_singleton.mp original
  rcases the_initial_opcode_is_an_advance_or_the_original_primitive with advance | primitive
  · rw [advance]; trivial
  · rw [primitive]; trivial

theorem the_same_actual_trial_root_itself_requests_and_consumes_the_read (version : Nat) :
    (actualPublicVisit (Control.Scenario.discovery version) 6).snapshot =
      Physical.Prefix.cursor (readInputs (Control.Scenario.discovery version)) := by
  let nature := Control.Scenario.discovery version
  have earlier := the_actual_probe_precedes_the_same_root_local_observation nature
  have source : selected nature ((firstOrigin nature).germ.snapshot.past ++
      (actualPublicVisit nature 5).snapshot.past) = .primitive rule.request := by
    have projected := congrArg (fun snapshot : CursorAt => selected nature
      ((firstOrigin nature).germ.snapshot.past ++ snapshot.past)) earlier
    have sourcePast := congrArg (fun past : List InputAt => selected nature
      ((firstOrigin nature).germ.snapshot.past ++ past)) (Physical.Prefix.past_readback (beforeReadInputs nature))
    exact projected.trans (sourcePast.trans (the_discovery_source_actually_requests_its_own_paid_observation _ version
      (the_original_first_prefix_has_no_unperformed_public_execution nature)
      (the_original_first_prefix_contains_no_submitted_trial_code nature)))
  have next := the_actual_primitive_visit_has_its_same_next_source_cursor nature (actualAdmission nature)
    (the_first_admission_is_the_actual_source_compiler_choice nature) 5 rule.request source
  exact next.trans ((congrArg (fun cursor : CursorAt => Physical.next (Physical.receive cursor (.primitive rule.request)))
    earlier).trans (Physical.Prefix.cursor_append _ _).symm)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
