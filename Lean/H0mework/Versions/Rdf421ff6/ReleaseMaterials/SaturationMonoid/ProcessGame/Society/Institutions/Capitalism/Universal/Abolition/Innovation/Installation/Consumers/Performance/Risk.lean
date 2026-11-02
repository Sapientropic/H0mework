import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Code
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem the_actual_code_carries_its_own_source_generated_risk_liability
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    executionInputs (observedCode (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
      (Control.Scenario.discovery version)) = performanceInputs version :=
  (congrArg executionInputs (congrArg programme
    (the_original_current_pays_and_learns_its_own_trial_observation version tested).2)).trans
      (the_real_observed_signal_has_the_original_liability_and_finite_performance version tested)

private theorem first_attempt_of_the_submitted_code
    (oldPast : List InputAt) (nature : RequestAt)
    (original : ∀ raw ∈ oldPast, beforePublic raw = true) :
    selected nature (oldPast ++ submittedInputs oldPast nature) =
      ((executionInputs (observedCode oldPast nature))[0]?).getD (.execute Control.Scenario.commonWork) := by
  simpa only [List.append_nil, List.length_nil] using
    the_submitted_programme_selects_its_original_unspent_attempt oldPast nature [] original (by simp)

theorem the_actual_paid_signal_submits_the_native_risk_before_its_work
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (actualPublicVisit (Control.Scenario.discovery version) 8).snapshot = Physical.Prefix.cursor
      (submittedInputs (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        (Control.Scenario.discovery version) ++ [.primitive (riskLiability version)]) := by
  let nature := Control.Scenario.discovery version
  let oldPast := (firstRaw nature).germ.snapshot.past
  have earlier := the_actual_paid_trial_signal_submits_the_same_roots_code version tested
  have source : selected nature ((firstOrigin nature).germ.snapshot.past ++
      (actualPublicVisit nature 7).snapshot.past) = .primitive (riskLiability version) := by
    have projected := congrArg (fun snapshot : CursorAt => selected nature
      ((firstOrigin nature).germ.snapshot.past ++ snapshot.past)) earlier
    have sourcePast := congrArg (fun past : List InputAt => selected nature
      ((firstOrigin nature).germ.snapshot.past ++ past)) (Physical.Prefix.past_readback (submittedInputs oldPast nature))
    have grammar := congrArg (fun inputs : List InputAt => inputs[0]?.getD (.execute Control.Scenario.commonWork))
      (the_actual_code_carries_its_own_source_generated_risk_liability version tested)
    exact projected.trans (sourcePast.trans ((first_attempt_of_the_submitted_code oldPast nature
      (the_original_first_prefix_has_no_unperformed_public_execution nature)).trans grammar))
  have next := the_actual_primitive_visit_has_its_same_next_source_cursor nature (actualAdmission nature)
    (the_first_admission_is_the_actual_source_compiler_choice nature) 7 (riskLiability version) source
  exact next.trans ((congrArg (fun cursor : CursorAt => Physical.next (Physical.receive cursor (.primitive (riskLiability version))))
    earlier).trans (Physical.Prefix.cursor_append _ _).symm)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
