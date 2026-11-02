import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Work

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem the_same_actual_trial_submits_its_first_finite_settlement
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (actualPublicVisit (Control.Scenario.discovery version) 10).snapshot = Physical.Prefix.cursor
      (submittedInputs (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        (Control.Scenario.discovery version) ++
          [.primitive (riskLiability version),.execute Control.Scenario.commonWork,.primitive (firstSettlement version)]) := by
  let nature := Control.Scenario.discovery version
  have earlier := the_original_actual_trial_executes_its_real_all_member_work version tested
  have source := the_actual_performance_cut_selects_only_its_original_unspent_attempt version tested 9
    [.primitive (riskLiability version),.execute Control.Scenario.commonWork]
    (by intro raw member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member;
        rcases member with rfl | rfl <;> trivial) earlier
  have next := the_actual_primitive_visit_has_its_same_next_source_cursor nature (actualAdmission nature)
    (the_first_admission_is_the_actual_source_compiler_choice nature) 9 (firstSettlement version) source
  exact next.trans ((congrArg (fun cursor : CursorAt => Physical.next (Physical.receive cursor (.primitive (firstSettlement version))))
    earlier).trans ((Physical.Prefix.cursor_append _ _).symm.trans
      (congrArg Physical.Prefix.cursor (List.append_assoc _ _ _))))

theorem the_same_actual_trial_completes_its_four_original_performance_attempts
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (actualPublicVisit (Control.Scenario.discovery version) 11).snapshot = Physical.Prefix.cursor
      (submittedInputs (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        (Control.Scenario.discovery version) ++ performanceInputs version) := by
  let nature := Control.Scenario.discovery version
  have earlier := the_same_actual_trial_submits_its_first_finite_settlement version tested
  have source := the_actual_performance_cut_selects_only_its_original_unspent_attempt version tested 10
    [.primitive (riskLiability version),.execute Control.Scenario.commonWork,.primitive (firstSettlement version)]
    (by intro raw member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member;
        rcases member with rfl | rfl | rfl <;> trivial) earlier
  have next := the_actual_primitive_visit_has_its_same_next_source_cursor nature (actualAdmission nature)
    (the_first_admission_is_the_actual_source_compiler_choice nature) 10 (lastSettlement version) source
  exact next.trans ((congrArg (fun cursor : CursorAt => Physical.next (Physical.receive cursor (.primitive (lastSettlement version))))
    earlier).trans ((Physical.Prefix.cursor_append _ _).symm.trans
      (congrArg Physical.Prefix.cursor (List.append_assoc _ _ _))))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
