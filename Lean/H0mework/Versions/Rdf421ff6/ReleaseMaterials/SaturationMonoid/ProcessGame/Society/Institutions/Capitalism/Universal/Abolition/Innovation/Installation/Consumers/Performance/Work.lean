import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Risk
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Raw
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Step

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Functions.Revision

noncomputable section

theorem the_actual_risk_bearing_trial_retains_its_full_current_work_checks
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    Macro.Public.Scope.Checks input 0 count 0 0 (firstOrigin (Control.Scenario.discovery version)).germ.snapshot.past
      (actualPublicVisit (Control.Scenario.discovery version) 8).snapshot
      (PublicPlan.executable Control.Scenario.commonWork) := by
  let nature := Control.Scenario.discovery version
  let oldPast := (firstRaw nature).germ.snapshot.past
  let frame := actualPublicVisit nature 8
  let members := Macro.Public.Scope.scope input 0 count 0 0 oldPast frame.snapshot
    (PublicPlan.executable Control.Scenario.commonWork)
  have sameSnapshot := the_actual_paid_signal_submits_the_native_risk_before_its_work version tested
  have projected := congrArg (fun cursor : CursorAt =>
    (Physical.Public.stateAt input 0 count 0 0 oldPast cursor.past).raw) sameSnapshot
  have sourcePast := congrArg (fun past : List InputAt =>
    (Physical.Public.stateAt input 0 count 0 0 oldPast past).raw)
      (Physical.Prefix.past_readback (submittedInputs oldPast nature ++ [.primitive (riskLiability version)]))
  have raw := projected.trans (sourcePast.trans
    (the_submitted_code_and_actual_risk_issue_have_the_original_checked_raw oldPast nature (riskLiability version)))
  have checked := the_original_paid_trial_and_native_liability_cover_the_whole_current_scope
    (Physical.stateAt input 0 count 0 0 oldPast).raw
    (the_first_actual_raw_is_in_its_actual_source_inventory nature) version tested
    (riskLiability version) (each_observed_risk_liability_is_one_of_the_original_source_requests version) members
  have atCurrent := Eq.mpr (congrArg (fun current : Raw => Review.Guarded.Checks (Macro.Public.Scope.checkInput input)
    Control.Scenario.seed current members (PublicPlan.executable Control.Scenario.commonWork)) raw) checked
  exact Eq.mpr (congrArg (fun origin : Raw => Review.Guarded.Checks (Macro.Public.Scope.checkInput input)
    origin (Physical.Public.stateAt input 0 count 0 0 oldPast frame.snapshot.past).raw members
      (PublicPlan.executable Control.Scenario.commonWork))
        (show Actual.origin input 0 count = Control.Scenario.seed from
          the_original_physical_seed_is_the_actual_capital_successor)) atCurrent

theorem the_original_actual_trial_executes_its_real_all_member_work
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (actualPublicVisit (Control.Scenario.discovery version) 9).snapshot = Physical.Prefix.cursor
      (submittedInputs (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        (Control.Scenario.discovery version) ++
          [.primitive (riskLiability version),.execute Control.Scenario.commonWork]) := by
  let nature := Control.Scenario.discovery version
  have earlier := the_actual_paid_signal_submits_the_native_risk_before_its_work version tested
  have source := the_actual_performance_cut_selects_only_its_original_unspent_attempt version tested 8
    [.primitive (riskLiability version)] (by intro raw member; obtain rfl := List.mem_singleton.mp member; trivial) earlier
  have next := the_actual_guarded_work_visit_has_its_same_next_source_cursor nature (actualAdmission nature)
    (the_first_admission_is_the_actual_source_compiler_choice nature) 8 Control.Scenario.commonWork source
    (the_actual_risk_bearing_trial_retains_its_full_current_work_checks version tested)
  exact next.trans ((congrArg (fun cursor : CursorAt => Physical.next (Physical.receive cursor (.execute Control.Scenario.commonWork)))
    earlier).trans ((Physical.Prefix.cursor_append _ _).symm.trans
      (congrArg Physical.Prefix.cursor (List.append_assoc _ _ _))))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
