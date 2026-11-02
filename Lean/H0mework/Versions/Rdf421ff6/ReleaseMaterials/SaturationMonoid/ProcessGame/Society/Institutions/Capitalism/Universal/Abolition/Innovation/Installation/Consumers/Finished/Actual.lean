import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Finished.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Settlement

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

def OriginalWholeNextAt (nature : RequestAt) (index : Nat) : Prop :=
  type_of% (every_scheduled_attempt_has_the_original_whole_root_and_next nature index)

theorem the_original_whole_next_is_generated_at_every_actual_trial_cut (nature : RequestAt) (index : Nat) :
    OriginalWholeNextAt nature index := every_scheduled_attempt_has_the_original_whole_root_and_next nature index

theorem the_completed_actual_trial_is_its_original_public_paid_raw
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (Physical.Public.stateAt input 0 count 0 0 (firstOrigin (Control.Scenario.discovery version)).germ.snapshot.past
      (actualPublicVisit (Control.Scenario.discovery version) 11).snapshot.past).raw =
        performanceFinalRaw
          (Physical.stateAt input 0 count 0 0 (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past).raw version := by
  let nature := Control.Scenario.discovery version
  let oldPast := (firstRaw nature).germ.snapshot.past
  have actual := the_same_actual_trial_completes_its_four_original_performance_attempts version tested
  have projected := congrArg (fun current : CursorAt =>
    (Physical.Public.stateAt input 0 count 0 0 oldPast current.past).raw) actual
  have sourcePast := congrArg (fun past : List InputAt => (Physical.Public.stateAt input 0 count 0 0 oldPast past).raw)
    (Physical.Prefix.past_readback (submittedInputs oldPast nature ++ performanceInputs version))
  exact projected.trans (sourcePast.trans (the_complete_original_public_syntax_has_its_same_finite_paid_raw oldPast version))

theorem the_same_named_original_engine_finishes_the_real_trial_with_the_original_claims
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (current (Control.Scenario.discovery version) (boundaryTick (Control.Scenario.discovery version) 12)).actualState.raw =
      performanceFinalRaw
        (Physical.stateAt input 0 count 0 0 (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past).raw version ∧
    PaidPerformance
      (Physical.stateAt input 0 count 0 0 (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past).raw version := by
  let nature := Control.Scenario.discovery version
  have source := every_public_visit_is_the_same_original_activated_frame nature (actualAdmission nature)
    (the_first_admission_is_the_actual_source_compiler_choice nature) 11
  have same := congrArg Macro.Runtime.ActivatedFrame.actualState source
  exact ⟨(congrArg (fun state : PhysicalState => state.raw) same).trans
      (the_completed_actual_trial_is_its_original_public_paid_raw version tested),
    every_original_three_branch_disposition_has_its_real_paid_contract _
      (the_first_actual_raw_is_in_its_actual_source_inventory nature) version tested⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
