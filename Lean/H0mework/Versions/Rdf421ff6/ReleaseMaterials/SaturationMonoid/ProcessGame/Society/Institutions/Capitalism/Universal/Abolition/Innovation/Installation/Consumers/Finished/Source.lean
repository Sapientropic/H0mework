import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Failure
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Success
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Novel

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem every_original_three_branch_disposition_has_its_real_paid_contract
    (before : Raw) (original : before ∈ firstRawVariants) (version : Nat)
    (tested : version ∈ ([0,1,2] : List Nat)) : PaidPerformance before version := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at tested
  rcases tested with rfl | rfl | rfl
  · exact of_decide_eq_true ((List.all_eq_true.mp every_original_failed_trial_really_pays_the_finite_risk_loss) before original)
  · exact of_decide_eq_true ((List.all_eq_true.mp every_original_successful_trial_really_pays_principal_and_finite_reward) before original)
  · exact of_decide_eq_true ((List.all_eq_true.mp the_unlisted_technology_really_pays_the_original_fixed_contract) before original)

theorem the_complete_original_public_syntax_has_its_same_finite_paid_raw
    (oldPast : List InputAt) (version : Nat) :
    (Physical.Public.stateAt input 0 count 0 0 oldPast
      (submittedInputs oldPast (Control.Scenario.discovery version) ++ performanceInputs version)).raw =
        performanceFinalRaw (Physical.stateAt input 0 count 0 0 oldPast).raw version := by
  let nature := Control.Scenario.discovery version
  let prefixState := Physical.Public.stateAt input 0 count 0 0 oldPast
    (submittedInputs oldPast nature ++ [.primitive (riskLiability version)])
  let tail : List InputAt := [.execute Control.Scenario.commonWork,.primitive (firstSettlement version),.primitive (lastSettlement version)]
  have originalRaw := the_submitted_code_and_actual_risk_issue_have_the_original_checked_raw oldPast nature (riskLiability version)
  have explicit : ∀ raw ∈ tail, raw ≠ .advance := by
    intro raw member
    change raw ∈ [.execute Control.Scenario.commonWork,.primitive (firstSettlement version),.primitive (lastSettlement version)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> intro impossible <;> cases impossible
  have same := an_explicit_prefix_reads_only_its_original_raw prefixState
    ⟨trialRawAfterRiskLiability (Physical.stateAt input 0 count 0 0 oldPast).raw nature (riskLiability version),.seeking,[]⟩
    originalRaw tail explicit
  have shape : submittedInputs oldPast nature ++ performanceInputs version =
      (submittedInputs oldPast nature ++ [.primitive (riskLiability version)]) ++ tail := by
    change submittedInputs oldPast nature ++ ([.primitive (riskLiability version)] ++ tail) = _
    exact (List.append_assoc _ _ _).symm
  have fields := congrArg (fun past : List InputAt => (Physical.Public.stateAt input 0 count 0 0 oldPast past).raw) shape
  refine fields.trans ?_
  unfold Physical.Public.stateAt
  rw [List.foldl_append]
  exact same

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
