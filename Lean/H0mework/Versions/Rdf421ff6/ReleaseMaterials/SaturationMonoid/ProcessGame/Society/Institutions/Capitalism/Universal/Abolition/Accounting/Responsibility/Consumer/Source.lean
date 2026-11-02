import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Law
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Effects

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer

open Source.Program
open Innovation

abbrev programme := Control.Scenario.mechanism false
abbrev originalPast := [[],Control.Scenario.capitalWord]
abbrev nature := Control.Scenario.discovery 2

/-- The successful physical response pays the original migration cost; the
controlled actual branch is exactly the original closed occurrence. -/
def costedResponse : Control.Scenario.Response := fun history word raw =>
  (if 0 < raw.stock 2 .result then [Control.Scenario.migrationFee] else []) ++
    Control.Scenario.retaliation history word raw

set_option maxHeartbeats 1600000 in
theorem the_assessment_preserves_the_entire_original_actual_word :
    Control.responseWord programme originalPast nature costedResponse =
      Control.Scenario.word false nature Control.Scenario.retaliation := by
  have absent : ¬ 0 < (programme.after nature).stock 2 .result := by decide +kernel
  change programme.word nature ++ ((if 0 < (programme.after nature).stock 2 .result then
      [Control.Scenario.migrationFee] else []) ++
    Control.Scenario.retaliation originalPast (programme.word nature) (programme.after nature)) =
      programme.word nature ++ Control.Scenario.retaliation originalPast
        (programme.word nature) (programme.after nature)
  simp only [if_neg absent,List.nil_append]

set_option maxHeartbeats 1600000 in
theorem the_material_gap_has_three_original_bearers_and_one_joint_control_cohort :
    partyLoss programme originalPast nature costedResponse 0 .material = 8 ∧
      partyLoss programme originalPast nature costedResponse 1 .material = 5 ∧
      partyLoss programme originalPast nature costedResponse 2 .material = 5 ∧
      controllerCohort programme originalPast nature costedResponse = [2] := by decide +kernel

set_option maxHeartbeats 1600000 in
theorem the_policy_component_is_empty_for_this_original_unrestricted_law :
    policyOccurrences programme originalPast nature costedResponse = [] :=
  an_unrestricted_original_policy_has_no_policy_rejection _ _ _ _ rfl

set_option maxHeartbeats 1600000 in
theorem the_costed_source_productive_gap_is_the_original_eighteen_and_three :
    Control.measuredLoss programme originalPast nature costedResponse .material = 18 ∧
      Control.measuredLoss programme originalPast nature costedResponse .result = 3 := by decide +kernel

set_option maxHeartbeats 1600000 in
theorem the_original_harm_matrix_covers_every_member_and_good :
    ∀ actor : Control.Scenario.Party, ∀ good : Control.Scenario.Good,
      partyLoss programme originalPast nature costedResponse actor good =
        match good with
        | .material => if actor = 0 then 8 else 5
        | .result => if actor = 0 then 2 else if actor = 1 then 1 else 0
        | .message | .life | .maintenance => 0 := by
  intro actor good
  cases good <;> revert actor <;> decide +kernel

noncomputable def claim : AssessedClaim programme originalPast nature costedResponse 0 .material :=
  (assess programme originalPast nature costedResponse 0 .material).get (by
    have positive : 0 < partyLoss programme originalPast nature costedResponse 0 .material := by
      rw [the_material_gap_has_three_original_bearers_and_one_joint_control_cohort.1]
      norm_num
    simp [assess,positive])

theorem the_generated_claim_has_the_original_quantity : claim.quantity = 8 :=
  the_material_gap_has_three_original_bearers_and_one_joint_control_cohort.1

theorem the_pending_material_cursor_is_the_original_actual_successor :
    (State.initial claim).raw = Control.Scenario.law.next Control.Scenario.seed
      (Control.Scenario.word false nature Control.Scenario.retaliation) := by
  change Control.Scenario.law.next Control.Scenario.seed
    (Control.responseWord programme originalPast nature costedResponse) = _
  rw [the_assessment_preserves_the_entire_original_actual_word]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer
