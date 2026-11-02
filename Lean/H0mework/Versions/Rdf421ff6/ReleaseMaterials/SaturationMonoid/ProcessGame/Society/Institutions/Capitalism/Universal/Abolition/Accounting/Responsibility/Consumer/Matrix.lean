import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.Law

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer

open Source.Program
open Innovation

noncomputable section

def familyClaim : Family.Claim programme originalPast nature costedResponse :=
  (Family.assess programme originalPast nature costedResponse).get (by
    have positive : 0 < partyLoss programme originalPast nature costedResponse 0 .material := by
      rw [the_material_gap_has_three_original_bearers_and_one_joint_control_cohort.1]
      norm_num
    have member := Family.every_positive_original_harm_is_in_the_generated_scope
      programme originalPast nature costedResponse 0 .material positive
    have nonempty : Family.positiveScope programme originalPast nature costedResponse ≠ [] := by
      intro empty
      rw [empty] at member
      exact List.not_mem_nil member
    simp [Family.assess,nonempty])

theorem the_one_native_obligation_retains_the_whole_original_harm_matrix
    (raw : Control.Scenario.Current) (actor : Control.Scenario.Party) (good : Control.Scenario.Good) :
    (Family.State.atCursor familyClaim raw).remaining (actor,good) =
      match good with
      | .material => if actor = 0 then 8 else 5
      | .result => if actor = 0 then 2 else if actor = 1 then 1 else 0
      | .message | .life | .maintenance => 0 := by
  rw [Family.State.admission_remaining_is_the_positive_source_quantity]
  unfold Family.quantity
  rw [the_original_harm_matrix_covers_every_member_and_good]
  cases good <;> revert actor <;> decide +kernel

def matrixActive : Family.State familyClaim :=
  Family.State.declare familyClaim (Family.State.atCursor familyClaim (State.initial claim).raw)

/-- One actual production history covers all original victims and goods together.
The original controller does not sign or consent to its own execution. -/
def matrixWord : RawEvent Control.Scenario.Party Control.Scenario.Good Bool Nat Unit :=
  [⟨0,[],false,[],.revise 2 2⟩] ++
    List.replicate 4 ⟨0,[],false,[],.produce 2⟩ ++
    ([0,1,2] : List Control.Scenario.Party).flatMap (fun actor =>
      [⟨0,[],false,[],.use actor [(.life,1)] .necessity⟩,
       ⟨0,[],false,[],.use actor [(.maintenance,1)] .maintenance⟩]) ++
    [⟨0,[],false,[],.transfer 2 0 [(.material,8),(.result,2)]⟩,
     ⟨0,[],false,[],.transfer 2 1 [(.material,5),(.result,1)]⟩]

def matrixPaid := Family.State.advance familyClaim matrixActive Control.Scenario.openLaw matrixWord

set_option maxHeartbeats 2400000 in
theorem the_joint_execution_really_pays_every_member_and_preserves_the_old_financial_claims :
    (∀ item ∈ Control.Scenario.openLaw.rawItems matrixActive.raw matrixWord,
      Control.Scenario.openLaw.Valid item.before item.request) ∧
      Exit.Necessity.AllNeedsPaid Control.Scenario.openLaw matrixActive.raw [0,1,2] matrixWord ∧
      (∀ request ∈ matrixWord, request.signer = 0 ∧ request.consents = []) ∧
      (∀ request ∈ matrixWord, Family.materialOperation [2]
        (Family.positiveScope programme originalPast nature costedResponse) request) := by decide +kernel

set_option maxHeartbeats 2400000 in
theorem one_actual_material_execution_clears_every_original_positive_cell :
    Family.State.isPaid familyClaim matrixPaid := by decide +kernel

theorem the_joint_execution_preserves_every_old_financial_address :
    matrixPaid.raw.claims = matrixActive.raw.claims :=
  Family.State.actual_advance_retains_every_original_financial_claim _ _ _ _

def the_single_native_paid_step_contains_the_entire_matrix :
    (Family.activationLaw familyClaim).StepAt matrixActive matrixPaid :=
  Family.StepAt.paid _ Control.Scenario.openLaw matrixWord rfl
    (Family.State.atCursor_is_unpaid familyClaim (State.initial claim).raw)
    one_actual_material_execution_clears_every_original_positive_cell

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer
