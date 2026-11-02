import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer.Actual

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation.Control Exit.Necessity

noncomputable section

local instance : Finite native.root.toAuthoritativeRoot.source.projectionLaw.Projection := original.projectionFinite

abbrev Word := RawEvent Scenario.Party Scenario.Good Bool Nat Unit
abbrev installed (word : Word) := Action.Installation.native input native visit C.familyClaim word

def originalMembers := (Financial.Installation.observe input (native.cursor visit.current)).members

def needFace (word : Word) : SourceNativeRootSemanticFaceAt
    (Source.Inquiry.root input (installed word) visit C.familyClaim word)
    (Source.Inquiry.temporalAt input (installed word) visit C.familyClaim word 1) where
  projection := .component .needs
  active := PUnit.unit
  classifier_eq := rfl

abbrev NeedAt (word : Word) := Responsibility.Family.NeedDisposition (Source.actualLaw input)
  (Source.declared input native visit C.familyClaim).raw
  (Responsibility.Family.State.attempt C.familyClaim (Source.declared input native visit C.familyClaim)
    (Source.actualLaw input) word).actualWord originalMembers

def actualNeeds (word : Word) : NeedAt word := (needFace word).rootRead

theorem the_need_face_belongs_to_the_same_actual_runtime_root (word : Word) :
    ((runtime word).stateAt 2).engine.node =
      .active (Source.Inquiry.presentationAt input (installed word) visit C.familyClaim word 1) :=
  Action.Runtime.the_actual_repair_then_keeps_its_residual_root_active
    input native visit C.familyClaim originalOrigin word originalAuthority

private theorem positive_actual_word :
    (Responsibility.Family.State.attempt C.familyClaim (Source.declared input native visit C.familyClaim)
      (Source.actualLaw input) C.matrixWord).actualWord = C.matrixWord := by
  rw [the_source_declaration_is_the_original_one_cursor_matrix]
  have source := Responsibility.Consumer.the_joint_execution_really_pays_every_member_and_preserves_the_old_financial_claims.2.2.2
  rw [← Responsibility.Consumer.the_material_gap_has_three_original_bearers_and_one_joint_control_cohort.2.2.2] at source
  change (Responsibility.Family.inspectAttempt Scenario.openLaw Responsibility.Consumer.matrixActive.raw
    (Responsibility.controllerCohort C.programme C.originalPast C.nature C.costedResponse)
    (Responsibility.Family.positiveScope C.programme C.originalPast C.nature C.costedResponse) C.matrixWord).actualWord = _
  unfold Responsibility.Family.inspectAttempt
  cases read : Responsibility.Family.inspectSource _ _ C.matrixWord with
  | accepted checked =>
      cases Responsibility.inspectMaterial Scenario.openLaw (Scenario.openLaw.rawItems Responsibility.Consumer.matrixActive.raw C.matrixWord) <;> rfl
  | rejected request member foreign => exact (foreign (source request member)).elim

theorem the_actual_root_need_report_accepts_the_paid_full_matrix :
    match actualNeeds C.matrixWord with
    | .paid _ => True
    | .necessity .. | .maintenance .. => False := by
  have paid : AllNeedsPaid (Source.actualLaw input) (Source.declared input native visit C.familyClaim).raw
      originalMembers (Responsibility.Family.State.attempt C.familyClaim
        (Source.declared input native visit C.familyClaim) (Source.actualLaw input) C.matrixWord).actualWord := by
    rw [positive_actual_word,the_source_declaration_is_the_original_one_cursor_matrix]
    intro actor _
    apply Responsibility.Consumer.the_joint_execution_really_pays_every_member_and_preserves_the_old_financial_claims.2.1
    fin_cases actor <;> decide
  cases actualNeeds C.matrixWord with
  | paid => trivial
  | necessity actor member missing => exact missing (paid actor member).1
  | maintenance actor member missing => exact missing (paid actor member).2

set_option maxHeartbeats 2400000 in
private theorem original_zero_member : (0 : Scenario.Party) ∈ originalMembers := by
  change 0 ∈ Source.ProgrammeFace.ActualBirth.participants input
    (Financial.Installation.Cursor.lastExecutedVisit input (original.cursor input))
  rw [cursor_eq]
  unfold Financial.Installation.Cursor.lastExecutedVisit
  rw [the_original_native_cursor_has_finished_the_complete_controlled_inventory.1]
  decide +kernel

private theorem no_needs_word_leaves_the_original_bearer_unpaid :
    ¬ BundlePaid (Source.actualLaw input) (Source.declared input native visit C.familyClaim).raw
      (Responsibility.Family.State.attempt C.familyClaim (Source.declared input native visit C.familyClaim)
        (Source.actualLaw input) Responsibility.Consumer.noNeedsWord).actualWord 0
      ((Source.actualLaw input).necessities (Source.declared input native visit C.familyClaim).raw 0) .necessity := by
  rw [the_source_declaration_is_the_original_one_cursor_matrix]
  generalize Responsibility.Family.State.attempt C.familyClaim Responsibility.Consumer.matrixActive
    (Source.actualLaw input) Responsibility.Consumer.noNeedsWord = attempted
  cases attempted <;> simp only [Responsibility.Family.Attempt.actualWord] <;> decide +kernel

theorem a_zero_matrix_cannot_hide_the_actual_original_need_bearer :
    Responsibility.Family.State.isPaid C.familyClaim (actualState Responsibility.Consumer.noNeedsWord) ∧
      match actualNeeds Responsibility.Consumer.noNeedsWord with
      | .paid _ => False
      | .necessity actor _member _ | .maintenance actor _member _ => actor ∈ originalMembers := by
  constructor
  · rw [actualState_eq,the_actual_input_has_the_same_rooted_material_interpretation]
    exact Responsibility.Consumer.clearing_the_control_matrix_does_not_hide_an_unpaid_necessity_bearer.1
  · cases actualNeeds Responsibility.Consumer.noNeedsWord with
    | paid complete => exact no_needs_word_leaves_the_original_bearer_unpaid (complete 0 original_zero_member).1
    | necessity actor member missing => exact member
    | maintenance actor member missing => exact member

#print axioms the_actual_root_need_report_accepts_the_paid_full_matrix
#print axioms a_zero_matrix_cannot_hide_the_actual_original_need_bearer

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer
