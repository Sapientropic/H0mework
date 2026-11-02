import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer.Origin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer.Residual
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer.Needs

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Innovation.Control Source.Program

noncomputable section

variable (word : RawEvent Scenario.Party Scenario.Good Bool Nat Unit)

theorem the_source_declaration_is_the_original_one_cursor_matrix :
    Source.declared input native visit C.familyClaim = Responsibility.Consumer.matrixActive :=
  congrArg (fun raw => Responsibility.Family.State.declare C.familyClaim
    (Responsibility.Family.State.atCursor C.familyClaim raw))
    the_live_physical_cursor_is_the_original_controlled_successor

theorem the_actual_input_has_the_same_rooted_material_interpretation :
    Source.observed input native visit C.familyClaim word =
      Responsibility.Family.State.advance C.familyClaim Responsibility.Consumer.matrixActive Scenario.openLaw word := by
  unfold Source.observed
  rw [the_source_declaration_is_the_original_one_cursor_matrix]
  rfl

theorem the_actual_root_repair_pays_the_entire_original_matrix :
    Responsibility.Family.State.isPaid C.familyClaim (Source.observed input native visit C.familyClaim C.matrixWord) := by
  rw [the_actual_input_has_the_same_rooted_material_interpretation]
  exact Responsibility.Consumer.one_actual_material_execution_clears_every_original_positive_cell

theorem nominal_credit_retains_the_same_original_unpaid_bearer :
    (Source.observed input native visit C.familyClaim Responsibility.Consumer.nominalMatrixWord).remaining (0,.material) = 8 := by
  rw [the_actual_input_has_the_same_rooted_material_interpretation]
  exact Responsibility.Consumer.a_new_iou_and_foreign_funding_cannot_move_the_original_material_cursor.2.2.1

theorem refusing_after_a_real_prefix_keeps_its_payment_in_the_original_account :
    (Source.observed input native visit C.familyClaim Responsibility.Consumer.paidPrefixThenRejected).remaining (0,.material) = 7 ∧
      (Source.observed input native visit C.familyClaim Responsibility.Consumer.paidPrefixThenRejected).raw.stock 0 .material =
        (Source.declared input native visit C.familyClaim).raw.stock 0 .material + 1 := by
  rw [the_actual_input_has_the_same_rooted_material_interpretation,
    the_source_declaration_is_the_original_one_cursor_matrix]
  exact Responsibility.Consumer.a_later_rejection_cannot_charge_again_for_the_original_real_paid_prefix

theorem full_material_delivery_does_not_issue_a_whole_world_terminal :
    (Responsibility.Family.activationLaw C.familyClaim).SupportTerminalAt
      (Source.observed input native visit C.familyClaim C.matrixWord) → False := by
  intro terminal
  exact nomatch terminal

#print axioms the_actual_root_repair_pays_the_entire_original_matrix
#print axioms refusing_after_a_real_prefix_keeps_its_payment_in_the_original_account

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer
