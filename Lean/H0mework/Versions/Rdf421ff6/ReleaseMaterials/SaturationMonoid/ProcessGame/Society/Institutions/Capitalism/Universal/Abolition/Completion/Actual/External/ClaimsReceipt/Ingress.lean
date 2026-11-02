import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Ingress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.ClaimsReceipt

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth : Nat)

def decisionAt : Admission.InitialClaimsDecision input :=
  (Financial.Installation.Ingress.generated input depth).receipt.2.down

theorem the_decision_is_read_from_the_original_generated_receipt :
    decisionAt input depth = Admission.inspectInitialClaims input := rfl

theorem the_same_receipt_retains_the_original_material_payment :
    Financial.Installation.AccountSource.materialAt input (Financial.Installation.Ingress.start input depth)
      (Financial.Installation.Ingress.firstSuccessor input depth).targetCurrent =
      (Financial.Installation.Ingress.generated input depth).answer.after :=
  (Financial.Installation.Ingress.generated input depth).receipt.1.down.down

theorem the_same_receipt_retains_the_original_row_target_and_whole_next :
    (Financial.Installation.Ingress.generated input depth).target.translatedSourceEntry =
      Financial.Installation.Ingress.sourceEntry input depth ∧
    (Financial.Installation.Ingress.generated input depth).target.targetRoot =
      Financial.Installation.Ingress.targetRoot input depth ∧
    (Financial.Installation.Ingress.generated input depth).target.firstSuccessor =
      Financial.Installation.Ingress.firstSuccessor input depth ∧
    (Financial.Installation.Ingress.generated input depth).target.targetAnswerAndNext.nextCurrent =
      (Financial.Installation.Ingress.targetRoot input depth).generatedNextCurrentAt
        (.finite (Financial.Installation.Ingress.targetInitial input depth)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem every_initial_receipt_exposes_exact_balance_or_the_original_unrepresented_coordinate :
    match decisionAt input depth with
    | .represented _ => input.initial.claims = Admission.nativeInitialClaims input
    | .residual _ => ∃ instrument debtor creditor,
        input.initial.claims instrument debtor creditor ≠ Admission.nativeInitialClaims input instrument debtor creditor := by
  cases decisionAt input depth with
  | represented matching => exact matching
  | residual issue => exact issue.has_an_exact_original_matrix_coordinate input

#print axioms decisionAt
#print axioms the_same_receipt_retains_the_original_material_payment
#print axioms the_same_receipt_retains_the_original_row_target_and_whole_next
#print axioms every_initial_receipt_exposes_exact_balance_or_the_original_unrepresented_coordinate

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.ClaimsReceipt
