import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.ClaimsReceipt.Ingress
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.ClaimsReceipt

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open M14SourceGeneratedContributionMergeActionSource SourceNativeInquiryRuntime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (positive : 0 < ProgrammeSource.registrationSize input)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)

local notation "originalRuntime" => Financial.Installation.Runtime.sourceRuntime input positive oldVisit sourceIndex boundary

def actualDecision : Admission.InitialClaimsDecision input :=
  ((originalRuntime).tickAt 1).receipt.2.2.down

theorem the_actual_root_receipt_is_the_original_source_decision :
    actualDecision input positive oldVisit sourceIndex boundary = Admission.inspectInitialClaims input := rfl

theorem the_same_actual_runtime_consumes_the_original_input_and_financial_ingress :
    CofaceRealizationResumptionAt
      (Financial.Installation.Runtime.originalInputCore input oldVisit sourceIndex boundary)
      originalRuntime 0 ∧
    SequentialActualActionResumptionAt (Financial.Installation.Ingress.generated input 1)
      originalRuntime 1 :=
  ⟨⟨HEq.rfl⟩, ⟨HEq.rfl⟩⟩

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem the_actual_registered_input_is_the_same_complete_raw_source :
    (InputSource.registeredInput (Financial.Installation.Runtime.datum input)
      (InputSource.visit (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary)).query.raw =
      .programme input := rfl

theorem the_actual_ingress_keeps_its_original_root_next :
    ((originalRuntime).tickAt 1).next.node =
      .active ((Financial.Installation.Runtime.initialFrame input 1).presentation input) := rfl

theorem the_actual_ingress_preserves_the_whole_generated_living_law :
    ((originalRuntime).stateAt 1).engine.node.PreservesGeneratedLivingLawAt
      ((originalRuntime).stateAt 1).activation.query ((originalRuntime).tickAt 1).next.node :=
  ((originalRuntime).tickAt 1).rawReadout.next_preservesGeneratedLivingLaw

theorem every_actual_initial_receipt_exposes_exact_balance_or_its_original_residual :
    match actualDecision input positive oldVisit sourceIndex boundary with
    | .represented _ => input.initial.claims = Admission.nativeInitialClaims input
    | .residual _ => ∃ instrument debtor creditor,
        input.initial.claims instrument debtor creditor ≠ Admission.nativeInitialClaims input instrument debtor creditor := by
  rw [the_actual_root_receipt_is_the_original_source_decision]
  cases result : Admission.inspectInitialClaims input with
  | represented matching => exact matching
  | residual issue => exact issue.has_an_exact_original_matrix_coordinate input

#print axioms actualDecision
#print axioms the_same_actual_runtime_consumes_the_original_input_and_financial_ingress
#print axioms the_actual_registered_input_is_the_same_complete_raw_source
#print axioms the_actual_ingress_keeps_its_original_root_next
#print axioms the_actual_ingress_preserves_the_whole_generated_living_law
#print axioms every_actual_initial_receipt_exposes_exact_balance_or_its_original_residual

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.ClaimsReceipt
