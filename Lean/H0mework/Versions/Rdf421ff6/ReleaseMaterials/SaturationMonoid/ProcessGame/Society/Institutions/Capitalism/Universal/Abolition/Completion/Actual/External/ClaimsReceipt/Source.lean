import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def nativeInitialClaims := Financial.BalanceConservation.ledgerClaims input
  (Financial.Installation.Cursor.initial input).account.current

theorem the_canonical_native_genesis_has_zero_claims :
    nativeInitialClaims input = fun _ _ _ => 0 := rfl

/-- This is a failure of the empty native genesis to represent the original
raw debt matrix. The original raw source remains its exact residual bearer. -/
structure InitialClaimsResidual where
  private mk ::
  unrepresented : input.initial.claims ≠ nativeInitialClaims input

inductive InitialClaimsDecision
  | represented (matching : input.initial.claims = nativeInitialClaims input)
  | residual (issue : InitialClaimsResidual input)

def inspectInitialClaims : InitialClaimsDecision input := by
  classical
  exact if matching : input.initial.claims = nativeInitialClaims input then
    .represented matching else .residual ⟨matching⟩

theorem a_residual_cannot_be_signed_as_an_initial_native_balance
    (issue : InitialClaimsResidual input) :
    Financial.BalanceConservation.ledgerClaims input
      (Financial.Installation.Cursor.initial input).account.current ≠ input.initial.claims :=
  Ne.symm issue.unrepresented

theorem the_source_genesis_condition_is_exact :
    (∃ proof, inspectInitialClaims input = .represented proof) ↔
      input.initial.claims = fun _ _ _ => 0 := by
  constructor
  · rintro ⟨proof, _generated⟩
    exact proof.trans (the_canonical_native_genesis_has_zero_claims input)
  · intro zero
    have matching : input.initial.claims = nativeInitialClaims input :=
      zero.trans (the_canonical_native_genesis_has_zero_claims input).symm
    exact ⟨matching, dif_pos matching⟩

theorem InitialClaimsResidual.has_an_exact_original_matrix_coordinate
    (issue : InitialClaimsResidual input) :
    ∃ instrument debtor creditor,
      input.initial.claims instrument debtor creditor ≠ nativeInitialClaims input instrument debtor creditor := by
  classical
  by_contra missing
  apply issue.unrepresented
  funext instrument debtor creditor
  by_contra different
  exact missing ⟨instrument, debtor, creditor, different⟩

#print axioms inspectInitialClaims
#print axioms a_residual_cannot_be_signed_as_an_initial_native_balance
#print axioms InitialClaimsResidual.has_an_exact_original_matrix_coordinate

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.Admission
