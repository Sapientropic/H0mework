import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Rows.Paid
import H0mework.Versions.R2.Foundation.Source.SequentialAction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  {root : SourceNativeLivingRootClosure N V}
  {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
  {entry : OpenResponsibilityAt N (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current)}
  {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}
  {program : SourceNativeSequentialActualActionProgramAt root visit entry authority}
  {event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit}
  (generated : SourceGeneratedSequentialActualActionAt program event)
  (rows : PaidRowsAt N (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current))

local notation "target" => generated.target

def sequentialInitialRows : PaidRowsAt (target).TargetN
    ((target).targetRoot.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt
      (target).targetRoot.toAuthoritativeRoot.toRoot.source.initial) where
  productive := (target).initialOpenLedger.forward rows.productive
  gross := (target).initialOpenLedger.forward rows.gross
  productive_zero := Nat.eq_zero_of_le_zero (rows.productive_zero ▸ (target).initialLedger_budget_conservative rows.productive)
  gross_zero := Nat.eq_zero_of_le_zero (rows.gross_zero ▸ (target).initialLedger_budget_conservative rows.gross)
  different_claims := by
    intro same
    have mapped : (target).translation.claim.forward rows.productive.claim = (target).translation.claim.forward rows.gross.claim :=
      ((target).initialLedger_claim_commutes rows.productive).trans
        (same.trans ((target).initialLedger_claim_commutes rows.gross).symm)
    have original := congrArg (target).translation.claim.backward mapped
    exact rows.different_claims (by simpa only [(target).translation.claim.backward_forward] using original)

def afterSequential : PaidRowsAt (target).TargetN
    ((target).targetRoot.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt (target).targetVisit.current) :=
  nextPaidRows (target).targetRoot (target).targetInitialVisit (target).firstSuccessor (sequentialInitialRows generated rows)

theorem sequential_preserves_both_original_claim_images :
    (afterSequential generated rows).productive.claim = (target).translation.claim.forward rows.productive.claim ∧
      (afterSequential generated rows).gross.claim = (target).translation.claim.forward rows.gross.claim :=
  ⟨(nextPaidRows_preserves_both_original_claims (target).targetRoot (target).targetInitialVisit
      (target).firstSuccessor (sequentialInitialRows generated rows)).1.trans
        ((target).initialLedger_claim_commutes rows.productive).symm,
    (nextPaidRows_preserves_both_original_claims (target).targetRoot (target).targetInitialVisit
      (target).firstSuccessor (sequentialInitialRows generated rows)).2.trans
        ((target).initialLedger_claim_commutes rows.gross).symm⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
