import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Rows.Next

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

/-- Two readouts of the original complete ledger; no separate account or registry. -/
structure PaidRowsAt (N : WorldRelationNetwork) (support : N.Support) where
  productive : OpenResponsibilityAt N support
  gross : OpenResponsibilityAt N support
  productive_zero : productive.progressBudget = 0
  gross_zero : gross.progressBudget = 0
  different_claims : productive.claim ≠ gross.claim

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
  (successor : SourceNativeLedgerGeneratedSuccessorAt (root.emitted visit.current)
    (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current))
  (rows : PaidRowsAt N (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current))

def nextPaidRows : PaidRowsAt N (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt successor.targetCurrent) where
  productive := nextRow root visit successor rows.productive
  gross := nextRow root visit successor rows.gross
  productive_zero := Nat.eq_zero_of_le_zero (rows.productive_zero ▸
    (nextRow_keeps_claim_and_never_refills root visit successor rows.productive).2)
  gross_zero := Nat.eq_zero_of_le_zero (rows.gross_zero ▸
    (nextRow_keeps_claim_and_never_refills root visit successor rows.gross).2)
  different_claims := by
    rw [(nextRow_keeps_claim_and_never_refills root visit successor rows.productive).1,
      (nextRow_keeps_claim_and_never_refills root visit successor rows.gross).1]
    exact rows.different_claims

theorem nextPaidRows_preserves_both_original_claims :
    (nextPaidRows root visit successor rows).productive.claim = rows.productive.claim ∧
      (nextPaidRows root visit successor rows).gross.claim = rows.gross.claim :=
  ⟨(nextRow_keeps_claim_and_never_refills root visit successor rows.productive).1,
    (nextRow_keeps_claim_and_never_refills root visit successor rows.gross).1⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
