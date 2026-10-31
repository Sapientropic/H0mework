import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Rows.Next
import H0mework.Foundation.Cofinal.ProductiveHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLedgerRootClosure N V) {current next : V.Current}
  (continued : (root.toRoot.evolutionAt current).nextCurrent? = some next)

def continuing : SourceNativeLedgerGeneratedSuccessorAt (root.emitted current) (root.generatedLedgerAt current) := by
  cases generated : root.generatedLedgerAt current with
  | nativeWrite => exact PUnit.unit
  | relationWrite => exact PUnit.unit
  | continuedTransport => exact PUnit.unit
  | borromeanRedirect => exact PUnit.unit
  | faithfulTerminal terminal structural evolution =>
      change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = _ at continued
      rw [structural] at continued
      cases continued

variable (living : SourceNativeLivingRootClosure N V)
  (visit : SourceNativeTemporalVisitAt living.toAuthoritativeRoot.toLedgerRoot)
  {after : V.Current}
  (nextEq : (living.toAuthoritativeRoot.toRoot.evolutionAt visit.current).nextCurrent? = some after)
  (row : OpenResponsibilityAt N (living.toAuthoritativeRoot.toRoot.supportAt visit.current))

theorem the_original_compiler_keeps_the_same_claim_and_never_refills :
    (living.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext nextEq row).claim = row.claim ∧
      (living.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext nextEq row).progressBudget ≤ row.progressBudget := by
  generalize chosen : continuing living.toAuthoritativeRoot.toLedgerRoot nextEq = actual
  have same : actual.targetCurrent = after := Option.some.inj (actual.next_eq.symm.trans nextEq)
  cases same
  exact (Evolving.nextRow_is_the_canonical_root_destination living visit actual row) ▸
    (Evolving.nextRow_keeps_claim_and_never_refills living visit actual row)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary
