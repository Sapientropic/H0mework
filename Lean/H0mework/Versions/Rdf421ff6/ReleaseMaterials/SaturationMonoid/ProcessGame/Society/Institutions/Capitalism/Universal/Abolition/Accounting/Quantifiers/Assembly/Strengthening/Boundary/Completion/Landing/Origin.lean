import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot CategoryTheory
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}

private def priorSource (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) {after : V.Current}
    (nextEq : (root.toAuthoritativeRoot.toRoot.evolutionAt visit.current).nextCurrent? = some after)
    (row : OpenResponsibilityAt N (root.toAuthoritativeRoot.toRoot.supportAt after)) :
    OpenResponsibilityAt N (root.toAuthoritativeRoot.toRoot.supportAt visit.current) := by
  generalize chosen : Boundary.continuing root.toAuthoritativeRoot.toLedgerRoot nextEq = actual
  have same : actual.targetCurrent = after := Option.some.inj (actual.next_eq.symm.trans nextEq)
  cases same
  let selected : OpenResponsibilityAt N actual.targetOccurrence.1 :=
    Eq.mpr (congrArg (OpenResponsibilityAt N) (Evolving.nextSupportEq root visit actual)) row
  exact (actual.ledgerEvolution.origin selected).1

variable (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

/-- Reverse only the origins actually supplied by the original whole ledger. -/
def initialSource : (cut : Nat) → rows root boundary cut → rows root boundary 0
  | 0,original => original
  | cut + 1,original => initialSource cut
      (priorSource root (.finite (boundary.history.visitAt cut))
        (boundary.history.next_eq_at_visit cut) original)

theorem every_original_row_has_the_same_actual_source_lineage (cut : Nat) (row : rows root boundary cut) :
    N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt cut).current) =
      N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt 0).current) := by
  induction cut with
  | zero => rfl
  | succ cut earlier =>
      let prior := priorSource root (.finite (boundary.history.visitAt cut)) (boundary.history.next_eq_at_visit cut) row
      exact (actualReceipt root boundary cut prior).toDebtLineage.lineage_eq.symm.trans (earlier prior)

theorem every_completed_row_keeps_the_initial_actual_lineage (point : Carrier root boundary) :
    lineage root boundary point =
      N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt 0).current) := by
  obtain ⟨cut,original,rfl⟩ := every_completed_standing_has_an_original_actual_source root boundary point
  exact every_original_row_has_the_same_actual_source_lineage root boundary cut original

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
