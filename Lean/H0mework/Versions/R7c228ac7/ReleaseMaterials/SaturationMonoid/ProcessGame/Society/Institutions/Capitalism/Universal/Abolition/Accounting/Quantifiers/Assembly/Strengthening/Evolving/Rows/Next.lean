import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Entry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

private theorem cast_row_heq {N : WorldRelationNetwork} {left right : N.Support}
    (same : left = right) (row : OpenResponsibilityAt N left) :
    HEq (same ▸ row : OpenResponsibilityAt N right) row := by cases same; rfl

private def transport_receipt {N : WorldRelationNetwork} {sourceSupport left right : N.Support}
    {source : OpenResponsibilityAt N sourceSupport} {target : OpenResponsibilityAt N left}
    (same : left = right) (receipt : LedgerEntryEvolutionAt N source target) :
    LedgerEntryEvolutionAt N source (same ▸ target : OpenResponsibilityAt N right) := by
  cases same
  exact receipt

private theorem emitted_target {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} {current : V.Current}
    (emit : (state : V.Current) → source.toRootSource.actual.OccurrenceAt state)
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (image : SourceNativeLedgerEvolutionAt source occurrence)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence image)
    (commutes : image.CommutesWith emit) :
    successor.targetOccurrence = emit successor.targetCurrent := by
  cases image <;> first | exact commutes | exact successor.elim

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
  (successor : SourceNativeLedgerGeneratedSuccessorAt (root.emitted visit.current)
    (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current))

theorem nextSupportEq : successor.targetOccurrence.1 =
    root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt successor.targetCurrent :=
  congrArg Sigma.fst (emitted_target root.emitted _ successor (root.compiler_commutes visit.current))

def nextRow (row : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current)) :
    OpenResponsibilityAt N (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt successor.targetCurrent) :=
  nextSupportEq root visit successor ▸ (successor.ledgerEvolution.destination row).1

def nextReceipt (row : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current)) :
    LedgerEntryEvolutionAt N row (nextRow root visit successor row) :=
  transport_receipt (nextSupportEq root visit successor) (successor.ledgerEvolution.destination row).2

theorem nextRow_is_the_canonical_root_destination (row : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current)) :
    nextRow root visit successor row =
      root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext successor.next_eq row := by
  apply eq_of_heq
  exact (cast_row_heq (nextSupportEq root visit successor) _).trans
    (Abolition.Accounting.Root.Compiler.canonical_destination_heq
      root.toAuthoritativeRoot.toLedgerRoot _ _ successor.next_eq successor row).symm

theorem nextRow_keeps_claim_and_never_refills (row : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current)) :
    (nextRow root visit successor row).claim = row.claim ∧
      (nextRow root visit successor row).progressBudget ≤ row.progressBudget :=
  ⟨(nextReceipt root visit successor row).toDebtLineage.claim_eq.symm,
    (nextReceipt root visit successor row).progressBudget_not_refilled⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
