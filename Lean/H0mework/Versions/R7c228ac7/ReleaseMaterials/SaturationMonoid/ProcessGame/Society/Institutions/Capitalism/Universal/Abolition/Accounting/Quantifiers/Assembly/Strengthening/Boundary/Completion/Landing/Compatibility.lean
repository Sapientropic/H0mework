import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.World

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def Compatible : Prop := ∀ point : Carrier root boundary,
  lineage root boundary point = N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt boundary.current)

/-- The exact original standing is retained when the source's landing lineage
cannot receive it. No absence of a row is inferred from this stronger index failure. -/
structure LineageFailure : Type where
  cut : Nat
  original : rows root boundary cut
  incompatible : N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt cut).current) ≠
    N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt boundary.current)

/-- Selection inspects original lineage coordinates and the original first
ledger, rather than asking an oracle whether a landing target exists. -/
def inspectCompatibility : PLift (Compatible root boundary) ⊕ LineageFailure root boundary := by
  classical
  by_cases same :
      N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt 0).current) =
        N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt boundary.current)
  · exact .inl ⟨fun point => (every_completed_row_keeps_the_initial_actual_lineage root boundary point).trans same⟩
  · by_cases originalExists : Nonempty (rows root boundary 0)
    · exact .inr ⟨0,Classical.choice originalExists,same⟩
    · exact .inl ⟨fun point => False.elim (by
        obtain ⟨cut,original,_⟩ := every_completed_standing_has_an_original_actual_source root boundary point
        exact originalExists ⟨initialSource root boundary cut original⟩)⟩

def registerOriginal (compatible : Compatible root boundary) (cut : Nat) (original : rows root boundary cut) :
    LedgerEntryEvolutionAt (W root boundary) (oldRow root boundary false original)
      (landingRow root boundary (includeRow root boundary cut original) (compatible _)) :=
  .transferred (.inr (.past cut original))
    (compatible (includeRow root boundary cut original))
    (the_completion_reads_each_literal_original_claim root boundary cut original).symm
    (completed_original_budgets_never_refill root boundary cut original)

theorem registration_never_declares_a_new_claim (compatible : Compatible root boundary)
    (cut : Nat) (original : rows root boundary cut) :
    (registerOriginal root boundary compatible cut original).toDebtLineage.claim_eq =
      (the_completion_reads_each_literal_original_claim root boundary cut original).symm := rfl

theorem canonical_registration_cannot_launder_an_old_debt_as_fresh
    (compatible : Compatible root boundary) (cut : Nat) (original : rows root boundary cut) :
    IsEmpty (RootDebtFreshAt (W root boundary)
      (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt cut).current,false)
      (landingRow root boundary (includeRow root boundary cut original) (compatible _))) :=
  ⟨fun fresh => PEmpty.elim (fresh.noPrior (oldRow root boundary false original)
    (registerOriginal root boundary compatible cut original).toDebtLineage)⟩

theorem the_failed_original_has_no_canonical_landing_incidence (failure : LineageFailure root boundary) :
    IsEmpty ((W root boundary).OpenAt
      (root.toAuthoritativeRoot.toRoot.supportAt boundary.current,true)
      (.inr (includeRow root boundary failure.cut failure.original))) :=
  ⟨fun alleged => failure.incompatible alleged.down⟩

theorem incompatible_sources_cannot_register_every_original_row (failure : LineageFailure root boundary) :
    ¬ Compatible root boundary := by
  intro compatible
  apply failure.incompatible
  exact compatible (includeRow root boundary failure.cut failure.original)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
