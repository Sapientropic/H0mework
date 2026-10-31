import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

abbrev originalProjection := root.source.base.projectionLaw

/-- The old query inventory, complete active/inactive fibres and payloads,
is fixed in the completed source before its emitter is supplied. -/
def inheritedLaw : SourceNativeProjectionLaw (ledgerSource root boundary) where
  Projection := (originalProjection root).Projection
  ActiveAt := fun projection {current} _ =>
    (originalProjection root).ActiveAt projection (rawOccurrence root boundary current)
  InactiveAt := fun projection {current} _ =>
    (originalProjection root).InactiveAt projection (rawOccurrence root boundary current)
  classify := fun projection {current} _ =>
    (originalProjection root).classify projection (rawOccurrence root boundary current)
  PayloadAt := fun projection {current} _ active =>
    (originalProjection root).PayloadAt projection (rawOccurrence root boundary current) active
  project := fun projection {current} _ active =>
    (originalProjection root).project projection (rawOccurrence root boundary current) active

theorem every_original_query_keeps_its_entire_source_fibre
    (current : Current) (projection : (originalProjection root).Projection) :
    (inheritedLaw root boundary).outcomeAt projection (emitted root boundary current) =
      (originalProjection root).outcomeAt projection (rawOccurrence root boundary current) := by
  cases classification : (originalProjection root).classify projection (rawOccurrence root boundary current)
  all_goals simp only [SourceNativeProjectionLaw.outcomeAt,inheritedLaw,classification]

theorem finite_queries_read_their_original_actual_occurrence
    (cut : Nat) (projection : (originalProjection root).Projection) :
    (inheritedLaw root boundary).outcomeAt projection (emitted root boundary (.inl cut)) =
      (originalProjection root).outcomeAt projection (root.emitted (boundary.history.visitAt cut).current) :=
  every_original_query_keeps_its_entire_source_fibre root boundary (.inl cut) projection

theorem landing_queries_read_the_original_actual_target
    (phase : Nat) (projection : (originalProjection root).Projection) :
    (inheritedLaw root boundary).outcomeAt projection (emitted root boundary (.inr phase)) =
      (originalProjection root).outcomeAt projection (root.emitted boundary.current) :=
  every_original_query_keeps_its_entire_source_fibre root boundary (.inr phase) projection

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
