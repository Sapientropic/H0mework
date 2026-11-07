import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Certification
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Inherited
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Theory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def restructuredSource : SourceNativeRestructuringLedgerSource (W root boundary) (SchemaV root boundary) where
  source := source root boundary
  compiler := {
    ledgerCompiler := ledgerCompiler root boundary
    restructuringLaw := Restructuring.law root boundary
    certifyRestructuring := Restructuring.certification root boundary }

def authoritySource : SourceNativeAuthoritySource (W root boundary) (SchemaV root boundary) where
  restructuringSource := restructuredSource root boundary
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuredSource root boundary)
    (fun _ => ⟨fun impossible => nomatch impossible⟩)
  lawSurface := retainedTheory root boundary
  projectionLaw := inheritedLaw root boundary
  observationAt := fun {current} _ => root.source.base.observationAt (rawOccurrence root boundary current)

def completedRoot : SourceNativeLivingRootClosure (W root boundary) (SchemaV root boundary) where
  source := {
    base := authoritySource root boundary
    terminalHandoff := (authoritySource root boundary).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => nomatch impossible⟩) }
  emitted := emitted root boundary
  compiler_commutes := by intro current; cases current <;> rfl

theorem the_completed_root_uses_the_actual_source_ledger :
    (completedRoot root boundary).toAuthoritativeRoot.toLedgerRoot = ledgerRoot root boundary := rfl

theorem the_completed_root_retains_the_original_theory :
    (completedRoot root boundary).source.base.lawSurface = retainedTheory root boundary := rfl

theorem the_completed_root_retains_every_original_observation (current : Current) :
    (completedRoot root boundary).source.base.observationAt (emitted root boundary current) =
      root.source.base.observationAt (rawOccurrence root boundary current) := rfl

theorem the_completed_root_retains_every_original_query
    (current : Current) (projection : (originalProjection root).Projection) :
    (completedRoot root boundary).source.base.projectionLaw.outcomeAt projection (emitted root boundary current) =
      (originalProjection root).outcomeAt projection (rawOccurrence root boundary current) :=
  every_original_query_keeps_its_entire_source_fibre root boundary current projection

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
