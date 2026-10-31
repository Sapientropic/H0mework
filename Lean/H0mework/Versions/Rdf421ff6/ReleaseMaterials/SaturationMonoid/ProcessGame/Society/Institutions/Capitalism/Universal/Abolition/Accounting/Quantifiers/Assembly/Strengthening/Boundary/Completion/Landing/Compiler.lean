import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Patch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def terminalRowSource : LedgerTerminalRowSourceAt (source root boundary) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => nomatch impossible

def packet {current : Current} (occurrence : (source root boundary).toRootSource.actual.OccurrenceAt current) :
    Σ image : SourceNativeLedgerEvolutionAt (source root boundary) occurrence,
      SourceNativeFiniteLedgerPatchAt (source root boundary) (ExactTransitionAt root boundary)
        (rowSource root boundary) (terminalRowSource root boundary) image := by
  rcases occurrence with ⟨support,event⟩
  cases event with
  | finite cut =>
      exact ⟨.nativeWrite (.computed (.inl cut)) rfl
        (emitted root boundary (next (.inl cut))) (patch root boundary (.inl cut)).toLedgerWriteEvolution,
        ⟨patch root boundary (.inl cut),rfl⟩⟩
  | landing phase =>
      exact ⟨.nativeWrite (.computed (.inr phase)) rfl
        (emitted root boundary (next (.inr phase))) (patch root boundary (.inr phase)).toLedgerWriteEvolution,
        ⟨patch root boundary (.inr phase),rfl⟩⟩

def ledgerCompiler : SourceNativeLedgerCompiler (source root boundary) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := ExactTransitionAt root boundary
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun exact => exact.evolution.toDebtLineage.lineage_eq
  writeRowSource := rowSource root boundary
  terminalRowSource := terminalRowSource root boundary
  compile := fun occurrence => (packet root boundary occurrence).1
  compilePatch := fun occurrence => (packet root boundary occurrence).2

def ledgerSource : SourceNativeLedgerSource (W root boundary) (SchemaV root boundary) where
  source := source root boundary
  ledgerCompiler := ledgerCompiler root boundary

def ledgerRoot : SourceNativeLedgerRootClosure (W root boundary) (SchemaV root boundary) where
  source := ledgerSource root boundary
  emitted := emitted root boundary
  compiler_commutes := by intro current; cases current <;> rfl

theorem the_source_compiler_selects_its_computed_next (current : Current) :
    ((ledgerRoot root boundary).toRoot.evolutionAt current).nextCurrent? = some (next current) := by
  cases current <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
