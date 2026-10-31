import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

structure ExactTransitionAt {current : Current}
    (occurrence : (source root boundary).toRootSource.actual.OccurrenceAt current)
    {targetSupport : (W root boundary).Support}
    (before : OpenResponsibilityAt (W root boundary) occurrence.1)
    (after : OpenResponsibilityAt (W root boundary) targetSupport) : Type where
  evolution : LedgerEntryEvolutionAt (W root boundary) before after

def remainderSource : LedgerTransportedRemainderSourceAt (source root boundary) (ExactTransitionAt root boundary) where
  OccurrenceAt := fun {current} _ target => PLift (target = supportAt root boundary (next current))
  emit? := by
    intro current occurrence target
    classical
    exact if same : target = supportAt root boundary (next current) then some ⟨same⟩ else none
  compileEvolution := by
    intro current occurrence target event
    rcases occurrence with ⟨oldSupport,origin⟩
    cases origin <;> rcases event with ⟨same⟩ <;> cases same <;> exact evolution root boundary _
  compileExact := by
    intro current occurrence target event
    rcases occurrence with ⟨oldSupport,origin⟩
    cases origin <;> rcases event with ⟨same⟩ <;> cases same
    all_goals exact {
      destination := fun entry => ⟨((evolution root boundary _).destination entry).2⟩
      origin := fun entry => ⟨((evolution root boundary _).origin entry).2⟩ }

def rowSource : LedgerWriteRowSourceAt (source root boundary) (ExactTransitionAt root boundary) where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun impossible => nomatch impossible
  compileExact := fun impossible => nomatch impossible
  transportedRemainderSource := remainderSource root boundary

def exceptionalRows (current : Current) : FiniteGeneratedLedgerWriteRowsAt
    (rowSource root boundary) (emitted root boundary current) ⟨supportAt root boundary (next current)⟩ where
  size := 0
  sourceEntryAt := Fin.elim0
  targetEntryAt := Fin.elim0
  rowAt := fun index => Fin.elim0 index

def remainderCoverage (current : Current) : LedgerTransportedRemainderCoverageAt (exceptionalRows root boundary current) where
  destinationIndex := fun _ => none
  originIndex := fun _ => none

theorem source_emits_the_whole_remainder (current : Current) :
    (remainderSource root boundary).emit? (emitted root boundary current)
      (supportAt root boundary (next current)) = some ⟨rfl⟩ := by
  classical
  simp [remainderSource]

def generatedRemainder (current : Current) : GeneratedLedgerTransportedRemainderAt
    (rowSource root boundary) (emitted root boundary current) ⟨supportAt root boundary (next current)⟩ :=
  (rowSource root boundary).generateTransportedRemainder _ _ ⟨rfl⟩
    (source_emits_the_whole_remainder root boundary current)

def patch (current : Current) : FiniteGeneratedLedgerWritePatchAt (rowSource root boundary)
    (emitted root boundary current) ⟨supportAt root boundary (next current)⟩ :=
  .transportedRemainder (exceptionalRows root boundary current) (remainderCoverage root boundary current)
    (generatedRemainder root boundary current)

private theorem ledger_ext {M : WorldRelationNetwork} {before after : CompleteLiveLedgerAt M}
    (left right : LedgerWriteEvolutionAt M before after)
    (destination : ∀ row,left.destination row = right.destination row)
    (origin : ∀ row,left.origin row = right.origin row) : left = right := by
  cases left
  cases right
  congr
  · funext row; exact destination row
  · funext row; exact origin row

theorem patch_is_the_complete_source_evolution (current : Current) :
    HEq (patch root boundary current).toLedgerWriteEvolution (evolution root boundary current) := by
  cases current <;> apply heq_of_eq <;> apply ledger_ext
  all_goals intro row; rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
