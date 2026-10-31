import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} (code : Code N)

def remainderSource : LedgerTransportedRemainderSourceAt (source code) (ExactTransitionAt code) where
  OccurrenceAt := fun {current} occurrence target => PLift (target = code.supportAt (code.next current) (originalOccurrence code occurrence))
  emit? := by
    intro current occurrence target
    classical
    exact if same : target = code.supportAt (code.next current) (originalOccurrence code occurrence) then some ⟨same⟩ else none
  compileEvolution := by
    intro current occurrence target event
    rcases occurrence with ⟨oldSupport,originEvent⟩
    cases originEvent
    rcases event with ⟨same⟩
    cases same
    exact code.evolution current _
  compileExact := by
    intro current occurrence target event
    rcases occurrence with ⟨oldSupport,originEvent⟩
    cases originEvent
    rcases event with ⟨same⟩
    cases same
    exact {
      destination := fun entry => ⟨((code.evolution current _).destination entry).2⟩
      origin := fun entry => ⟨((code.evolution current _).origin entry).2⟩ }

def rowSource : LedgerWriteRowSourceAt (source code) (ExactTransitionAt code) where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun impossible => nomatch impossible
  compileExact := fun impossible => nomatch impossible
  transportedRemainderSource := remainderSource code

def exceptionalRows (current : code.Current) (origin : code.Fibre) : FiniteGeneratedLedgerWriteRowsAt
    (rowSource code) (represented code current origin) ⟨code.supportAt (code.next current) origin⟩ where
  size := 0
  sourceEntryAt := Fin.elim0
  targetEntryAt := Fin.elim0
  rowAt := fun index => Fin.elim0 index

def remainderCoverage (current : code.Current) (origin : code.Fibre) : LedgerTransportedRemainderCoverageAt (exceptionalRows code current origin) where
  destinationIndex := fun _ => none
  originIndex := fun _ => none

theorem remainder_is_generated_by_the_source (current : code.Current) (origin : code.Fibre) :
    (remainderSource code).emit? (represented code current origin) (code.supportAt (code.next current) origin) = some ⟨rfl⟩ := by
  classical
  simp [remainderSource,original_represented]

def generatedRemainder (current : code.Current) (origin : code.Fibre) : GeneratedLedgerTransportedRemainderAt (rowSource code)
    (represented code current origin) ⟨code.supportAt (code.next current) origin⟩ :=
  (rowSource code).generateTransportedRemainder (represented code current origin) _ ⟨rfl⟩
    (remainder_is_generated_by_the_source code current origin)

def patch (current : code.Current) (origin : code.Fibre) : FiniteGeneratedLedgerWritePatchAt (rowSource code)
    (represented code current origin) ⟨code.supportAt (code.next current) origin⟩ :=
  .transportedRemainder (exceptionalRows code current origin) (remainderCoverage code current origin) (generatedRemainder code current origin)

private theorem ledgerEvolution_ext {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    (left right : LedgerWriteEvolutionAt N sourceLedger targetLedger)
    (destination : ∀ entry,left.destination entry = right.destination entry)
    (origin : ∀ entry,left.origin entry = right.origin entry) : left = right := by
  cases left
  cases right
  congr
  · funext entry; exact destination entry
  · funext entry; exact origin entry

theorem patch_is_the_complete_original_transport (current : code.Current) (origin : code.Fibre) :
    (patch code current origin).toLedgerWriteEvolution = code.evolution current origin := by
  apply ledgerEvolution_ext
  · intro entry
    change (generatedRemainder code current origin).evolution.destination entry = _
    rfl
  · intro entry
    change (generatedRemainder code current origin).evolution.origin entry = _
    rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler
