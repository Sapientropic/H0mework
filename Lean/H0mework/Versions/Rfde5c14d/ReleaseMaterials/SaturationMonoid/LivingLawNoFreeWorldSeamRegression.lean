import H0mework.Versions.R2.Foundation.Cofinal.TemporalAnswer

/-!
# Regression: stored incidence rows cannot disappear from the world seam

The hostile patch stores the same exact generated row twice while selecting
neither slot.  The rows remain available as diagnostic inventory and the patch
folds to identity, but the canonical authority producer returns `none`.

The positive theorem records the repaired contract: every authoritative row's
dependent target and evolution are exactly those used by the world fold.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoFreeWorldSeamRegression

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {source : SourceNativeSource N V}
variable {ExactTransitionAt :
  {current : V.Current} →
  (occurrence : source.toRootSource.actual.OccurrenceAt current) →
  {targetSupport : N.Support} →
  OpenResponsibilityAt N
    (source.toRootSource.account.supportOf occurrence) →
  OpenResponsibilityAt N targetSupport → Type u}
variable {rowSource : LedgerWriteRowSourceAt source ExactTransitionAt}
variable {current : V.Current}
variable {occurrence : source.toRootSource.actual.OccurrenceAt current}
variable {sourceEntry targetEntry : OpenResponsibilityAt N
  (source.toRootSource.account.supportOf occurrence)}

def duplicateRowsOf
    (row : GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry targetEntry) :
    FiniteGeneratedLedgerWriteRowsAt rowSource occurrence
      ⟨source.toRootSource.account.supportOf occurrence⟩ where
  size := 2
  sourceEntryAt := fun _ => sourceEntry
  targetEntryAt := fun _ => targetEntry
  rowAt := fun _ => row

def duplicateIgnoredCoverageOf
    (row : GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry targetEntry) :
    LedgerIdentityRemainderCoverageAt (duplicateRowsOf row) where
  destinationIndex := fun _ => none
  originIndex := fun _ => none

def duplicateIgnoredPatchOf
    (row : GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry targetEntry) :
    FiniteGeneratedLedgerWritePatchAt rowSource occurrence
      ⟨source.toRootSource.account.supportOf occurrence⟩ :=
  .identityRemainder (duplicateRowsOf row) (duplicateIgnoredCoverageOf row)

theorem duplicate_rows_repeat_the_exact_generated_event
    (row : GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry targetEntry) :
    (duplicateRowsOf row).rowAt ⟨0, Nat.zero_lt_succ 1⟩ = row ∧
      (duplicateRowsOf row).rowAt
        ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ = row :=
  ⟨rfl, rfl⟩

theorem ignored_rows_fold_to_identity
    (row : GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry targetEntry) :
    (duplicateIgnoredPatchOf row).toLedgerWriteEvolution =
      LedgerWriteEvolutionAt.identity
        ⟨source.toRootSource.account.supportOf occurrence⟩ :=
  rfl

/-- The old stored positions do not become authority when the world selector
omits them. -/
theorem ignored_rows_generate_no_canonical_authority
    (row : GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry targetEntry) :
    (duplicateIgnoredPatchOf row).canonicalGeneratedSourceRow? sourceEntry =
      none :=
  rfl

theorem canonical_row_target_and_evolution_align
    {target : CompleteLiveLedgerAt N}
    {patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target}
    {entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    (selected : patch.CanonicalGeneratedSourceRowAt entry) :
    selected.targetEntry =
        (patch.toLedgerWriteEvolution.destination entry).1 ∧
      HEq selected.row.evolution
        (patch.toLedgerWriteEvolution.destination entry).2 :=
  ⟨selected.target_eq_fold, selected.evolution_heq_fold⟩

namespace Terminal

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {source : SourceNativeSource N V}
variable {rowSource : LedgerTerminalRowSourceAt source}
variable {current : V.Current}
variable {occurrence : source.toRootSource.actual.OccurrenceAt current}
variable {entry : OpenResponsibilityAt N
  (source.toRootSource.account.supportOf occurrence)}

/-- Hostile terminal inventory: two stored rows name the same entry, while the
world fold canonically selects only slot zero. -/
def duplicateTerminalPatchOf
    (entryUnique : (other : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) → other = entry)
    (first second : GeneratedLedgerTerminalRowAt rowSource occurrence entry) :
    FiniteGeneratedLedgerTerminalPatchAt rowSource occurrence where
  size := 2
  entryAt := fun _ => entry
  rowAt := fun index => Fin.cases first (fun _ => second) index
  entryIndex := fun _ => ⟨0, Nat.zero_lt_succ 1⟩
  entry_sound := fun other => (entryUnique other).symm

def storedSiblingOf
    (entryUnique : (other : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) → other = entry)
    (first second : GeneratedLedgerTerminalRowAt rowSource occurrence entry) :
    (duplicateTerminalPatchOf entryUnique first second).GeneratedEntryAt entry :=
  ⟨⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩, rfl⟩

def canonicalTerminalOf
    (entryUnique : (other : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) → other = entry)
    (first second : GeneratedLedgerTerminalRowAt rowSource occurrence entry) :
    FiniteGeneratedLedgerTerminalPatchAt.CanonicalGeneratedEntryAt
      (duplicateTerminalPatchOf entryUnique first second) entry :=
  FiniteGeneratedLedgerTerminalPatchAt.canonicalGeneratedEntryAt
    (duplicateTerminalPatchOf entryUnique first second) entry

/-- Stored sibling membership cannot be passed where the fold-selected
terminal token is required. -/
theorem stored_terminal_sibling_is_not_authority
    (_entryUnique : (other : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) → other = entry)
    (_first _second : GeneratedLedgerTerminalRowAt rowSource occurrence entry) :
    True := by
  fail_if_success
    exact (storedSiblingOf _entryUnique _first _second :
      FiniteGeneratedLedgerTerminalPatchAt.CanonicalGeneratedEntryAt
        (duplicateTerminalPatchOf _entryUnique _first _second) entry)
  trivial

theorem canonical_terminal_receipt_aligns_world_fold
    {patch : FiniteGeneratedLedgerTerminalPatchAt rowSource occurrence}
    (selected : patch.CanonicalGeneratedEntryAt entry) :
    selected.row.terminal =
      patch.toLedgerTerminalEvolution.discharge entry :=
  selected.terminal_eq_fold

end Terminal

namespace CausalTarget

theorem canonical_row_is_world_commuting
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : RootVisit root.toRoot}
    {generated : SourceNativeTemporalVisitGeneratedEvolutionAt
      root (.finite visit)}
    {entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (row : generated.GeneratedEntryRowAt entry) :
    row.sourceRow.CommutesWithWorld :=
  row.sourceRow.commutes_with_world

end CausalTarget

#print axioms duplicate_rows_repeat_the_exact_generated_event
#print axioms ignored_rows_fold_to_identity
#print axioms ignored_rows_generate_no_canonical_authority
#print axioms canonical_row_target_and_evolution_align
#print axioms Terminal.stored_terminal_sibling_is_not_authority
#print axioms Terminal.canonical_terminal_receipt_aligns_world_fold
#print axioms CausalTarget.canonical_row_is_world_commuting

end NoFreeWorldSeamRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
