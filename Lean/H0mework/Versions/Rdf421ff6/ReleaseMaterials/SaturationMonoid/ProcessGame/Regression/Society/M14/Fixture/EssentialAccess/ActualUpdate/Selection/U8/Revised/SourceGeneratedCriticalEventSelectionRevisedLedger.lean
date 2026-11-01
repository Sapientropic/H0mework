import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.SourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed
import H0mework.Versions.R2.Foundation.Inquiry.SemanticRevision

/-!
# Revised critical-event selection ledger

The selection U8 coface supplies the new world network.  Its vocabulary
replaces the old `Unit` current with the field-grounded exact-seed unfolding.
The root's own write only retains that current root while recording one more
finite occurrence; a different next seed must come from a later actual action,
not from a stored schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCriticalEventSelectionRevisedLedger

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open M14SourceGeneratedHealthTargetCriticalEventSelectionU8Frontier
open M14SourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent

abbrev RootedFailure :=
  healthTargetRootedSelectionFailureAt 1

def minimalCoface : GeneratedMinimalCofaceAt RootedFailure :=
  healthTargetSelectionCofaceAt 1

abbrev NewN := minimalCoface.worldNetwork

def initialSelectionCurrent : EssentialAccessCriticalSelectionCurrent :=
  sourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed.revisedCurrent

def retainedSelectionNext
    (current : EssentialAccessCriticalSelectionCurrent) :
    EssentialAccessCriticalSelectionCurrent :=
  .occur current.root (AccountedBranches.singleton current)

def revisedVocabulary : ConstructiveRoot.Vocabulary where
  Current := EssentialAccessCriticalSelectionCurrent
  Anchor := NewN.Anchor
  Incidence := NewN.Incidence
  Lineage := NewN.Lineage × Nat
  anchorAt := fun _ => NewN.anchorAt minimalCoface.cofaceSupport
  incidenceAt := fun _ => NewN.incidenceAt minimalCoface.cofaceSupport
  lineageAt := fun current =>
    (NewN.lineageAt minimalCoface.cofaceSupport, current.trace.length)
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => retainedSelectionNext current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev NewV := revisedVocabulary

def revisedEventLaw : SourceNativeEventAlgebra NewN NewV where
  EventAt := fun _ support =>
    match support with
    | .inl _ => PEmpty
    | .inr _ => PUnit
  compile := by
    intro current support event
    cases support with
    | inl _ => exact nomatch event
    | inr direction =>
        cases direction
        exact .nativeWrite PUnit.unit
  AffectedInventoryAt := fun {_} {support} _ =>
    OpenResponsibilityAt NewN support
  affectedInventoryPresentation := by
    intro _current _support _event
    exact ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := Prod.fst
  anchor_commutes := by
    intro _current support event
    cases support with
    | inl _ => exact nomatch event
    | inr direction => cases direction; rfl
  incidence_commutes := by
    intro _current support event
    cases support with
    | inl _ => exact nomatch event
    | inr direction => cases direction; rfl
  lineage_commutes := by
    intro _current support event
    cases support with
    | inl _ => exact nomatch event
    | inr direction => cases direction; rfl

def revisedSource : SourceNativeSource NewN NewV where
  initial := initialSelectionCurrent
  law := revisedEventLaw

def revisedEmitted (current : NewV.Current) :
    revisedSource.toRootSource.actual.OccurrenceAt current :=
  ⟨minimalCoface.cofaceSupport, PUnit.unit⟩

def oldRevisedEntry :
    OpenResponsibilityAt NewN minimalCoface.cofaceSupport :=
  minimalCoface.cofaceLedgerRetract.forward RootedFailure.oldTargetEntry

def newRevisedEntry :
    OpenResponsibilityAt NewN minimalCoface.cofaceSupport :=
  minimalCoface.obstructionEntry

def revisedEntryAtNat : Nat →
    OpenResponsibilityAt NewN minimalCoface.cofaceSupport
  | 0 => oldRevisedEntry
  | _ + 1 => newRevisedEntry

def revisedEntryAt (index : Fin 2) :
    OpenResponsibilityAt NewN minimalCoface.cofaceSupport :=
  revisedEntryAtNat index.val

def oldEntryIndex : Fin 2 := ⟨0, by omega⟩
def newEntryIndex : Fin 2 := ⟨1, by omega⟩

def RevisedExactTransitionAt :
    {current : NewV.Current} →
    (occurrence : revisedSource.toRootSource.actual.OccurrenceAt current) →
    {targetSupport : NewN.Support} →
    OpenResponsibilityAt NewN
      (revisedSource.toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt NewN targetSupport → Type :=
  fun {_current} occurrence {targetSupport} sourceEntry targetEntry =>
    PLift (targetSupport =
      revisedSource.toRootSource.account.supportOf occurrence) ×
    PLift (sourceEntry.claim = targetEntry.claim) ×
    PLift (targetEntry.progressBudget ≤ sourceEntry.progressBudget)

def revisedWriteRowSource : LedgerWriteRowSourceAt revisedSource
    RevisedExactTransitionAt where
  IncidenceOccurrenceAt := fun {_current} occurrence {_targetSupport}
      sourceEntry targetEntry =>
    RevisedExactTransitionAt occurrence sourceEntry targetEntry
  compileEvolution := by
    intro _current occurrence targetSupport sourceEntry targetEntry rowEvent
    rcases occurrence with ⟨support, sourceEvent⟩
    cases support with
    | inl oldSupport => exact nomatch sourceEvent
    | inr direction =>
        cases direction
        cases rowEvent.1.down
        exact .transferred
          (GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ()) rfl
          rowEvent.2.1.down rowEvent.2.2.down
  compileExact := fun event => event

def revisedRows
    {current : NewV.Current}
    (occurrence : revisedSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt revisedWriteRowSource occurrence
      ⟨minimalCoface.cofaceSupport⟩ := by
  rcases occurrence with ⟨support, event⟩
  cases support with
  | inl oldSupport => exact nomatch event
  | inr direction =>
      cases direction
      exact
        { size := 2
          sourceEntryAt := revisedEntryAt
          targetEntryAt := revisedEntryAt
          rowAt := fun _ => revisedWriteRowSource.generate
            ⟨PLift.up rfl, PLift.up rfl, PLift.up (Nat.le_refl _)⟩ }

def revisedResponsibilityIndex : NewN.Responsibility → Fin 2
  | .inl _ => oldEntryIndex
  | .inr _ => newEntryIndex

def revisedEntryIndex
    (entry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport) : Fin 2 :=
  revisedResponsibilityIndex entry.1

theorem revisedEntryAt_index
    (entry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport) :
    revisedEntryAt (revisedEntryIndex entry) = entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      cases oldResponsibility
      cases isOpen
      rfl
  | inr generatedResponsibility =>
      cases generatedResponsibility
      cases isOpen
      rfl

def revisedPatch
    {current : NewV.Current}
    (occurrence : revisedSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt revisedWriteRowSource occurrence
      ⟨minimalCoface.cofaceSupport⟩ := by
  rcases occurrence with ⟨support, event⟩
  cases support with
  | inl oldSupport => exact nomatch event
  | inr direction =>
      cases direction
      exact .identityRemainder
        (revisedRows ⟨minimalCoface.cofaceSupport, event⟩)
        { destinationIndex := fun entry =>
            some ⟨revisedEntryIndex entry, revisedEntryAt_index entry⟩
          originIndex := fun entry =>
            some ⟨revisedEntryIndex entry, revisedEntryAt_index entry⟩ }

def revisedLedgerCompiler : SourceNativeLedgerCompiler revisedSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := RevisedExactTransitionAt
  exact_incidence := by
    intro _current _occurrence _targetSupport _sourceEntry _targetEntry exact
    cases exact.1.down
    exact PUnit.unit
  exact_lineage := by
    intro _current _occurrence _targetSupport _sourceEntry _targetEntry exact
    cases exact.1.down
    rfl
  writeRowSource := revisedWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty revisedSource
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support with
    | inl oldSupport => exact nomatch event
    | inr direction =>
        cases direction
        exact .nativeWrite PUnit.unit rfl
          (revisedEmitted (retainedSelectionNext current))
          (revisedPatch ⟨minimalCoface.cofaceSupport, event⟩
            ).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support with
    | inl oldSupport => exact nomatch event
    | inr direction =>
        cases direction
        exact ⟨revisedPatch ⟨minimalCoface.cofaceSupport, event⟩, rfl⟩

def revisedLedgerSource : SourceNativeLedgerSource NewN NewV where
  source := revisedSource
  ledgerCompiler := revisedLedgerCompiler

theorem revisedOpenAt_subsingleton
    (support : NewN.Support) (responsibility : NewN.Responsibility) :
    Subsingleton (NewN.OpenAt support responsibility) := by
  constructor
  intro left right
  cases support with
  | inl oldSupport =>
      cases responsibility with
      | inl oldResponsibility => cases left; cases right; rfl
      | inr generatedResponsibility => exact PEmpty.elim left
  | inr direction =>
      cases responsibility with
      | inl oldResponsibility => cases left; cases right; rfl
      | inr generatedResponsibility => cases left; cases right; rfl

def revisedRestructuringLaw :
    SourceNativeLedgerRestructuringLaw revisedSource :=
  identityOnlyWorldLedgerRestructuringLaw revisedSource
    (NewN.anchorAt minimalCoface.cofaceSupport) revisedOpenAt_subsingleton

theorem revisedPatch_origin_eq
    (current : NewV.Current) (event : PUnit)
    (entry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport) :
    ((revisedPatch (current := current)
      ⟨minimalCoface.cofaceSupport, event⟩).toLedgerWriteEvolution.origin
        entry).1 = entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility => cases oldResponsibility; cases isOpen; rfl
  | inr generatedResponsibility =>
      cases generatedResponsibility; cases isOpen; rfl

theorem revisedPatch_destination_eq
    (current : NewV.Current) (event : PUnit)
    (entry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport) :
    ((revisedPatch (current := current)
      ⟨minimalCoface.cofaceSupport, event⟩).toLedgerWriteEvolution.destination
        entry).1 = entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility => cases oldResponsibility; cases isOpen; rfl
  | inr generatedResponsibility =>
      cases generatedResponsibility; cases isOpen; rfl

def revisedRestructuringCertification
    {current : NewV.Current}
    (occurrence : revisedSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt revisedRestructuringLaw
      (revisedLedgerCompiler.compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases support with
  | inl oldSupport => exact nomatch event
  | inr direction =>
      cases direction
      exact ExactLedgerRestructuringCertificationAt.ofInjective
        (fun left right equality =>
          (revisedPatch_origin_eq current event left).symm.trans
            (equality.trans (revisedPatch_origin_eq current event right)))
        (fun left right equality =>
          (revisedPatch_destination_eq current event left).symm.trans
            (equality.trans
              (revisedPatch_destination_eq current event right)))

def revisedRestructuringCompiler :
    SourceNativeRestructuringLedgerCompiler revisedSource where
  ledgerCompiler := revisedLedgerCompiler
  restructuringLaw := revisedRestructuringLaw
  certifyRestructuring := revisedRestructuringCertification

def revisedRestructuringSource :
    SourceNativeRestructuringLedgerSource NewN NewV where
  source := revisedSource
  compiler := revisedRestructuringCompiler

end
end M14SourceGeneratedCriticalEventSelectionRevisedLedger
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedLedger.revisedLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedLedger.revisedRestructuringSource
