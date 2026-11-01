import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.Revised.SourceGeneratedCriticalEventSelectionRevisedLedger

/-!
# Polymorphic rooted-accounted-unfolding append ledger

This is the sole mechanical append ledger.  For an arbitrary atom type, the
first whole write creates `occur nextAtom (singleton prior)` and every later
write retains the current occurrence.  It reuses the existing revised coface,
two identity rows and identity restructuring; it owns no domain carrier,
selector, root, runtime or registry.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedRootedAccountedUnfoldingAppendLedger

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M14SourceGeneratedCriticalEventSelectionRevisedLedger

local instance {Atom : Type} :
    DecidableEq (RootedAccountedUnfolding Atom) :=
  Classical.decEq _

abbrev rootedAppendedCurrent {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    RootedAccountedUnfolding Atom :=
  .occur nextAtom (AccountedBranches.singleton prior)

def rootedRetainedCurrent {Atom : Type}
    (current : RootedAccountedUnfolding Atom) :
    RootedAccountedUnfolding Atom :=
  .occur current.root (AccountedBranches.singleton current)

def rootedAppendNativeTarget {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom)
    (current : RootedAccountedUnfolding Atom) :
    RootedAccountedUnfolding Atom :=
  if current = prior then rootedAppendedCurrent prior nextAtom
  else rootedRetainedCurrent current

theorem rootedAppendedCurrent_ne_prior {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    rootedAppendedCurrent prior nextAtom ≠ prior := by
  intro equality
  have lengths := congrArg (fun occurrence => occurrence.trace.length) equality
  unfold rootedAppendedCurrent RootedAccountedUnfolding.trace
    AccountedBranches.singleton at lengths
  simp only [List.append_nil, List.length_cons] at lengths
  omega

@[simp] theorem rootedAppendNativeTarget_initial {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    rootedAppendNativeTarget prior nextAtom prior =
      rootedAppendedCurrent prior nextAtom := by
  simp [rootedAppendNativeTarget]

@[simp] theorem rootedAppendNativeTarget_after_append {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    rootedAppendNativeTarget prior nextAtom
        (rootedAppendedCurrent prior nextAtom) =
      rootedRetainedCurrent (rootedAppendedCurrent prior nextAtom) := by
  simp [rootedAppendNativeTarget,
    rootedAppendedCurrent_ne_prior prior nextAtom]

def rootedAppendVocabulary {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    ConstructiveRoot.Vocabulary where
  Current := RootedAccountedUnfolding Atom
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
  nativeTarget := fun {current} _ =>
    rootedAppendNativeTarget prior nextAtom current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev RootedAppendVAt {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :=
  rootedAppendVocabulary prior nextAtom

def rootedAppendEventLaw {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    SourceNativeEventAlgebra NewN (RootedAppendVAt prior nextAtom) where
  EventAt := fun _ support =>
    match support with
    | .inl _ => PEmpty
    | .inr _ => PUnit
  compile := by
    intro current support event
    cases support with
    | inl _ => exact nomatch event
    | inr direction => cases direction; exact .nativeWrite PUnit.unit
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt NewN support
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

def rootedAppendSource {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    SourceNativeSource NewN (RootedAppendVAt prior nextAtom) where
  initial := prior
  law := rootedAppendEventLaw prior nextAtom

def rootedAppendEmitted {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom)
    (current : (RootedAppendVAt prior nextAtom).Current) :
    (rootedAppendSource prior nextAtom).toRootSource.actual.OccurrenceAt current :=
  ⟨minimalCoface.cofaceSupport, PUnit.unit⟩

def RootedAppendExactTransitionAt {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    {current : (RootedAppendVAt prior nextAtom).Current} →
    (occurrence : (rootedAppendSource prior nextAtom).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : NewN.Support} →
    OpenResponsibilityAt NewN
      ((rootedAppendSource prior nextAtom).toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt NewN targetSupport → Type :=
  fun {_current} occurrence {targetSupport} sourceEntry targetEntry =>
    PLift (targetSupport =
      (rootedAppendSource prior nextAtom).toRootSource.account.supportOf occurrence) ×
    PLift (sourceEntry.claim = targetEntry.claim) ×
    PLift (targetEntry.progressBudget ≤ sourceEntry.progressBudget)

def rootedAppendWriteRowSource {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    LedgerWriteRowSourceAt (rootedAppendSource prior nextAtom)
      (RootedAppendExactTransitionAt prior nextAtom) where
  IncidenceOccurrenceAt := fun {_current} occurrence {_targetSupport}
      sourceEntry targetEntry =>
    RootedAppendExactTransitionAt prior nextAtom occurrence sourceEntry targetEntry
  compileEvolution := by
    intro _current occurrence targetSupport sourceEntry targetEntry rowEvent
    rcases occurrence with ⟨support, sourceEvent⟩
    cases support with
    | inl _ => exact nomatch sourceEvent
    | inr direction =>
        cases direction
        cases rowEvent.1.down
        exact .transferred
          (GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ()) rfl
          rowEvent.2.1.down rowEvent.2.2.down
  compileExact := fun event => event

def rootedAppendRows {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom)
    {current : (RootedAppendVAt prior nextAtom).Current}
    (occurrence :
      (rootedAppendSource prior nextAtom).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt
      (rootedAppendWriteRowSource prior nextAtom) occurrence
      ⟨minimalCoface.cofaceSupport⟩ := by
  rcases occurrence with ⟨support, event⟩
  cases support with
  | inl _ => exact nomatch event
  | inr direction =>
      cases direction
      exact
        { size := 2
          sourceEntryAt := revisedEntryAt
          targetEntryAt := revisedEntryAt
          rowAt := fun _ =>
            (rootedAppendWriteRowSource prior nextAtom).generate
              ⟨PLift.up rfl, PLift.up rfl, PLift.up (Nat.le_refl _)⟩ }

def rootedAppendPatch {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom)
    {current : (RootedAppendVAt prior nextAtom).Current}
    (occurrence :
      (rootedAppendSource prior nextAtom).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt
      (rootedAppendWriteRowSource prior nextAtom) occurrence
      ⟨minimalCoface.cofaceSupport⟩ := by
  rcases occurrence with ⟨support, event⟩
  cases support with
  | inl _ => exact nomatch event
  | inr direction =>
      cases direction
      exact .identityRemainder
        (rootedAppendRows prior nextAtom
          ⟨minimalCoface.cofaceSupport, event⟩)
        { destinationIndex := fun entry =>
            some ⟨revisedEntryIndex entry, revisedEntryAt_index entry⟩
          originIndex := fun entry =>
            some ⟨revisedEntryIndex entry, revisedEntryAt_index entry⟩ }

def rootedAppendLedgerCompiler {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    SourceNativeLedgerCompiler (rootedAppendSource prior nextAtom) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := RootedAppendExactTransitionAt prior nextAtom
  exact_incidence := by
    intro _current _occurrence _targetSupport _sourceEntry _targetEntry exact
    cases exact.1.down
    exact PUnit.unit
  exact_lineage := by
    intro _current _occurrence _targetSupport _sourceEntry _targetEntry exact
    cases exact.1.down
    rfl
  writeRowSource := rootedAppendWriteRowSource prior nextAtom
  terminalRowSource := LedgerTerminalRowSourceAt.empty
    (rootedAppendSource prior nextAtom)
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support with
    | inl _ => exact nomatch event
    | inr direction =>
        cases direction
        exact .nativeWrite PUnit.unit rfl
          (rootedAppendEmitted prior nextAtom
            (rootedAppendNativeTarget prior nextAtom current))
          (rootedAppendPatch prior nextAtom
            ⟨minimalCoface.cofaceSupport, event⟩).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support with
    | inl _ => exact nomatch event
    | inr direction =>
        cases direction
        exact ⟨rootedAppendPatch prior nextAtom
          ⟨minimalCoface.cofaceSupport, event⟩, rfl⟩

def rootedAppendRestructuringLaw {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    SourceNativeLedgerRestructuringLaw (rootedAppendSource prior nextAtom) :=
  identityOnlyWorldLedgerRestructuringLaw (rootedAppendSource prior nextAtom)
    (NewN.anchorAt minimalCoface.cofaceSupport) revisedOpenAt_subsingleton

theorem rootedAppendPatch_origin_eq {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom)
    (current : (RootedAppendVAt prior nextAtom).Current) (event : PUnit)
    (entry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport) :
    ((rootedAppendPatch prior nextAtom (current := current)
      ⟨minimalCoface.cofaceSupport, event⟩).toLedgerWriteEvolution.origin
        entry).1 = entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl old => cases old; cases isOpen; rfl
  | inr generated => cases generated; cases isOpen; rfl

theorem rootedAppendPatch_destination_eq {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom)
    (current : (RootedAppendVAt prior nextAtom).Current) (event : PUnit)
    (entry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport) :
    ((rootedAppendPatch prior nextAtom (current := current)
      ⟨minimalCoface.cofaceSupport, event⟩).toLedgerWriteEvolution.destination
        entry).1 = entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl old => cases old; cases isOpen; rfl
  | inr generated => cases generated; cases isOpen; rfl

def rootedAppendRestructuringCompiler {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    SourceNativeRestructuringLedgerCompiler
      (rootedAppendSource prior nextAtom) where
  ledgerCompiler := rootedAppendLedgerCompiler prior nextAtom
  restructuringLaw := rootedAppendRestructuringLaw prior nextAtom
  certifyRestructuring := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support with
    | inl _ => exact nomatch event
    | inr direction =>
        cases direction
        exact ExactLedgerRestructuringCertificationAt.ofInjective
          (fun left right equality =>
            (rootedAppendPatch_origin_eq prior nextAtom current event left).symm.trans
              (equality.trans
                (rootedAppendPatch_origin_eq prior nextAtom current event right)))
          (fun left right equality =>
            (rootedAppendPatch_destination_eq prior nextAtom current event left).symm.trans
              (equality.trans
                (rootedAppendPatch_destination_eq prior nextAtom current event right)))

def rootedAppendRestructuringSource {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    SourceNativeRestructuringLedgerSource NewN
      (RootedAppendVAt prior nextAtom) where
  source := rootedAppendSource prior nextAtom
  compiler := rootedAppendRestructuringCompiler prior nextAtom

def rootedAppendFirstSuccessor {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    SourceNativeLedgerGeneratedSuccessorAt
      (rootedAppendEmitted prior nextAtom prior)
      ((rootedAppendLedgerCompiler prior nextAtom).compile
        (rootedAppendEmitted prior nextAtom prior)) :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((rootedAppendLedgerCompiler prior nextAtom).compile
      (rootedAppendEmitted prior nextAtom prior))).get (by rfl)

@[simp] theorem rootedAppendFirstSuccessor_target_exact {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    (rootedAppendFirstSuccessor prior nextAtom).targetCurrent =
      rootedAppendedCurrent prior nextAtom :=
  rootedAppendNativeTarget_initial prior nextAtom

theorem rootedAppendLedger_directConsumer {Atom : Type}
    (prior : RootedAccountedUnfolding Atom) (nextAtom : Atom) :
    (rootedAppendSource prior nextAtom).initial = prior ∧
      (rootedAppendFirstSuccessor prior nextAtom).targetCurrent =
        rootedAppendedCurrent prior nextAtom ∧
      (rootedAppendedCurrent prior nextAtom).root = nextAtom ∧
      (rootedAppendRows prior nextAtom
        (rootedAppendEmitted prior nextAtom prior)).size = 2 ∧
      rootedAppendNativeTarget prior nextAtom
          (rootedAppendedCurrent prior nextAtom) =
        rootedRetainedCurrent (rootedAppendedCurrent prior nextAtom) :=
  ⟨rfl, rootedAppendFirstSuccessor_target_exact prior nextAtom, rfl, rfl,
    rootedAppendNativeTarget_after_append prior nextAtom⟩

end
end M14SourceGeneratedRootedAccountedUnfoldingAppendLedger
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRootedAccountedUnfoldingAppendLedger.rootedAppendLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRootedAccountedUnfoldingAppendLedger.rootedAppendRestructuringSource
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRootedAccountedUnfoldingAppendLedger.rootedAppendLedger_directConsumer
