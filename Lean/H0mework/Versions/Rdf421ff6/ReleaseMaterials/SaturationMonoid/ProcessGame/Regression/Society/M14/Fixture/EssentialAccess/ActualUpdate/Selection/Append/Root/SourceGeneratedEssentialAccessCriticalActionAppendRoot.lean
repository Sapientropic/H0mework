import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Root.SourceGeneratedEssentialAccessCriticalActionAppendSelection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.Revised.Inquiry.SourceGeneratedCriticalEventSelectionRevisedInquiry
/-!
# Source-generated critical-action append root
The append root installs selection only at the carrier-generated current, adds
the inquiry/answer/consumer faces needed by a later actual-action runtime, and
transports every predecessor projection outcome at its exact occurrence.
The prior and first retained successor remain inactive; no sibling root,
ledger, registry, schedule or completed future is introduced.
-/
set_option autoImplicit false
namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
noncomputable section
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal
open ConstructiveRoot.RootInquiryCompletion
open M14SourceEssentialAccessCriticalRenewal
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendSelection
abbrev appendTheory := revisedInquiryTheory
inductive AppendLocalProjection
  | ledger
  | inquiry
  | answer
  | consumer
  | selection
abbrev AppendProjection (InheritedProjection : Type) :=
  AppendLocalProjection ⊕ InheritedProjection
namespace AppendProjection
def ledger {InheritedProjection : Type} : AppendProjection InheritedProjection :=
  .inl .ledger
def inquiry {InheritedProjection : Type} : AppendProjection InheritedProjection :=
  .inl .inquiry
def answer {InheritedProjection : Type} : AppendProjection InheritedProjection :=
  .inl .answer
def consumer {InheritedProjection : Type} : AppendProjection InheritedProjection :=
  .inl .consumer
def selection {InheritedProjection : Type} : AppendProjection InheritedProjection :=
  .inl .selection
def inherited {InheritedProjection : Type} (projection : InheritedProjection) :
    AppendProjection InheritedProjection := .inr projection
end AppendProjection
def appendProjectionLaw
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    SourceNativeProjectionLaw
      (appendRestructuringSource prior actionCarrier).toLedgerSource where
  Projection := AppendProjection
    sourceRoot.toAuthoritativeRoot.source.projectionLaw.Projection
  ActiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl .ledger => PUnit
    | .inl .inquiry => PUnit
    | .inl .answer => PUnit
    | .inl .consumer => PUnit
    | .inl .selection =>
        (appendCriticalRenewalRootShell prior actionCarrier).ActiveAt occurrence
    | .inr oldProjection =>
        sourceRoot.toAuthoritativeRoot.source.projectionLaw.ActiveAt
          oldProjection sourceOccurrence
  InactiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl .ledger => PEmpty
    | .inl .inquiry => PEmpty
    | .inl .answer => PEmpty
    | .inl .consumer => PEmpty
    | .inl .selection =>
        (appendCriticalRenewalRootShell prior actionCarrier).InactiveAt occurrence
    | .inr oldProjection =>
        sourceRoot.toAuthoritativeRoot.source.projectionLaw.InactiveAt
          oldProjection sourceOccurrence
  classify := fun projection {_current} occurrence =>
    match projection with
    | .inl .ledger => .inl PUnit.unit
    | .inl .inquiry => .inl PUnit.unit
    | .inl .answer => .inl PUnit.unit
    | .inl .consumer => .inl PUnit.unit
    | .inl .selection =>
        (appendCriticalRenewalRootShell prior actionCarrier).classify occurrence
    | .inr oldProjection =>
        sourceRoot.toAuthoritativeRoot.source.projectionLaw.classify
          oldProjection sourceOccurrence
  PayloadAt := fun projection {current} occurrence active =>
    match projection with
    | .inl .ledger => SourceNativeLedgerEvolutionAt
        (appendSource prior actionCarrier) occurrence
    | .inl .inquiry => SourceNativeInquiryCompilationTokenAt
        (revisedInquiryEntryAt current) () (ULift.up.{1, 0} occurrence)
          (revisedInquiryAuditAt current) PUnit
    | .inl .answer => PUnit
    | .inl .consumer => SourceNativeInquiryAnswerConsumerTokenAt
        () (ULift.up.{1, 0} occurrence) (revisedInquiryEntryAt current)
          PUnit.unit
    | .inl .selection => SourceGeneratedInstalledCriticalRenewalAt
        prior actionCarrier (current := current) occurrence active
    | .inr oldProjection =>
        sourceRoot.toAuthoritativeRoot.source.projectionLaw.PayloadAt
          oldProjection sourceOccurrence active
  project := fun projection {_current} occurrence active =>
    match projection with
    | .inl .ledger => (appendLedgerCompiler prior actionCarrier).compile occurrence
    | .inl .inquiry => .canonical PUnit.unit
    | .inl .answer => PUnit.unit
    | .inl .consumer => .canonical
    | .inl .selection => sourceGeneratedInstalledCriticalRenewalAt
        prior actionCarrier occurrence active
    | .inr oldProjection =>
        sourceRoot.toAuthoritativeRoot.source.projectionLaw.project
          oldProjection sourceOccurrence active
theorem appendInheritedProjection_outcome_exact
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
    (projection : sourceRoot.toAuthoritativeRoot.source.projectionLaw.Projection)
    {current : (AppendVAt prior actionCarrier).Current}
    (occurrence :
      (appendSource prior actionCarrier).toRootSource.actual.OccurrenceAt current) :
    HEq ((appendProjectionLaw sourceRoot sourceOccurrence prior actionCarrier
      ).outcomeAt (.inherited projection) occurrence)
      (sourceRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        projection sourceOccurrence) := by
  unfold SourceNativeProjectionLaw.outcomeAt
  dsimp only [appendProjectionLaw, AppendProjection.inherited]
  generalize classifier_eq :
    sourceRoot.toAuthoritativeRoot.source.projectionLaw.classify
      projection sourceOccurrence = classified
  cases classified <;> exact HEq.rfl
def appendAuthoritySource
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    SourceNativeAuthoritySource NewN (AppendVAt prior actionCarrier) where
  restructuringSource := appendRestructuringSource prior actionCarrier
  eventInventoryAdmission := .reflOfNoFaithfulTerminal
    (appendRestructuringSource prior actionCarrier)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := appendTheory
  projectionLaw := appendProjectionLaw sourceRoot sourceOccurrence
    prior actionCarrier
def appendLivingRoot
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    SourceNativeLivingRootClosure NewN (AppendVAt prior actionCarrier) where
  source :=
    { base := appendAuthoritySource sourceRoot sourceOccurrence prior actionCarrier
      terminalHandoff := (appendAuthoritySource sourceRoot sourceOccurrence
        prior actionCarrier
        ).emptyFaithfulTerminalHandoff
          (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := appendEmitted prior actionCarrier
  compiler_commutes := fun _ => rfl
def installedAppendedInquiry
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  (appendProjectionLaw sourceRoot sourceOccurrence prior actionCarrier).project
    .inquiry (appendEmitted prior actionCarrier
      (appendedCriticalSelectionCurrent prior actionCarrier)) PUnit.unit
def installedAppendedAnswer
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  (appendProjectionLaw sourceRoot sourceOccurrence prior actionCarrier).project
    .answer (appendEmitted prior actionCarrier
      (appendedCriticalSelectionCurrent prior actionCarrier)) PUnit.unit
def installedAppendedConsumer
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  (appendProjectionLaw sourceRoot sourceOccurrence prior actionCarrier).project
    .consumer (appendEmitted prior actionCarrier
      (appendedCriticalSelectionCurrent prior actionCarrier)) PUnit.unit
theorem installedAppendedInquiryFaces_exact
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    installedAppendedInquiry sourceRoot sourceOccurrence prior actionCarrier =
        SourceNativeInquiryCompilationTokenAt.canonical PUnit.unit ∧
      installedAppendedAnswer sourceRoot sourceOccurrence prior actionCarrier =
        PUnit.unit ∧
      installedAppendedConsumer sourceRoot sourceOccurrence prior actionCarrier =
        SourceNativeInquiryAnswerConsumerTokenAt.canonical :=
  ⟨rfl, rfl, rfl⟩
def installedAppendedCriticalRenewal
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  (appendProjectionLaw sourceRoot sourceOccurrence prior actionCarrier).project
    .selection
    (appendEmitted prior actionCarrier
      (appendedCriticalSelectionCurrent prior actionCarrier)) ⟨rfl⟩
theorem priorSelectionActivation_isEmpty
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    IsEmpty ((appendProjectionLaw sourceRoot sourceOccurrence prior actionCarrier
      ).ActiveAt .selection (appendEmitted prior actionCarrier prior)) :=
  ⟨fun active => appendedCriticalSelectionCurrent_ne_prior prior actionCarrier
    active.down.symm⟩
theorem retainedSelectionNext_ne
    (current : EssentialAccessCriticalSelectionCurrent) :
    retainedSelectionNext current ≠ current := by
  intro equality
  have lengthEquality := congrArg
    (fun value => value.trace.length) equality
  unfold retainedSelectionNext RootedAccountedUnfolding.trace
    AccountedBranches.singleton at lengthEquality
  simp only [List.append_nil, List.length_cons] at lengthEquality
  omega
abbrev AppendedSelectionReplayAt
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :=
  (appendProjectionLaw sourceRoot sourceOccurrence prior actionCarrier).ActiveAt
    .selection
    (appendEmitted prior actionCarrier
      (retainedSelectionNext
        (appendedCriticalSelectionCurrent prior actionCarrier)))
theorem appendedSelectionReplay_isEmpty
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    IsEmpty (AppendedSelectionReplayAt sourceRoot sourceOccurrence
      prior actionCarrier) :=
  ⟨fun replay => retainedSelectionNext_ne
    (appendedCriticalSelectionCurrent prior actionCarrier) replay.down⟩
theorem appendRoot_directConsumer
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceCurrent)
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    (appendLivingRoot sourceRoot sourceOccurrence prior actionCarrier
      ).toAuthoritativeRoot.toRoot.source.initial =
        prior ∧
      (appendFirstSuccessor prior actionCarrier).targetCurrent =
        appendedCriticalSelectionCurrent prior actionCarrier ∧
      (installedAppendedCriticalRenewal sourceRoot sourceOccurrence
        prior actionCarrier).selected.selectedEvent =
        actionCarrier.event ∧
      (installedAppendedCriticalRenewal sourceRoot sourceOccurrence
        prior actionCarrier).payload.consumer.action =
        actionCarrier.action ∧
      (installedAppendedCriticalRenewal sourceRoot sourceOccurrence
        prior actionCarrier).payload.disposition.update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt actionCarrier.event ∧
      (installedAppendedCriticalRenewal sourceRoot sourceOccurrence
        prior actionCarrier).payload.successor.targetCurrent =
        retainedSelectionNext
          (appendedCriticalSelectionCurrent prior actionCarrier) ∧
      IsEmpty (AppendedSelectionReplayAt sourceRoot sourceOccurrence
        prior actionCarrier) := by
  refine ⟨rfl, appendFirstSuccessor_target_exact prior actionCarrier,
    (installedAppendedCriticalRenewal sourceRoot sourceOccurrence
      prior actionCarrier).selectedEventExact,
    ?_, rfl, ?_, appendedSelectionReplay_isEmpty sourceRoot sourceOccurrence
      prior actionCarrier⟩
  · rw [(installedAppendedCriticalRenewal sourceRoot sourceOccurrence
      prior actionCarrier).payloadExact]
    exact (sourceEssentialAccessCriticalRenewalLaw_directConsumer
      actionCarrier.event (appendCriticalRenewalRootShell prior actionCarrier)
      (appendEmitted prior actionCarrier
        (appendedCriticalSelectionCurrent prior actionCarrier)) ⟨rfl⟩).2.1 |>.trans
        actionCarrier.actionExact.symm
  · change appendNativeTarget prior actionCarrier
      (appendedCriticalSelectionCurrent prior actionCarrier) = _
    exact appendNativeTarget_after_append prior actionCarrier
end
end M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
end Society
end ProcessGame
end SaturationMonoid
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendRoot.appendLivingRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendRoot.appendInheritedProjection_outcome_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendRoot.installedAppendedInquiryFaces_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendRoot.installedAppendedCriticalRenewal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendRoot.appendedSelectionReplay_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendRoot.appendRoot_directConsumer
