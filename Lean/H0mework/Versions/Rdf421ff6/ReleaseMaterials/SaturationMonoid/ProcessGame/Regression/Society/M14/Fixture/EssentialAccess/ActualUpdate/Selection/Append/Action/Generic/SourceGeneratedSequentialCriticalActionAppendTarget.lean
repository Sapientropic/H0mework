import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Root.SourceGeneratedEssentialAccessCriticalActionAppendRoot
/-!
# Carrier-native sequential critical-action append target
This is the unique append-root-to-append-root assembler.  A base root,
occurrence and already source-generated carrier definitionally generate the
exact source root.  Its live visit/entry authority and the next dependent
action carrier generate the target root, receipt core and first whole-ledger
successor.  Domain provenance remains a Prop seal.
-/
set_option autoImplicit false
namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialCriticalActionAppendTarget
noncomputable section
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14EssentialAccessRelationFixture
open M14SourceEssentialAccessCriticalRenewal
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendSelection
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
section
variable {PredecessorV : ConstructiveRoot.Vocabulary}
variable (predecessorRoot : SourceNativeLivingRootClosure NewN PredecessorV)
variable {predecessorCurrent : PredecessorV.Current}
variable (predecessorOccurrence :
  predecessorRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    predecessorCurrent)
variable (sourcePrior : EssentialAccessCriticalSelectionCurrent)
variable (sourceCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
abbrev sequentialCriticalActionAppendSourceRoot :=
  appendLivingRoot predecessorRoot predecessorOccurrence
    sourcePrior sourceCarrier
variable (sourceVisit : SourceNativeTemporalVisitAt
  (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
    sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot)
variable (sourceEntry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport)
variable (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
  (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
    sourcePrior sourceCarrier) sourceVisit sourceEntry)
variable (prior : EssentialAccessCriticalSelectionCurrent)
variable (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
def sequentialCriticalActionAppendTargetRoot
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) :=
  appendLivingRoot
    (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
      sourcePrior sourceCarrier)
    sourceEvent.occurrence prior actionCarrier
def sequentialCriticalActionAppendIdentityTranslation :
    TypedSemanticWorldNetworkTranslationAt NewN NewN where
  support :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  anchor :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  incidence :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  lineage :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  responsibility :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  claim :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ =>
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ proof => proof
  oldDispositionSurvives := fun _ _ proof => proof
def sequentialCriticalActionAppendOccurrencePresentation
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) : ConstructivePresentation
    ((sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
      sourcePrior sourceCarrier).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        sourceVisit.current)
    ((sequentialCriticalActionAppendTargetRoot predecessorRoot predecessorOccurrence
      sourcePrior sourceCarrier sourceVisit prior actionCarrier sourceEvent
      ).toAuthoritativeRoot.toRoot.actual.OccurrenceAt prior) :=
  ConstructivePresentation.refl _
def sequentialCriticalActionAppendTargetInitialVisit
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) : SourceNativeTemporalVisitAt
    (sequentialCriticalActionAppendTargetRoot predecessorRoot predecessorOccurrence
      sourcePrior sourceCarrier sourceVisit prior actionCarrier sourceEvent
      ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (sequentialCriticalActionAppendTargetRoot predecessorRoot predecessorOccurrence
    sourcePrior sourceCarrier sourceVisit prior actionCarrier sourceEvent
    ).toAuthoritativeRoot.toRoot.initialVisit
def sequentialCriticalActionAppendTargetInitialGenerated
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) :=
  (sequentialCriticalActionAppendTargetRoot predecessorRoot predecessorOccurrence
    sourcePrior sourceCarrier sourceVisit prior actionCarrier sourceEvent
    ).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (sequentialCriticalActionAppendTargetInitialVisit predecessorRoot
        predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
        actionCarrier sourceEvent)
def sequentialCriticalActionAppendTargetNewEntryRow
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit)
    (entry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport) :
    (sequentialCriticalActionAppendTargetInitialGenerated predecessorRoot
      predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
      actionCarrier sourceEvent).GeneratedEntryRowAt entry :=
  ((sequentialCriticalActionAppendTargetInitialGenerated predecessorRoot
    predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
    actionCarrier sourceEvent).canonicalGeneratedEntryRow? entry).get
      (by rfl)
def sequentialCriticalActionAppendTargetFirstSuccessor
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) : SourceNativeLedgerGeneratedSuccessorAt
    (sequentialCriticalActionAppendTargetInitialGenerated predecessorRoot
      predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
      actionCarrier sourceEvent).occurrence
    (sequentialCriticalActionAppendTargetInitialGenerated predecessorRoot
      predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
      actionCarrier sourceEvent).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    (sequentialCriticalActionAppendTargetInitialGenerated predecessorRoot
      predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
      actionCarrier sourceEvent).wholeLedgerWriteBack).get (by rfl)
structure SequentialCriticalActionAppendReceiptCoreAt
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) : Prop where
  priorFromSource : prior = sourceVisit.current
  sourceEntryExact : sourceEntry = newRevisedEntry
  actionSeedExact : actionCarrier.action.criticalBearer.bearerLineage.seed =
    exactEssentialAccessSeed actionCarrier.event
  occurrenceCommutes :
    (sequentialCriticalActionAppendOccurrencePresentation predecessorRoot
      predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
      actionCarrier sourceEvent).forward sourceEvent.occurrence =
      (sequentialCriticalActionAppendTargetRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier sourceVisit prior actionCarrier sourceEvent
        ).emitted prior
  targetAppendCurrent :
    (sequentialCriticalActionAppendTargetFirstSuccessor predecessorRoot
      predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
      actionCarrier sourceEvent).targetCurrent =
      appendedCriticalSelectionCurrent prior actionCarrier
  selectedRenewal :
    let installed := installedAppendedCriticalRenewal
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier) sourceEvent.occurrence prior actionCarrier
    installed.selected.selectedEvent = actionCarrier.event ∧
      installed.payload.consumer.action = actionCarrier.action ∧
      installed.payload.disposition.update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt actionCarrier.event
  selectedRetainedSuccessor :
    let installed := installedAppendedCriticalRenewal
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier) sourceEvent.occurrence prior actionCarrier
    installed.payload.successor.targetCurrent =
      retainedSelectionNext (appendedCriticalSelectionCurrent prior actionCarrier)
  selectionReplay : IsEmpty (AppendedSelectionReplayAt
    (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
      sourcePrior sourceCarrier) sourceEvent.occurrence prior actionCarrier)
  inheritedOutcomes : ∀ projection :
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.source.projectionLaw.Projection,
    HEq ((appendProjectionLaw
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier) sourceEvent.occurrence prior actionCarrier
      ).outcomeAt (.inherited projection)
        (appendEmitted prior actionCarrier prior))
      ((sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.source.projectionLaw.outcomeAt
          projection sourceEvent.occurrence)
  firstWholeSuccessor : Nonempty (SourceNativeLedgerGeneratedSuccessorAt
    (sequentialCriticalActionAppendTargetInitialGenerated predecessorRoot
      predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
      actionCarrier sourceEvent).occurrence
    (sequentialCriticalActionAppendTargetInitialGenerated predecessorRoot
      predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
      actionCarrier sourceEvent).wholeLedgerWriteBack)
theorem sequentialCriticalActionAppendReceiptCoreAt
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit)
    (priorFromSource : prior = sourceVisit.current)
    (sourceEntryExact : sourceEntry = newRevisedEntry) :
    SequentialCriticalActionAppendReceiptCoreAt predecessorRoot predecessorOccurrence
      sourcePrior sourceCarrier sourceVisit sourceEntry prior actionCarrier
      sourceEvent := by
  let installed := installedAppendedCriticalRenewal
    (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
      sourcePrior sourceCarrier) sourceEvent.occurrence prior actionCarrier
  exact
    { priorFromSource := priorFromSource
      sourceEntryExact := sourceEntryExact
      actionSeedExact := (criticalActionCarrier_directConsumer actionCarrier).1
      occurrenceCommutes := rfl
      targetAppendCurrent := by
        change appendNativeTarget prior actionCarrier prior = _
        exact appendNativeTarget_initial prior actionCarrier
      selectedRenewal := by
        refine ⟨installed.selectedEventExact, ?_, rfl⟩
        rw [installed.payloadExact]
        exact (sourceEssentialAccessCriticalRenewalLaw_directConsumer
          actionCarrier.event (appendCriticalRenewalRootShell prior actionCarrier)
          (appendEmitted prior actionCarrier
            (appendedCriticalSelectionCurrent prior actionCarrier)) ⟨rfl⟩).2.1
          |>.trans actionCarrier.actionExact.symm
      selectedRetainedSuccessor := by
        change appendNativeTarget prior actionCarrier
          (appendedCriticalSelectionCurrent prior actionCarrier) = _
        exact appendNativeTarget_after_append prior actionCarrier
      selectionReplay := appendedSelectionReplay_isEmpty
        (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
          sourcePrior sourceCarrier) sourceEvent.occurrence prior actionCarrier
      inheritedOutcomes := fun projection =>
        appendInheritedProjection_outcome_exact
          (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
            sourcePrior sourceCarrier) sourceEvent.occurrence prior actionCarrier
          projection (appendEmitted prior actionCarrier prior)
      firstWholeSuccessor := ⟨sequentialCriticalActionAppendTargetFirstSuccessor
        predecessorRoot predecessorOccurrence sourcePrior sourceCarrier
        sourceVisit prior actionCarrier sourceEvent⟩ }
def ExactSequentialCriticalActionAppendReceiptAt
    (SourceSealAt : (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) → Prop)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) (_answer : PUnit) : Type 3 :=
  ULift.{3, 0} (PLift (SourceSealAt sourceEvent ∧
    SequentialCriticalActionAppendReceiptCoreAt predecessorRoot predecessorOccurrence
      sourcePrior sourceCarrier sourceVisit sourceEntry prior actionCarrier
      sourceEvent))
def sequentialCriticalActionAppendTargetAt
    (priorFromSource : prior = sourceVisit.current)
    (sourceEntryExact : sourceEntry = newRevisedEntry)
    (SourceSealAt : (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) → Prop)
    (sourceSeal : ∀ sourceEvent, SourceSealAt sourceEvent)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceCarrier).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) : SourceNativeSequentialActualActionTargetAt
    (sequentialCriticalActionAppendSourceRoot predecessorRoot predecessorOccurrence
      sourcePrior sourceCarrier) sourceVisit sourceEvent sourceEntry
      sourceAuthority :=
    { TargetN := NewN
      translation := sequentialCriticalActionAppendIdentityTranslation
      TargetV := AppendVAt prior actionCarrier
      targetRoot := sequentialCriticalActionAppendTargetRoot predecessorRoot
        predecessorOccurrence sourcePrior sourceCarrier sourceVisit prior
        actionCarrier sourceEvent
      targetTheory := revisedInquiryTheory
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic :=
        { compile := id
          commuting := fun _ => rfl }
      occurrencePresentation := sequentialCriticalActionAppendOccurrencePresentation
        predecessorRoot predecessorOccurrence sourcePrior sourceCarrier
        sourceVisit prior actionCarrier sourceEvent
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := sequentialCriticalActionAppendIdentityTranslation.oldOpenLedger
        minimalCoface.cofaceSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := fun targetEntry => ⟨⟨targetEntry, PLift.up rfl⟩⟩
      translatedSourceEntryRow := sequentialCriticalActionAppendTargetNewEntryRow
        predecessorRoot predecessorOccurrence sourcePrior sourceCarrier
        sourceVisit prior actionCarrier sourceEvent sourceEntry
      firstSuccessor := sequentialCriticalActionAppendTargetFirstSuccessor
        predecessorRoot predecessorOccurrence sourcePrior sourceCarrier
        sourceVisit prior actionCarrier sourceEvent
      canonical_targetNextVisit_eq := rfl
      Answer := PUnit
      answer := PUnit.unit
      Receipt := ExactSequentialCriticalActionAppendReceiptAt predecessorRoot
        predecessorOccurrence sourcePrior sourceCarrier sourceVisit
        sourceEntry prior actionCarrier SourceSealAt sourceEvent
      receipt := ULift.up (PLift.up
        ⟨sourceSeal sourceEvent,
          sequentialCriticalActionAppendReceiptCoreAt predecessorRoot
            predecessorOccurrence sourcePrior sourceCarrier sourceVisit
            sourceEntry prior actionCarrier sourceEvent priorFromSource
              sourceEntryExact⟩) }
end
end
end M14SourceGeneratedSequentialCriticalActionAppendTarget
end Society
end ProcessGame
end SaturationMonoid
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialCriticalActionAppendTarget.sequentialCriticalActionAppendReceiptCoreAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialCriticalActionAppendTarget.sequentialCriticalActionAppendTargetAt
