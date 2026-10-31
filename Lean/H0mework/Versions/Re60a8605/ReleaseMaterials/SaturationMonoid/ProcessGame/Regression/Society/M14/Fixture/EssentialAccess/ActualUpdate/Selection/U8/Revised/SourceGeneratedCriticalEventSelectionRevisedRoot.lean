import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.Revised.Inquiry.SourceGeneratedCriticalEventSelectionRevisedInquiry

/-!
# U8-revised critical-event selection root

The generated minimal coface is realized by one living root whose current is
the receipt-grounded exact-seed unfolding.  Selection is an installed
projection of that root occurrence.  The first whole-ledger write preserves
the current root and records one finite predecessor; no later event seed or
completed future is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCriticalEventSelectionRevisedRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open M14SourceEssentialAccessCriticalRenewal
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedHealthCessationTargetRoot
open M14SourceGeneratedHealthCessationTargetHistory
open M14SourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry

def revisedTheory : TheoryState NewN :=
  revisedInquiryTheory

abbrev OldHealthTargetProjection :=
  healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.Projection

def oldHealthTargetSelectionOccurrence :=
  healthCessationTargetRoot.emitted
    (healthCessationTargetTemporalVisitAt 1).current

/-- The revised event algebra has exactly one emitted occurrence at every
current.  This theorem removes the ambient occurrence presentation before a
renewal payload is installed; it does not identify distinct currents. -/
theorem revisedOccurrence_eq_emitted
    {current : NewV.Current}
    (occurrence : revisedSource.toRootSource.actual.OccurrenceAt current) :
    occurrence = revisedEmitted current := by
  rcases occurrence with ⟨support, event⟩
  cases support with
  | inl oldSupport => exact nomatch event
  | inr direction => cases direction; cases event; rfl

/-- The initial revised occurrence alone may execute the critical renewal.
The root's retained successor remains a living current but carries an explicit
inactive receipt, so a whole-ledger write cannot replay the action for free. -/
def revisedCriticalRenewalRootShell :
    SourceNativeRenewalRootShellAt
      revisedRestructuringSource.toLedgerSource where
  ActiveAt := fun {current} _occurrence =>
    PLift (current = initialSelectionCurrent)
  InactiveAt := fun {current} _occurrence =>
    PLift (current ≠ initialSelectionCurrent)
  classify := by
    intro current occurrence
    by_cases current_eq : current = initialSelectionCurrent
    · exact .inl ⟨current_eq⟩
    · exact .inr ⟨current_eq⟩
  sourceEntry := by
    intro current occurrence active
    cases active.down
    rw [revisedOccurrence_eq_emitted occurrence]
    exact newRevisedEntry
  selectedRow := by
    intro current occurrence active
    cases active.down
    rw [revisedOccurrence_eq_emitted occurrence]
    exact revisedLedgerCompiler.canonicalGeneratedEntry_of_terminalOrTransferred
      (revisedEmitted initialSelectionCurrent) newRevisedEntry (by rfl)
  successor := by
    intro current occurrence active
    cases active.down
    rw [revisedOccurrence_eq_emitted occurrence]
    exact
      (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
        (revisedLedgerCompiler.compile
          (revisedEmitted initialSelectionCurrent))).get (by rfl)
  activeOccurrences_eq := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      leftActive rightActive
    cases leftActive.down
    cases rightActive.down
    rw [revisedOccurrence_eq_emitted leftOccurrence,
      revisedOccurrence_eq_emitted rightOccurrence]

/-- One installed selection coordinate contains both the fold-selected event
and the event-polymorphic renewal payload compiled at the same exact root
occurrence.  Neither the event nor the local action is a caller argument. -/
structure SourceGeneratedInstalledSelectedCriticalRenewalAt
    {current : NewV.Current}
    (occurrence : revisedSource.toRootSource.actual.OccurrenceAt current)
    (active : revisedCriticalRenewalRootShell.ActiveAt occurrence) : Type where
  private mk ::
  selected : SourceGeneratedSelectedEssentialAccessCriticalEventAt current
  selectedExact : selected =
    sourceGeneratedSelectedEssentialAccessCriticalEventAt current
  payload : RootRestrictedRenewalPayloadAt
    revisedRestructuringSource.toLedgerSource occurrence LocalGame
      (EssentialAccessCriticalLocalSeed selected.selectedEvent)
      (EssentialAccessCriticalLocalSeedAt selected.selectedEvent)
      (SourceEssentialAccessCriticalConsumerAt selected.selectedEvent)
      (SourceEssentialAccessCriticalDispositionAt selected.selectedEvent)
  payloadExact : payload =
    (sourceEssentialAccessCriticalRenewalLaw selected.selectedEvent
      revisedCriticalRenewalRootShell).compile occurrence active

def sourceGeneratedInstalledSelectedCriticalRenewalAt
    {current : NewV.Current}
    (occurrence : revisedSource.toRootSource.actual.OccurrenceAt current)
    (active : revisedCriticalRenewalRootShell.ActiveAt occurrence) :
    SourceGeneratedInstalledSelectedCriticalRenewalAt occurrence active :=
  let selected :=
    sourceGeneratedSelectedEssentialAccessCriticalEventAt current
  let law := sourceEssentialAccessCriticalRenewalLaw selected.selectedEvent
    revisedCriticalRenewalRootShell
  { selected := selected
    selectedExact := rfl
    payload := law.compile occurrence active
    payloadExact := rfl }

inductive RevisedProjection
  | ledger
  | inquiry
  | selection
  | inherited (projection : OldHealthTargetProjection)

def revisedProjectionLaw : SourceNativeProjectionLaw
    revisedRestructuringSource.toLedgerSource where
  Projection := RevisedProjection
  ActiveAt := fun projection {_current} occurrence =>
    match projection with
    | .ledger => PUnit
    | .inquiry => PUnit
    | .selection => revisedCriticalRenewalRootShell.ActiveAt occurrence
    | .inherited oldProjection =>
        healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.ActiveAt
          oldProjection oldHealthTargetSelectionOccurrence
  InactiveAt := fun projection {_current} occurrence =>
    match projection with
    | .ledger => PEmpty
    | .inquiry => PEmpty
    | .selection => revisedCriticalRenewalRootShell.InactiveAt occurrence
    | .inherited oldProjection =>
        healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.InactiveAt
          oldProjection oldHealthTargetSelectionOccurrence
  classify := by
    intro projection current occurrence
    cases projection with
    | ledger => exact .inl PUnit.unit
    | inquiry => exact .inl PUnit.unit
    | selection => exact revisedCriticalRenewalRootShell.classify occurrence
    | inherited oldProjection =>
        exact healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.classify
          oldProjection oldHealthTargetSelectionOccurrence
  PayloadAt := fun projection {current} occurrence active =>
    match projection with
    | .ledger => SourceNativeLedgerEvolutionAt revisedSource occurrence
    | .inquiry => SourceNativeInquiryCompilationTokenAt
        (revisedInquiryEntryAt current) () (ULift.up.{1, 0} occurrence)
          (revisedInquiryAuditAt current) PUnit
    | .selection =>
        SourceGeneratedInstalledSelectedCriticalRenewalAt occurrence active
    | .inherited oldProjection =>
        healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.PayloadAt
          oldProjection oldHealthTargetSelectionOccurrence active
  project := fun projection {current} occurrence active => by
    cases projection with
    | ledger => exact revisedLedgerCompiler.compile occurrence
    | inquiry => exact .canonical PUnit.unit
    | selection =>
        exact sourceGeneratedInstalledSelectedCriticalRenewalAt occurrence active
    | inherited oldProjection =>
        exact healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.project
          oldProjection oldHealthTargetSelectionOccurrence active

/-- Every old health-target coordinate is retained as its complete dependent
classifier outcome.  The transport is indexed by the exact old occurrence
presented to the revised initial occurrence; it creates no second source,
ledger or domain payload. -/
theorem revisedInheritedProjection_outcome_exact
    (projection : OldHealthTargetProjection)
    {current : NewV.Current}
    (occurrence : revisedSource.toRootSource.actual.OccurrenceAt current) :
    HEq (revisedProjectionLaw.outcomeAt (.inherited projection) occurrence)
      (healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        projection oldHealthTargetSelectionOccurrence) := by
  unfold SourceNativeProjectionLaw.outcomeAt
  dsimp only [revisedProjectionLaw]
  generalize classifier_eq :
    healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.classify
      projection oldHealthTargetSelectionOccurrence = classified
  cases classified <;> exact HEq.rfl

def revisedInheritedInquiryProjection : RevisedProjection :=
  .inherited M9SourceHealthCessationSuffix.inquiryProjection

def revisedInquiryProjection : RevisedProjection :=
  .inquiry

def revisedInheritedFailureProjection : RevisedProjection :=
  .inherited M9SourceHealthCessationSuffix.failureProjection

def revisedInheritedProofCarryingProjection : RevisedProjection :=
  .inherited M9SourceHealthCessationSuffix.proofCarryingProjection

def revisedInheritedUBIProjection : RevisedProjection :=
  .inherited M9SourceHealthCessationSuffix.ubiProjection

def revisedInheritedRecognitionProjection : RevisedProjection :=
  .inherited M9SourceHealthCessationSuffix.recognitionProjection

def revisedInheritedMandateProjection : RevisedProjection :=
  .inherited M9SourceHealthCessationSuffix.mandateProjection

def revisedInheritedHealthCessationProjection : RevisedProjection :=
  .inherited M9SourceHealthCessationSuffix.healthCessationProjection

def revisedInheritedRouteProjection : RevisedProjection :=
  .inherited M9SourceHealthCessationSuffix.routeProjection

def revisedInheritedCommonClearingProjection : RevisedProjection :=
  .inherited M9SourceHealthCessationSuffix.commonClearingProjection

def revisedInheritedClearingBackstopProjection : RevisedProjection :=
  .inherited M9SourceHealthCessationSuffix.clearingBackstopProjection

theorem revisedNamedOldCoordinates_preserved
    {current : NewV.Current}
    (occurrence : revisedSource.toRootSource.actual.OccurrenceAt current) :
    HEq (revisedProjectionLaw.outcomeAt revisedInheritedInquiryProjection
          occurrence)
        (healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          M9SourceHealthCessationSuffix.inquiryProjection
          oldHealthTargetSelectionOccurrence) ∧
      HEq (revisedProjectionLaw.outcomeAt revisedInheritedFailureProjection
          occurrence)
        (healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          M9SourceHealthCessationSuffix.failureProjection
          oldHealthTargetSelectionOccurrence) ∧
      HEq (revisedProjectionLaw.outcomeAt revisedInheritedUBIProjection
          occurrence)
        (healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          M9SourceHealthCessationSuffix.ubiProjection
          oldHealthTargetSelectionOccurrence) ∧
      HEq (revisedProjectionLaw.outcomeAt revisedInheritedMandateProjection
          occurrence)
        (healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          M9SourceHealthCessationSuffix.mandateProjection
          oldHealthTargetSelectionOccurrence) ∧
      HEq (revisedProjectionLaw.outcomeAt
          revisedInheritedHealthCessationProjection occurrence)
        (healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          M9SourceHealthCessationSuffix.healthCessationProjection
          oldHealthTargetSelectionOccurrence) ∧
      HEq (revisedProjectionLaw.outcomeAt revisedInheritedRouteProjection
          occurrence)
        (healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          M9SourceHealthCessationSuffix.routeProjection
          oldHealthTargetSelectionOccurrence) ∧
      HEq (revisedProjectionLaw.outcomeAt
          revisedInheritedCommonClearingProjection occurrence)
        (healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          M9SourceHealthCessationSuffix.commonClearingProjection
          oldHealthTargetSelectionOccurrence) ∧
      HEq (revisedProjectionLaw.outcomeAt
          revisedInheritedClearingBackstopProjection occurrence)
        (healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          M9SourceHealthCessationSuffix.clearingBackstopProjection
          oldHealthTargetSelectionOccurrence) :=
  ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    HEq.rfl⟩

def revisedAuthoritySource : SourceNativeAuthoritySource NewN NewV where
  restructuringSource := revisedRestructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal revisedRestructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := revisedTheory
  projectionLaw := revisedProjectionLaw

def revisedAuthoritativeRoot :
    SourceNativeAuthoritativeRootClosure NewN NewV where
  source := revisedAuthoritySource
  emitted := revisedEmitted
  compiler_commutes := fun _ => rfl

def revisedLivingRoot : SourceNativeLivingRootClosure NewN NewV where
  source :=
    { base := revisedAuthoritySource
      terminalHandoff := revisedAuthoritySource.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := revisedEmitted
  compiler_commutes := fun _ => rfl

def revisedInitialVisit : SourceNativeTemporalVisitAt
    revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite revisedLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def revisedOccurrencePresentation : ConstructivePresentation
    (healthCessationTargetRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      RootedFailure.oldSuccessor.next)
    (revisedAuthoritativeRoot.toRoot.actual.OccurrenceAt
      initialSelectionCurrent) where
  forward := by
    rintro ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => exact revisedEmitted initialSelectionCurrent
  backward := by
    rintro ⟨support, event⟩
    cases support with
    | inl oldSupport => exact nomatch event
    | inr direction =>
        exact healthCessationTargetRoot.emitted RootedFailure.oldSuccessor.next
  backward_forward := by
    rintro ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => cases event; rfl
  forward_backward := by
    rintro ⟨support, event⟩
    cases support with
    | inl oldSupport => exact nomatch event
    | inr direction => cases direction; cases event; rfl

def revisedFirstWrite : CanonicalFirstRootWriteAt
    revisedAuthoritativeRoot.toLedgerRoot :=
  PUnit.unit

def revisedInitialGenerated :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      revisedAuthoritativeRoot.toLedgerRoot
      (.finite revisedAuthoritativeRoot.toRoot.initialVisit) :=
  revisedAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite revisedAuthoritativeRoot.toRoot.initialVisit)

def revisedOldEntryRow :
    revisedInitialGenerated.GeneratedEntryRowAt oldRevisedEntry :=
  (revisedInitialGenerated.canonicalGeneratedEntryRow?
    oldRevisedEntry).get (by rfl)

def revisedNewEntryRow :
    revisedInitialGenerated.GeneratedEntryRowAt newRevisedEntry :=
  (revisedInitialGenerated.canonicalGeneratedEntryRow?
    newRevisedEntry).get (by rfl)

theorem oldEntry_eq_target
    (oldEntry : OpenResponsibilityAt
      M14SourceGeneratedHealthCessationTargetRoot.N
      (healthCessationTargetRoot.toAuthoritativeRoot.toRoot.supportAt
        RootedFailure.oldSuccessor.next)) :
    oldEntry = RootedFailure.oldTargetEntry := by
  rcases oldEntry with ⟨responsibility, isOpen⟩
  rcases RootedFailure.oldTargetEntry with
    ⟨targetResponsibility, targetOpen⟩
  cases responsibility
  cases targetResponsibility
  cases isOpen
  cases targetOpen
  rfl

def revisedOldEntryRows
    (oldEntry : OpenResponsibilityAt
      M14SourceGeneratedHealthCessationTargetRoot.N
      (healthCessationTargetRoot.toAuthoritativeRoot.toRoot.supportAt
        RootedFailure.oldSuccessor.next)) :
    revisedInitialGenerated.GeneratedEntryRowAt
      (minimalCoface.cofaceLedgerRetract.forward oldEntry) := by
  rw [oldEntry_eq_target oldEntry]
  exact revisedOldEntryRow

def generatedTypedRevision :
    GeneratedTypedSemanticWorldNetworkRevisionAt RootedFailure where
  NewN := NewN
  translation := minimalCoface.translation
  NewV := NewV
  newLivingRoot := revisedLivingRoot
  new_support_restricts :=
    minimalCoface.firstWrite_targetSupport_is_cofaceRestriction
  oldTargetOpenLedger := minimalCoface.cofaceLedgerRetract
  oldTargetOpenClaim_commutes := fun _ => rfl
  oldTargetOpenProgressBudget_not_refilled := fun _ => Nat.le_refl _
  occurrencePresentation := revisedOccurrencePresentation
  occurrence_commutes := rfl
  firstWrite := revisedFirstWrite
  newOnlyEntry := newRevisedEntry
  newOnlyProgressBudget_eq_zero := rfl
  revisedClaimHolds := minimalCoface.obstructionClaimHolds
  semanticChange := minimalCoface.obstructionSemanticChange
  revisedClaim_hasNoOldPreimage :=
    minimalCoface.obstructionClaim_hasNoOldPreimage
  newOnlyIncidence_hasNoOldPreimage :=
    minimalCoface.obstructionIncidence_hasNoOldPreimage
  oldEntryRows := revisedOldEntryRows
  newOnlyEntry_hasNoOldPreimage :=
    minimalCoface.obstructionEntry_hasNoOldPreimage
  newOnlyEntryRow := revisedNewEntryRow

theorem generatedTypedRevisionFieldGrounding :
    generatedTypedRevision.ExactFieldGrounding where
  network_eq := rfl
  lawSurface_heq := HEq.rfl
  translation_heq := HEq.rfl
  initialSupport_heq := HEq.rfl
  oldTargetOpenLedger_heq := HEq.rfl
  newOnlyEntry_heq := HEq.rfl
  revisedClaimHolds_heq := HEq.rfl
  semanticChange_heq := HEq.rfl

def typedRevisionSource :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt RootedFailure :=
  FieldGroundedTypedSemanticWorldNetworkRevisionAt.ofGeneratedOccurrence
    generatedTypedRevision generatedTypedRevisionFieldGrounding

def installedInitialCriticalRenewal :
    SourceGeneratedInstalledSelectedCriticalRenewalAt
      (revisedEmitted initialSelectionCurrent) ⟨rfl⟩ :=
  revisedProjectionLaw.project .selection
    (revisedEmitted initialSelectionCurrent) ⟨rfl⟩

def installedInitialSelection :
    SourceGeneratedSelectedEssentialAccessCriticalEventAt
      initialSelectionCurrent :=
  installedInitialCriticalRenewal.selected

@[simp] theorem installedInitialSelection_exact :
    installedInitialSelection =
      sourceGeneratedSelectedEssentialAccessCriticalEventAt
        initialSelectionCurrent :=
  rfl

@[simp] theorem installedInitialSelection_event_health :
    installedInitialSelection.selectedEvent = .health := by
  rw [installedInitialSelection_exact]
  exact healthCriticalSelectionInitialSelected_event

theorem retainedSelectionNext_initial_ne :
    retainedSelectionNext initialSelectionCurrent ≠
      initialSelectionCurrent := by
  unfold initialSelectionCurrent
  rw [sourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed
    |>.revisedCurrentExact]
  simp [retainedSelectionNext, AccountedBranches.singleton,
    RootedAccountedUnfolding.zero]

abbrev RevisedFirstTargetSelectionReplay :=
  revisedProjectionLaw.ActiveAt .selection
    (revisedEmitted (retainedSelectionNext initialSelectionCurrent))

theorem revisedFirstTargetSelectionReplay_isEmpty :
    IsEmpty RevisedFirstTargetSelectionReplay :=
  ⟨fun replay => retainedSelectionNext_initial_ne replay.down⟩

def revisedFirstTargetSelectionInactive :
    revisedProjectionLaw.InactiveAt .selection
      (revisedEmitted (retainedSelectionNext initialSelectionCurrent)) :=
  ⟨retainedSelectionNext_initial_ne⟩

theorem revisedFirstTargetSelection_classifies_inactive :
    revisedProjectionLaw.classify .selection
        (revisedEmitted (retainedSelectionNext initialSelectionCurrent)) =
      .inr revisedFirstTargetSelectionInactive := by
  classical
  change (if current_eq : retainedSelectionNext initialSelectionCurrent =
      initialSelectionCurrent then
        Sum.inl (PLift.up current_eq)
      else Sum.inr (PLift.up current_eq)) = _
  rw [dif_neg retainedSelectionNext_initial_ne]
  unfold revisedFirstTargetSelectionInactive
  rfl

theorem installedInitialCriticalRenewal_exact :
    installedInitialCriticalRenewal.selected =
        sourceGeneratedSelectedEssentialAccessCriticalEventAt
          initialSelectionCurrent ∧
      installedInitialCriticalRenewal.payload.sourceSeed =
        sourceEssentialAccessCriticalSeed .health ∧
      installedInitialCriticalRenewal.payload.consumer.action =
        sourceGeneratedEssentialAccessCriticalActionAt .health ∧
      installedInitialCriticalRenewal.payload.disposition.update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt .health ∧
      installedInitialCriticalRenewal.payload.sourceEntry =
        newRevisedEntry ∧
      installedInitialCriticalRenewal.payload.successor.targetCurrent =
        retainedSelectionNext initialSelectionCurrent :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def revisedFirstSuccessor :
    SourceNativeLedgerGeneratedSuccessorAt
      generatedTypedRevision.initialRestructuringGenerated.occurrence
      generatedTypedRevision.initialRestructuringGenerated.wholeLedgerWriteBack :=
  PUnit.unit

theorem revisedFirstSuccessor_targetCurrent :
    revisedFirstSuccessor.targetCurrent =
      retainedSelectionNext initialSelectionCurrent :=
  rfl

theorem installedInitialCriticalRenewal_successor_exact :
    HEq installedInitialCriticalRenewal.payload.successor
      revisedFirstSuccessor :=
  HEq.rfl

def revisedRoot_wholeInitialRowsAndClaim :
    generatedTypedRevision.NewN.HoldsAt
        (generatedTypedRevision.newLivingRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (generatedTypedRevision.newLivingRoot.toAuthoritativeRoot.toLedgerRoot.emitted
            generatedTypedRevision.newLivingRoot.toAuthoritativeRoot.toRoot.source.initial))
        generatedTypedRevision.newOnlyEntry.claim ×
      generatedTypedRevision.NewN.SemanticChangeAt
        (generatedTypedRevision.newLivingRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (generatedTypedRevision.newLivingRoot.toAuthoritativeRoot.toLedgerRoot.emitted
            generatedTypedRevision.newLivingRoot.toAuthoritativeRoot.toRoot.source.initial))
        (generatedTypedRevision.translation.claim.forward
        (M14SourceGeneratedHealthCessationTargetRoot.N.obstructionClaim
            RootInquiryU8CompletionRegression.obstruction))
        generatedTypedRevision.newOnlyEntry.claim ×
      PLift ((generatedTypedRevision.oldEntryRows
        RootedFailure.oldTargetEntry).sourceRow.CommutesWithWorld) ×
      PLift generatedTypedRevision.newOnlyEntryRow.sourceRow.CommutesWithWorld ×
      PLift installedInitialCriticalRenewal.payload.selectedRow.CommutesWithWorld :=
  ⟨generatedTypedRevision.revisedClaimHolds,
    generatedTypedRevision.semanticChange,
    ⟨generatedTypedRevision.oldEntryRow_commutes_with_world
      RootedFailure.oldTargetEntry⟩,
    ⟨generatedTypedRevision.newOnlyEntryRow_commutes_with_world⟩,
    ⟨installedInitialCriticalRenewal.payload.selectedRow.commutes_with_world⟩⟩

abbrev RevisedRootInitialFactorization :=
  FaithfulCofaceMorphism
      (root_obstruction_generates_minimal_coface RootedFailure)
      generatedTypedRevision.toAdmissibleMinimalCoface ×
    SourceGeneratedAttachedCofaceRealizationAt generatedTypedRevision

def revisedRoot_fullInitialFactorization :
    RevisedRootInitialFactorization :=
  generatedTypedRevision.factorizesThroughInitialCoface

theorem revisedRoot_directConsumer :
    typedRevisionSource.generate = generatedTypedRevision ∧
      installedInitialSelection.selectedEvent = .health ∧
      installedInitialSelection.action.criticalBearer.bearerLineage.seed =
          initialSelectionCurrent.root ∧
      installedInitialCriticalRenewal.payload.consumer.action =
        sourceGeneratedEssentialAccessCriticalActionAt .health ∧
      installedInitialCriticalRenewal.payload.disposition.update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt .health ∧
      revisedFirstSuccessor.targetCurrent =
        retainedSelectionNext initialSelectionCurrent ∧
      IsEmpty RevisedFirstTargetSelectionReplay ∧
      Nonempty RevisedRootInitialFactorization := by
  refine ⟨rfl, installedInitialSelection_event_health, ?_,
    installedInitialCriticalRenewal_exact.2.2.1,
    installedInitialCriticalRenewal_exact.2.2.2.1,
    revisedFirstSuccessor_targetCurrent,
    revisedFirstTargetSelectionReplay_isEmpty,
    ⟨revisedRoot_fullInitialFactorization⟩⟩
  rw [installedInitialSelection_exact]
  exact (sourceGeneratedSelectedEssentialAccessCriticalEventAt
    initialSelectionCurrent).actionSeed_commutes

end
end M14SourceGeneratedCriticalEventSelectionRevisedRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedRoot.generatedTypedRevision
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedRoot.typedRevisionSource
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedRoot.revisedRoot_directConsumer
