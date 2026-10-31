import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Runtime.SourceGeneratedTenureQueueAppendRuntime
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.Revised.NoGo.SourceGeneratedCriticalEventSelectionRevisedRootNoGo
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Source.Queue.SourceGeneratedEssentialAccessCriticalActionQueueSuccession

/-!
# Proof-carrying critical-event selection U8

The health action's generated macro next reaches the exact old target at
depth one.  Its installed failure face opens one fixed U8 runtime tick, whose
two live rows generate the revised root at depth two.  The immediately
generated next tick executes the first queue occurrence as a tenure actual
action, crosses to the append root, installs its fold-selected renewal, and
then reaches an inactive retained successor.

The whole theorem retains the machine no-go against claiming preinstalled
tenure/health/platform coverage.  The three-position queue remains finite
actual provenance; only tenure is installed here, by the exact runtime action.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCriticalEventSelectionU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M10OccurrenceCapacityProcessFixture
open M14EssentialAccessRelationFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedSequentialHealthCessation
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedHealthCessationTargetRoot
open M14SourceGeneratedHealthCessationTargetHistory
open M14HealthTargetCriticalEventSelectionNoGo
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedHealthTargetCriticalEventSelectionU8Compilation
open M14SourceGeneratedHealthTargetCriticalEventSelectionU8Runtime
open M14SourceGeneratedCriticalEventSelectionRevisedRootNoGo
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedEssentialAccessCriticalActionQueue
open M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession
open M14SourceGeneratedTenureQueueActionAtRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedSequentialTenureQueueAppend
open M14SourceGeneratedTenureQueueAppendContinuation
open M14SourceGeneratedTenureQueueAppendRuntime

/-- Complete checkpoint carrier.  Its constructor is private so a caller
cannot replace the revised root, queue action, event or first successor. -/
structure RootControlledCriticalEventSelectionU8TenureAppendAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Type 15 where
  private mk ::
  priorMacroNextDepthOne :
    (generatedHealthCessationActionAt initial depth).target.targetVisit =
      healthCessationTargetTemporalVisitAt 1
  compilationProgramExact :
    healthTargetSelectionInquiryState.compilationProgramAt () =
      healthTargetSelectionRequiresU8Program
  runtimeU8Installed :
    SourceNativeInquiryRuntime.CofaceRealizationInstalledAt
      healthTargetSelectionInquiryFrontier
        healthTargetSelectionRealizationCandidate runtime 0
  runtimeU8ResolutionExact :
    u8Tick.resolution =
      .revised RootInquiryU8CompletionRegression.obstruction
        RootInquiryU8CompletionRegression.u7Gate
        RootInquiryU8CompletionRegression.failure
        healthTargetSelectionU8Core
  realizationCertified :
    SourceNativeInquiryCofaceRealizationCertificationAt
      healthTargetSelectionRealizationCandidate healthTargetSelectionU8Core
  runtimeCofaceAnswerAndNext :
    Nonempty healthTargetSelectionCompletion.CofaceAnswerAndNextReceiptAt
  runtimeU8NextRootExact :
    HEq u8Tick.next.node.erase.current.root
      revisedLivingRoot.toAuthoritativeRoot
  runtimeTenureActionResumed :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      generatedTenureQueueAppendAction runtime 1
  runtimeTenureActionResolutionExact :
    tenureActionTick.resolution =
      .actualAction generatedTenureQueueAppendAction
  runtimeTenureActionReceiptProvenance :
    TenureQueueAppendReceiptProvenanceAt revisedDepthTwoEvent
  runtimeTenureActionTargetRootExact :
    HEq tenureActionTick.next.node.erase.current.root
      tenureAppendTargetRoot.toAuthoritativeRoot
  runtimeTenureSelectionCurrentExact :
    (runtime.stateAt 2).engine.node.erase.current.visit.current =
      appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction
  runtimeTenureSelectionResolutionExact :
    tenureSelectionTick.resolution =
      .directlyAnswered (tenureAppendSelectionAnswerFaceAt 0)
        (tenureAppendSelectionAnswerConsumerAt 0)
  runtimeTenureSelectionEvent :
    tenureAppendInstalledRenewal.selected.selectedEvent = .tenure
  runtimeTenureSelectionAction :
    tenureAppendInstalledRenewal.payload.consumer.action =
      tenureQueueAction.action
  runtimeTenureSelectionUpdate :
    tenureAppendInstalledRenewal.payload.disposition.update =
      sourceGeneratedEssentialAccessCriticalActualUpdateAt .tenure
  runtimeRetainedCurrentExact :
    erasedCurrentLabel (runtime.stateAt 3).engine.node.erase =
      ⟨EssentialAccessCriticalSelectionCurrent,
        retainedSelectionNext
          (appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction)⟩
  runtimeRetainedSelectionInactive :
    IsEmpty (AppendedSelectionReplayAt revisedLivingRoot
      revisedDepthTwoEvent.occurrence tenureAppendPrior tenureQueueAction)
  initialSelectionHealth : installedInitialSelection.selectedEvent = .health
  installedActionExact :
    installedInitialCriticalRenewal.payload.consumer.action =
      sourceGeneratedEssentialAccessCriticalActionAt .health
  installedUpdateExact :
    installedInitialCriticalRenewal.payload.disposition.update =
      sourceGeneratedEssentialAccessCriticalActualUpdateAt .health
  wholeRowsAndClaim : Nonempty
    (type_of% revisedRoot_wholeInitialRowsAndClaim)
  oldProjectionOutcomesPreserved :
    (projection : OldHealthTargetProjection) →
      HEq (revisedProjectionLaw.outcomeAt (.inherited projection)
          (revisedEmitted initialSelectionCurrent))
        (healthCessationTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          projection oldHealthTargetSelectionOccurrence)
  firstSuccessorSelectionInactive :
    IsEmpty RevisedFirstTargetSelectionReplay
  oldRawCoverageEmpty : IsEmpty OldHealthTargetCriticalEventCoverageAt
  installedFamilyCoverageEmpty :
    IsEmpty RevisedInstalledCriticalEventFamilyCoverageAt
  noUnaccountedProjection : IsEmpty UnaccountedRevisedProjectionAt
  noCompletedFiniteCofinalVisit :
    IsEmpty (StrictCofinalRootVisitAt revisedProductiveFiniteHistory)
  tenureQueueAction :
    SourceGeneratedEssentialAccessCriticalActionQueueAt firstExactUnit
  healthQueueAction :
    SourceGeneratedEssentialAccessCriticalActionQueueAt middleExactUnit
  platformQueueAction :
    SourceGeneratedEssentialAccessCriticalActionQueueAt recurrentExactUnit
  everyQueueOccurrenceGeneratesAction :
    (unit : ExactQueueUnit) →
      Nonempty (SourceGeneratedEssentialAccessCriticalActionQueueAt unit)
  queueFirstToMiddle : SourceGeneratedQueueCriticalActionSuccessorAt
    firstExactUnit middleExactUnit
  queueMiddleToRecurrent : SourceGeneratedQueueCriticalActionSuccessorAt
    middleExactUnit recurrentExactUnit
  queueRecurrentTerminal : IsEmpty RecurrentQueueCriticalActionSuccessorAt

def sourceGeneratedRootControlledCriticalEventSelectionU8TenureAppendAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    RootControlledCriticalEventSelectionU8TenureAppendAt initial depth where
  priorMacroNextDepthOne :=
    generatedHealthCessationAction_targetVisit_eq_depthOne initial depth
  compilationProgramExact := rfl
  runtimeU8Installed := u8RuntimeInstallation
  runtimeU8ResolutionExact := u8Tick_resolution_exact
  realizationCertified := healthTargetSelectionRealizationCertification
  runtimeCofaceAnswerAndNext := ⟨u8TickCofaceAnswerAndNextReceipt⟩
  runtimeU8NextRootExact := HEq.rfl
  runtimeTenureActionResumed := tenureActionRuntimeResumption
  runtimeTenureActionResolutionExact := tenureActionTick_resolution_exact
  runtimeTenureActionReceiptProvenance :=
    tenureActionTickReceipt_provenance
  runtimeTenureActionTargetRootExact := HEq.rfl
  runtimeTenureSelectionCurrentExact := tenureSelectionState_current_exact
  runtimeTenureSelectionResolutionExact :=
    tenureSelectionTick_resolution_exact
  runtimeTenureSelectionEvent :=
    tenureSelectionState_installs_exact_queue_action.1
  runtimeTenureSelectionAction :=
    tenureSelectionState_installs_exact_queue_action.2.1
  runtimeTenureSelectionUpdate :=
    tenureSelectionState_installs_exact_queue_action.2.2
  runtimeRetainedCurrentExact := tenureRetainedState_current_exact
  runtimeRetainedSelectionInactive :=
    tenureRetainedState_selectionReplay_isEmpty
  initialSelectionHealth := installedInitialSelection_event_health
  installedActionExact := installedInitialCriticalRenewal_exact.2.2.1
  installedUpdateExact := installedInitialCriticalRenewal_exact.2.2.2.1
  wholeRowsAndClaim := ⟨revisedRoot_wholeInitialRowsAndClaim⟩
  oldProjectionOutcomesPreserved := fun projection =>
    revisedInheritedProjection_outcome_exact projection
      (revisedEmitted initialSelectionCurrent)
  firstSuccessorSelectionInactive := revisedFirstTargetSelectionReplay_isEmpty
  oldRawCoverageEmpty := oldHealthTargetCriticalEventCoverage_isEmpty
  installedFamilyCoverageEmpty :=
    revisedInstalledCriticalEventFamilyCoverage_isEmpty
  noUnaccountedProjection := unaccountedRevisedProjection_isEmpty
  noCompletedFiniteCofinalVisit := revisedStrictCofinalFiniteVisit_isEmpty
  tenureQueueAction := sourceGeneratedTenureCriticalActionQueue
  healthQueueAction := sourceGeneratedHealthCriticalActionQueue
  platformQueueAction := sourceGeneratedPlatformCriticalActionQueue
  everyQueueOccurrenceGeneratesAction :=
    everyExactQueueUnit_generatesEssentialAccessCriticalAction
  queueFirstToMiddle := firstToMiddleQueueCriticalAction
  queueMiddleToRecurrent := middleToRecurrentQueueCriticalAction
  queueRecurrentTerminal := recurrentQueueCriticalActionSuccessor_isEmpty

/-- Public whole mouth.  It accepts only the already registered canonical
cycle and finite depth; no event, seed, current, root, core or candidate is a
producer argument. -/
theorem cycle_rootControlledCriticalEventSelectionU8TenureAppend
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    Nonempty
      (RootControlledCriticalEventSelectionU8TenureAppendAt initial depth) :=
  ⟨sourceGeneratedRootControlledCriticalEventSelectionU8TenureAppendAt
    initial depth⟩

theorem rootControlledCriticalEventSelectionU8TenureAppend_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    let whole :=
      sourceGeneratedRootControlledCriticalEventSelectionU8TenureAppendAt
        initial depth
    SourceNativeInquiryRuntime.CofaceRealizationInstalledAt
        healthTargetSelectionInquiryFrontier
          healthTargetSelectionRealizationCandidate runtime 0 ∧
      SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
        generatedTenureQueueAppendAction runtime 1 ∧
      whole.initialSelectionHealth = installedInitialSelection_event_health ∧
      whole.runtimeTenureSelectionEvent =
        tenureSelectionState_installs_exact_queue_action.1 ∧
      whole.tenureQueueAction.event = EssentialAccessEvent.tenure ∧
      whole.healthQueueAction.event = EssentialAccessEvent.health ∧
      whole.platformQueueAction.event = EssentialAccessEvent.platform ∧
      IsEmpty (AppendedSelectionReplayAt revisedLivingRoot
        revisedDepthTwoEvent.occurrence tenureAppendPrior tenureQueueAction) ∧
      IsEmpty RevisedInstalledCriticalEventFamilyCoverageAt :=
  ⟨u8RuntimeInstallation, tenureActionRuntimeResumption,
    rfl, rfl, rfl, rfl, rfl,
    tenureRetainedState_selectionReplay_isEmpty,
    revisedInstalledCriticalEventFamilyCoverage_isEmpty⟩

end
end M14ProofCarryingCriticalEventSelectionU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCriticalEventSelectionU8.sourceGeneratedRootControlledCriticalEventSelectionU8TenureAppendAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCriticalEventSelectionU8.cycle_rootControlledCriticalEventSelectionU8TenureAppend
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCriticalEventSelectionU8.rootControlledCriticalEventSelectionU8TenureAppend_directConsumer
