import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Consumer.ProofCarryingCriticalEventSelectionU8
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Runtime.SourceGeneratedTenureQueueAppendRuntime
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Health.NoGo.SourceGeneratedHealthQueueAppendNoGo

/-!
# Proof-carrying health queue append

The registered U8-to-tenure checkpoint is consumed intact.  At its exact
retained current the same runtime executes the middle queue's health action,
migrates every tenure-root projection, installs health event/action/update,
and reaches a retained successor where platform-at-the-same-occurrence and
selection replay are both empty.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCriticalEventSelectionHealthAppend

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M10OccurrenceCapacityProcessFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedTenureQueueActionAtRevisedRoot
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedHealthQueueActionAtTenureRoot
open M14SourceGeneratedHealthQueueAppendTarget
open M14SourceGeneratedSequentialQueueAppendTarget
open M14SourceGeneratedSequentialHealthQueueAppend
open M14SourceGeneratedTenureQueueAppendRuntime
open M14SourceGeneratedHealthQueueAppendNoGo
open M14ProofCarryingCriticalEventSelectionU8

structure RootControlledCriticalEventSelectionU8TenureHealthAppendAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Type 15 where
  private mk ::
  tenureCheckpoint :
    RootControlledCriticalEventSelectionU8TenureAppendAt initial depth
  healthRuntimeResumption :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      generatedHealthQueueAppendAction runtime 3
  retainedTenureCurrent :
    erasedCurrentLabel (runtime.stateAt 3).engine.node.erase =
      ⟨EssentialAccessCriticalSelectionCurrent,
        retainedSelectionNext
          (appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction)⟩
  healthSourceSeal : HealthQueueAppendSourceSealAt healthAppendExactEvent
  healthReceiptCore : type_of% healthActionTickReceiptCore
  healthTargetRootExact :
    HEq healthActionTick.next.node.erase.current.root
      healthAppendTargetRoot.toAuthoritativeRoot
  healthAppendedCurrent :
    (runtime.stateAt 4).engine.node.erase.current.visit.current =
      appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction
  healthNewRootSeed :
    (appendedCriticalSelectionCurrent healthAppendPrior
      healthQueueAction).root =
        healthQueueAction.action.criticalBearer.bearerLineage.seed
  healthInstalledEvent :
    healthAppendInstalledRenewal.selected.selectedEvent = .health
  healthInstalledAction :
    healthAppendInstalledRenewal.payload.consumer.action =
      healthQueueAction.action
  healthInstalledUpdate :
    healthAppendInstalledRenewal.payload.disposition.update =
      sourceGeneratedEssentialAccessCriticalActualUpdateAt .health
  inheritedTenureOutcomes :
    (projection :
      tenureAppendTargetRoot.toAuthoritativeRoot.source.projectionLaw.Projection) →
      HEq ((appendProjectionLaw tenureAppendTargetRoot
        healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction
        ).outcomeAt (.inherited projection)
          (appendEmitted healthAppendPrior healthQueueAction healthAppendPrior))
        (tenureAppendTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          projection healthAppendExactEvent.occurrence)
  retainedHealthCurrent :
    erasedCurrentLabel (runtime.stateAt 5).engine.node.erase =
      ⟨EssentialAccessCriticalSelectionCurrent,
        retainedSelectionNext
          (appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction)⟩
  platformSameOccurrenceEmpty : IsEmpty PlatformAtHealthAppendOccurrence
  twoEventsSameOccurrenceEmpty :
    IsEmpty (TwoSelectedCriticalEventsAt HealthAppendedCurrent)
  retainedHealthReplayEmpty :
    IsEmpty (AppendedSelectionReplayAt tenureAppendTargetRoot
      healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction)

def sourceGeneratedRootControlledCriticalEventSelectionU8TenureHealthAppendAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    RootControlledCriticalEventSelectionU8TenureHealthAppendAt initial depth where
  tenureCheckpoint :=
    sourceGeneratedRootControlledCriticalEventSelectionU8TenureAppendAt
      initial depth
  healthRuntimeResumption := healthActionRuntimeResumption
  retainedTenureCurrent := tenureRetainedState_current_exact
  healthSourceSeal := healthActionTickSourceSeal
  healthReceiptCore := healthActionTickReceiptCore
  healthTargetRootExact := HEq.rfl
  healthAppendedCurrent := healthSelectionState_current_exact
  healthNewRootSeed := healthSelectionState_newRootSeed_exact
  healthInstalledEvent := healthSelectionState_installs_exact_queue_action.1
  healthInstalledAction :=
    healthSelectionState_installs_exact_queue_action.2.1
  healthInstalledUpdate :=
    healthSelectionState_installs_exact_queue_action.2.2
  inheritedTenureOutcomes := generatedHealthQueueAppend_inheritedOutcomes
  retainedHealthCurrent := healthRetainedState_current_exact
  platformSameOccurrenceEmpty := platformAtHealthAppendOccurrence_isEmpty
  twoEventsSameOccurrenceEmpty := twoEventsAtHealthAppendOccurrence_isEmpty
  retainedHealthReplayEmpty := healthRetainedState_selectionReplay_isEmpty

theorem cycle_rootControlledCriticalEventSelectionU8TenureHealthAppend
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    Nonempty
      (RootControlledCriticalEventSelectionU8TenureHealthAppendAt initial depth) :=
  ⟨sourceGeneratedRootControlledCriticalEventSelectionU8TenureHealthAppendAt
    initial depth⟩

theorem rootControlledCriticalEventSelectionHealthAppend_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    Nonempty
        (RootControlledCriticalEventSelectionU8TenureHealthAppendAt
          initial depth) ∧
      SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
        generatedHealthQueueAppendAction runtime 3 ∧
      healthAppendInstalledRenewal.selected.selectedEvent = .health ∧
      IsEmpty PlatformAtHealthAppendOccurrence ∧
      IsEmpty (AppendedSelectionReplayAt tenureAppendTargetRoot
        healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction) :=
  ⟨cycle_rootControlledCriticalEventSelectionU8TenureHealthAppend
      initial depth,
    healthActionRuntimeResumption,
    healthSelectionState_installs_exact_queue_action.1,
    platformAtHealthAppendOccurrence_isEmpty,
    healthRetainedState_selectionReplay_isEmpty⟩

end
end M14ProofCarryingCriticalEventSelectionHealthAppend
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCriticalEventSelectionHealthAppend.sourceGeneratedRootControlledCriticalEventSelectionU8TenureHealthAppendAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCriticalEventSelectionHealthAppend.cycle_rootControlledCriticalEventSelectionU8TenureHealthAppend
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCriticalEventSelectionHealthAppend.rootControlledCriticalEventSelectionHealthAppend_directConsumer
