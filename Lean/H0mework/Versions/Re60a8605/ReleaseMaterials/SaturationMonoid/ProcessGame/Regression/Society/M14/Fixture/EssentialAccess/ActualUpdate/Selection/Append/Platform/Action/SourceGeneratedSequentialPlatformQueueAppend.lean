import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Platform.Action.SourceGeneratedPlatformQueueAppendTarget

/-! # Sequential platform queue append -/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialPlatformQueueAppend

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M10OccurrenceCapacityProcessFixture
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedHealthQueueActionAtTenureRoot
open M14SourceGeneratedHealthQueueAppendTarget
open M14SourceGeneratedHealthQueueAppendContinuation
open M14SourceGeneratedPlatformQueueActionAtHealthRoot
open M14SourceGeneratedSequentialQueueAppendTarget
open M14SourceGeneratedSequentialQueueAppendProgram
open M14SourceGeneratedPlatformQueueAppendTarget

def platformQueueAppendProgram := sequentialQueueAppendProgram
  tenureAppendTargetRoot healthAppendExactEvent.occurrence healthAppendPrior
    healthQueueAction (healthAppendTemporalVisitAt 1)
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntry
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceAuthority
    platformAppendPrior platformQueueAction rfl
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntryExact
    PlatformQueueAppendSourceSealAt platformQueueAppendSourceSealAt

def generatedPlatformQueueAppendAction := generatedSequentialQueueAppendAction
  tenureAppendTargetRoot healthAppendExactEvent.occurrence healthAppendPrior
    healthQueueAction (healthAppendTemporalVisitAt 1)
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntry
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceAuthority
    platformAppendPrior platformQueueAction rfl
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntryExact
    PlatformQueueAppendSourceSealAt platformQueueAppendSourceSealAt
    platformAppendExactEvent

def platformQueueAppendActualActionCompilation :=
  sequentialQueueAppendActualActionCompilation tenureAppendTargetRoot
    healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction
    (healthAppendTemporalVisitAt 1)
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntry
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceAuthority
    platformAppendPrior platformQueueAction rfl
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntryExact
    PlatformQueueAppendSourceSealAt platformQueueAppendSourceSealAt
    platformAppendExactEvent

theorem generatedPlatformQueueAppendSourceSeal :
    PlatformQueueAppendSourceSealAt platformAppendExactEvent :=
  generatedPlatformQueueAppendAction.receipt.down.down.1

theorem generatedPlatformQueueAppendReceiptCore :
    SequentialQueueAppendReceiptCoreAt tenureAppendTargetRoot
      healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction
      (healthAppendTemporalVisitAt 1)
      sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntry
      platformAppendPrior platformQueueAction platformAppendExactEvent :=
  generatedPlatformQueueAppendAction.receipt.down.down.2

@[simp] theorem generatedPlatformQueueAppendAction_targetRoot_exact :
    generatedPlatformQueueAppendAction.target.targetRoot =
      appendLivingRoot healthAppendTargetRoot
        platformAppendExactEvent.occurrence platformAppendPrior
          platformQueueAction :=
  rfl

@[simp] theorem generatedPlatformQueueAppendAction_targetCurrent_exact :
    generatedPlatformQueueAppendAction.target.firstSuccessor.targetCurrent =
      appendedCriticalSelectionCurrent platformAppendPrior
        platformQueueAction :=
  generatedPlatformQueueAppendReceiptCore.targetAppendCurrent

@[simp] theorem generatedPlatformQueueAppendAction_newRootSeed_exact :
    generatedPlatformQueueAppendAction.target.firstSuccessor.targetCurrent.root =
      platformQueueAction.action.criticalBearer.bearerLineage.seed := by
  rw [generatedPlatformQueueAppendAction_targetCurrent_exact]
  rfl

@[simp] theorem platformQueueAppendActualActionCompilation_exact :
    platformQueueAppendActualActionCompilation =
      .actualAction generatedPlatformQueueAppendAction :=
  rfl

theorem generatedPlatformQueueAppendAction_macroNext_exact :
    generatedPlatformQueueAppendAction.target.targetAnswerAndNext.nextCurrent =
      ⟨generatedPlatformQueueAppendAction.target.TargetV,
        platformAppendTargetRoot.toAuthoritativeRoot,
        generatedPlatformQueueAppendAction.target.targetVisit⟩ :=
  generatedPlatformQueueAppendAction.target.targetAnswerAndNext_next_eq

def platformAppendInstalledRenewal := installedAppendedCriticalRenewal
  healthAppendTargetRoot platformAppendExactEvent.occurrence
    platformAppendPrior platformQueueAction

theorem generatedPlatformQueueAppend_inheritedOutcomes
    (projection :
      healthAppendTargetRoot.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((appendProjectionLaw healthAppendTargetRoot
      platformAppendExactEvent.occurrence platformAppendPrior
        platformQueueAction).outcomeAt (.inherited projection)
          (appendEmitted platformAppendPrior platformQueueAction
            platformAppendPrior))
      (healthAppendTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        projection platformAppendExactEvent.occurrence) :=
  generatedPlatformQueueAppendReceiptCore.inheritedOutcomes projection

theorem generatedPlatformQueueAppend_selectionReplay_isEmpty :
    IsEmpty (AppendedSelectionReplayAt healthAppendTargetRoot
      platformAppendExactEvent.occurrence platformAppendPrior
        platformQueueAction) :=
  generatedPlatformQueueAppendReceiptCore.selectionReplay

theorem sequentialPlatformQueueAppend_directConsumer :
    platformQueueAppendActualActionCompilation =
        .actualAction generatedPlatformQueueAppendAction ∧
      SourceGeneratedQueueCriticalActionSuccessorAt
        middleExactUnit recurrentExactUnit ∧
      IsEmpty RecurrentQueueCriticalActionSuccessorAt ∧
      generatedPlatformQueueAppendAction.target.firstSuccessor.targetCurrent =
        appendedCriticalSelectionCurrent platformAppendPrior
          platformQueueAction ∧
      (appendedCriticalSelectionCurrent platformAppendPrior
        platformQueueAction).root =
          platformQueueAction.action.criticalBearer.bearerLineage.seed ∧
      platformAppendInstalledRenewal.selected.selectedEvent = .platform ∧
      platformAppendInstalledRenewal.payload.consumer.action =
        platformQueueAction.action ∧
      platformAppendInstalledRenewal.payload.disposition.update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt .platform ∧
      platformAppendInstalledRenewal.payload.successor.targetCurrent =
        retainedSelectionNext
          (appendedCriticalSelectionCurrent platformAppendPrior
            platformQueueAction) ∧
      IsEmpty (AppendedSelectionReplayAt healthAppendTargetRoot
        platformAppendExactEvent.occurrence platformAppendPrior
          platformQueueAction) :=
  ⟨rfl, generatedPlatformQueueAppendSourceSeal.queueSuccession,
    generatedPlatformQueueAppendSourceSeal.noFiniteQueueSuccessor,
    generatedPlatformQueueAppendReceiptCore.targetAppendCurrent,
    rfl, generatedPlatformQueueAppendReceiptCore.selectedRenewal.1,
    generatedPlatformQueueAppendReceiptCore.selectedRenewal.2.1,
    generatedPlatformQueueAppendReceiptCore.selectedRenewal.2.2,
    generatedPlatformQueueAppendReceiptCore.selectedRetainedSuccessor,
    generatedPlatformQueueAppendReceiptCore.selectionReplay⟩

end
end M14SourceGeneratedSequentialPlatformQueueAppend
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialPlatformQueueAppend.generatedPlatformQueueAppendAction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialPlatformQueueAppend.platformQueueAppendActualActionCompilation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialPlatformQueueAppend.sequentialPlatformQueueAppend_directConsumer
