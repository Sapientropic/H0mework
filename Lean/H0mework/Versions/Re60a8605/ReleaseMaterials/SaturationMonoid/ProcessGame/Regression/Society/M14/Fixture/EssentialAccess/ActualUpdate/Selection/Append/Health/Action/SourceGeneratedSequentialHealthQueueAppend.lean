import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Health.Action.SourceGeneratedHealthQueueAppendTarget

/-! # Sequential health queue append -/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialHealthQueueAppend

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M10OccurrenceCapacityProcessFixture
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedTenureQueueActionAtRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedTenureQueueAppendContinuation
open M14SourceGeneratedHealthQueueActionAtTenureRoot
open M14SourceGeneratedSequentialQueueAppendTarget
open M14SourceGeneratedSequentialQueueAppendProgram
open M14SourceGeneratedHealthQueueAppendTarget

def healthQueueAppendProgram := sequentialQueueAppendProgram
  revisedLivingRoot revisedDepthTwoEvent.occurrence tenureAppendPrior
    tenureQueueAction (tenureAppendTemporalVisitAt 1)
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntry
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceAuthority
    healthAppendPrior healthQueueAction rfl
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntryExact
    HealthQueueAppendSourceSealAt healthQueueAppendSourceSealAt

def generatedHealthQueueAppendAction := generatedSequentialQueueAppendAction
  revisedLivingRoot revisedDepthTwoEvent.occurrence tenureAppendPrior
    tenureQueueAction (tenureAppendTemporalVisitAt 1)
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntry
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceAuthority
    healthAppendPrior healthQueueAction rfl
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntryExact
    HealthQueueAppendSourceSealAt healthQueueAppendSourceSealAt
    healthAppendExactEvent

def healthQueueAppendActualActionCompilation :=
  sequentialQueueAppendActualActionCompilation revisedLivingRoot
    revisedDepthTwoEvent.occurrence tenureAppendPrior tenureQueueAction
    (tenureAppendTemporalVisitAt 1)
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntry
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceAuthority
    healthAppendPrior healthQueueAction rfl
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntryExact
    HealthQueueAppendSourceSealAt healthQueueAppendSourceSealAt
    healthAppendExactEvent

theorem generatedHealthQueueAppendSourceSeal :
    HealthQueueAppendSourceSealAt healthAppendExactEvent :=
  generatedHealthQueueAppendAction.receipt.down.down.1

theorem generatedHealthQueueAppendReceiptCore :
    SequentialQueueAppendReceiptCoreAt revisedLivingRoot
      revisedDepthTwoEvent.occurrence tenureAppendPrior tenureQueueAction
      (tenureAppendTemporalVisitAt 1)
      sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntry healthAppendPrior
      healthQueueAction healthAppendExactEvent :=
  generatedHealthQueueAppendAction.receipt.down.down.2

@[simp] theorem generatedHealthQueueAppendAction_targetRoot_exact :
    generatedHealthQueueAppendAction.target.targetRoot =
      appendLivingRoot tenureAppendTargetRoot healthAppendExactEvent.occurrence
        healthAppendPrior healthQueueAction :=
  rfl

@[simp] theorem generatedHealthQueueAppendAction_targetCurrent_exact :
    generatedHealthQueueAppendAction.target.firstSuccessor.targetCurrent =
      appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction :=
  generatedHealthQueueAppendReceiptCore.targetAppendCurrent

@[simp] theorem generatedHealthQueueAppendAction_newRootSeed_exact :
    generatedHealthQueueAppendAction.target.firstSuccessor.targetCurrent.root =
      healthQueueAction.action.criticalBearer.bearerLineage.seed := by
  rw [generatedHealthQueueAppendAction_targetCurrent_exact]
  rfl

@[simp] theorem healthQueueAppendActualActionCompilation_exact :
    healthQueueAppendActualActionCompilation =
      .actualAction generatedHealthQueueAppendAction :=
  rfl

theorem generatedHealthQueueAppendAction_macroNext_exact :
    generatedHealthQueueAppendAction.target.targetAnswerAndNext.nextCurrent =
      ⟨generatedHealthQueueAppendAction.target.TargetV,
        healthAppendTargetRoot.toAuthoritativeRoot,
        generatedHealthQueueAppendAction.target.targetVisit⟩ :=
  generatedHealthQueueAppendAction.target.targetAnswerAndNext_next_eq

def healthAppendInstalledRenewal := installedAppendedCriticalRenewal
  tenureAppendTargetRoot healthAppendExactEvent.occurrence
    healthAppendPrior healthQueueAction

theorem generatedHealthQueueAppend_inheritedOutcomes
    (projection : tenureAppendTargetRoot.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((appendProjectionLaw tenureAppendTargetRoot
      healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction
      ).outcomeAt (.inherited projection)
        (appendEmitted healthAppendPrior healthQueueAction healthAppendPrior))
      (tenureAppendTargetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        projection healthAppendExactEvent.occurrence) :=
  generatedHealthQueueAppendReceiptCore.inheritedOutcomes projection

theorem generatedHealthQueueAppend_selectionReplay_isEmpty :
    IsEmpty (AppendedSelectionReplayAt tenureAppendTargetRoot
      healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction) :=
  generatedHealthQueueAppendReceiptCore.selectionReplay

theorem sequentialHealthQueueAppend_directConsumer :
    healthQueueAppendActualActionCompilation =
        .actualAction generatedHealthQueueAppendAction ∧
      SourceGeneratedQueueCriticalActionSuccessorAt
        firstExactUnit middleExactUnit ∧
      generatedHealthQueueAppendAction.target.firstSuccessor.targetCurrent =
        appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction ∧
      (appendedCriticalSelectionCurrent healthAppendPrior
        healthQueueAction).root =
          healthQueueAction.action.criticalBearer.bearerLineage.seed ∧
      healthAppendInstalledRenewal.selected.selectedEvent = .health ∧
      healthAppendInstalledRenewal.payload.consumer.action =
        healthQueueAction.action ∧
      healthAppendInstalledRenewal.payload.disposition.update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt .health ∧
      healthAppendInstalledRenewal.payload.successor.targetCurrent =
        retainedSelectionNext
          (appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction) ∧
      IsEmpty (AppendedSelectionReplayAt tenureAppendTargetRoot
        healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction) :=
  ⟨rfl, generatedHealthQueueAppendSourceSeal.queueSuccession,
    generatedHealthQueueAppendReceiptCore.targetAppendCurrent,
    rfl, generatedHealthQueueAppendReceiptCore.selectedRenewal.1,
    generatedHealthQueueAppendReceiptCore.selectedRenewal.2.1,
    generatedHealthQueueAppendReceiptCore.selectedRenewal.2.2,
    generatedHealthQueueAppendReceiptCore.selectedRetainedSuccessor,
    generatedHealthQueueAppendReceiptCore.selectionReplay⟩

end
end M14SourceGeneratedSequentialHealthQueueAppend
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialHealthQueueAppend.generatedHealthQueueAppendAction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialHealthQueueAppend.healthQueueAppendActualActionCompilation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialHealthQueueAppend.sequentialHealthQueueAppend_directConsumer
