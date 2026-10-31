import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Health.Source.SourceGeneratedHealthQueueActionAtTenureRoot
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.Generic.SourceGeneratedSequentialQueueAppendProgram

/-! # Health queue append target specialization -/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedHealthQueueAppendTarget

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Power
open M10OccurrenceCapacityProcessFixture
open M14EssentialAccessRelationFixture
open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedTenureQueueActionAtRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedSequentialTenureQueueAppend
open M14SourceGeneratedTenureQueueAppendContinuation
open M14SourceGeneratedHealthQueueActionAtTenureRoot
open M14SourceGeneratedSequentialQueueAppendTarget

structure HealthQueueAppendSourceSealAt
    (exactSource : ExactTemporalCausalRootEventAt
      tenureAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (tenureAppendTemporalVisitAt 1)) : Prop where
  sourceCanonical : exactSource = healthAppendExactEvent
  sourceTether : sourceGeneratedHealthQueueActionAtTenureRoot.exactSource =
    healthAppendExactEvent
  priorRetained : healthAppendPrior = retainedSelectionNext
    (appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction)
  queueSuccession : SourceGeneratedQueueCriticalActionSuccessorAt
    firstExactUnit middleExactUnit
  inheritedUBI : HEq
    sourceGeneratedHealthQueueActionAtTenureRoot.inheritedUBIPayload.consumer
    sourceGeneratedUBIRootRestriction
  tenureInstalledEvent : tenureAppendInstalledRenewal.selected.selectedEvent =
    EssentialAccessEvent.tenure
  tenureInstalledAction : tenureAppendInstalledRenewal.payload.consumer.action =
    tenureQueueAction.action
  tenureInstalledUpdate : tenureAppendInstalledRenewal.payload.disposition.update =
    sourceGeneratedEssentialAccessCriticalActualUpdateAt .tenure
  tenureReplayEmpty : IsEmpty (AppendedSelectionReplayAt revisedLivingRoot
    revisedDepthTwoEvent.occurrence tenureAppendPrior tenureQueueAction)
  middleActionSeed :
    (sourceGeneratedHealthQueueActionAtTenureRoot.queueAction.action
      ).criticalBearer.bearerLineage.seed = exactEssentialAccessSeed .health
  middleBearer :
    (sourceGeneratedHealthQueueActionAtTenureRoot.queueAction.action
      ).criticalBearer.commonBearer =
        (criticalRelationObligation essentialAccessCriticalBearerOf .health).bearer

theorem healthQueueAppendSourceSealAt
    (exactSource : ExactTemporalCausalRootEventAt
      tenureAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (tenureAppendTemporalVisitAt 1)) :
    HealthQueueAppendSourceSealAt exactSource := by
  rw [exactSource.eq_generated]
  exact
    { sourceCanonical := rfl
      sourceTether := rfl
      priorRetained := healthAppendPrior_exact
      queueSuccession := firstToMiddleQueueCriticalAction
      inheritedUBI :=
        sourceGeneratedHealthQueueActionAtTenureRoot.inheritedUBIConsumerExact
      tenureInstalledEvent := generatedTenureQueueAppendReceiptProvenance.selectedEvent
      tenureInstalledAction := generatedTenureQueueAppendReceiptProvenance.selectedAction
      tenureInstalledUpdate := generatedTenureQueueAppendReceiptProvenance.selectedUpdate
      tenureReplayEmpty := appendedSelectionReplay_isEmpty revisedLivingRoot
        revisedDepthTwoEvent.occurrence tenureAppendPrior tenureQueueAction
      middleActionSeed :=
        sourceGeneratedHealthQueueActionAtTenureRoot.actionSeedExact
      middleBearer := by
        rw [sourceGeneratedHealthQueueActionAtTenureRoot.queueActionExact]
        exact (sourceGeneratedEssentialAccessCriticalActualUpdateAt
          .health).bearerCommutes }

def healthAppendTargetRoot := sequentialQueueAppendTargetRoot
  revisedLivingRoot revisedDepthTwoEvent.occurrence tenureAppendPrior
    tenureQueueAction (tenureAppendTemporalVisitAt 1) healthAppendPrior
      healthQueueAction healthAppendExactEvent

def healthQueueAppendTargetAt
    (exactSource : ExactTemporalCausalRootEventAt
      tenureAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (tenureAppendTemporalVisitAt 1)) :
    SourceNativeSequentialActualActionTargetAt tenureAppendTargetRoot
      (tenureAppendTemporalVisitAt 1) exactSource
      sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntry
      sourceGeneratedHealthQueueActionAtTenureRoot.sourceAuthority :=
  sequentialQueueAppendTargetAt revisedLivingRoot
    revisedDepthTwoEvent.occurrence tenureAppendPrior tenureQueueAction
    (tenureAppendTemporalVisitAt 1)
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntry
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceAuthority
    healthAppendPrior healthQueueAction rfl
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntryExact
    HealthQueueAppendSourceSealAt healthQueueAppendSourceSealAt exactSource

@[simp] theorem healthQueueAppendTarget_root_exact :
    (healthQueueAppendTargetAt healthAppendExactEvent).targetRoot =
      appendLivingRoot tenureAppendTargetRoot
        healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction :=
  rfl

@[simp] theorem healthQueueAppendTarget_current_exact :
    (healthQueueAppendTargetAt healthAppendExactEvent
      ).firstSuccessor.targetCurrent =
      appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction := by
  change appendNativeTarget healthAppendPrior healthQueueAction
    healthAppendPrior = _
  exact appendNativeTarget_initial healthAppendPrior healthQueueAction

end
end M14SourceGeneratedHealthQueueAppendTarget
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthQueueAppendTarget.healthQueueAppendSourceSealAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthQueueAppendTarget.healthQueueAppendTargetAt
