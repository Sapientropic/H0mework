import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Platform.Source.SourceGeneratedPlatformQueueActionAtHealthRoot
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.Generic.SourceGeneratedSequentialQueueAppendProgram

/-! # Platform queue append target specialization -/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPlatformQueueAppendTarget

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Power
open M10OccurrenceCapacityProcessFixture
open M14EssentialAccessRelationFixture
open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedHealthQueueActionAtTenureRoot
open M14SourceGeneratedHealthQueueAppendTarget
open M14SourceGeneratedSequentialHealthQueueAppend
open M14SourceGeneratedHealthQueueAppendContinuation
open M14SourceGeneratedPlatformQueueActionAtHealthRoot
open M14SourceGeneratedSequentialQueueAppendTarget

structure PlatformQueueAppendSourceSealAt
    (exactSource : ExactTemporalCausalRootEventAt
      healthAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (healthAppendTemporalVisitAt 1)) : Prop where
  sourceCanonical : exactSource = platformAppendExactEvent
  sourceTether : sourceGeneratedPlatformQueueActionAtHealthRoot.exactSource =
    platformAppendExactEvent
  priorRetained : platformAppendPrior = retainedSelectionNext
    (appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction)
  queueSuccession : SourceGeneratedQueueCriticalActionSuccessorAt
    middleExactUnit recurrentExactUnit
  noFiniteQueueSuccessor : IsEmpty RecurrentQueueCriticalActionSuccessorAt
  inheritedUBI : HEq
    sourceGeneratedPlatformQueueActionAtHealthRoot.inheritedUBIPayload.consumer
    sourceGeneratedUBIRootRestriction
  healthInstalledEvent : healthAppendInstalledRenewal.selected.selectedEvent =
    EssentialAccessEvent.health
  healthInstalledAction : healthAppendInstalledRenewal.payload.consumer.action =
    healthQueueAction.action
  healthInstalledUpdate : healthAppendInstalledRenewal.payload.disposition.update =
    sourceGeneratedEssentialAccessCriticalActualUpdateAt .health
  healthReplayEmpty : IsEmpty (AppendedSelectionReplayAt tenureAppendTargetRoot
    healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction)
  recurrentActionSeed :
    (sourceGeneratedPlatformQueueActionAtHealthRoot.queueAction.action
      ).criticalBearer.bearerLineage.seed = exactEssentialAccessSeed .platform
  recurrentBearer :
    (sourceGeneratedPlatformQueueActionAtHealthRoot.queueAction.action
      ).criticalBearer.commonBearer =
        (criticalRelationObligation essentialAccessCriticalBearerOf
          .platform).bearer

theorem platformQueueAppendSourceSealAt
    (exactSource : ExactTemporalCausalRootEventAt
      healthAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (healthAppendTemporalVisitAt 1)) :
    PlatformQueueAppendSourceSealAt exactSource := by
  rw [exactSource.eq_generated]
  exact
    { sourceCanonical := rfl
      sourceTether := rfl
      priorRetained := platformAppendPrior_exact
      queueSuccession := middleToRecurrentQueueCriticalAction
      noFiniteQueueSuccessor := recurrentQueueCriticalActionSuccessor_isEmpty
      inheritedUBI :=
        sourceGeneratedPlatformQueueActionAtHealthRoot.inheritedUBIConsumerExact
      healthInstalledEvent := generatedHealthQueueAppendReceiptCore.selectedRenewal.1
      healthInstalledAction :=
        generatedHealthQueueAppendReceiptCore.selectedRenewal.2.1
      healthInstalledUpdate :=
        generatedHealthQueueAppendReceiptCore.selectedRenewal.2.2
      healthReplayEmpty := generatedHealthQueueAppend_selectionReplay_isEmpty
      recurrentActionSeed :=
        sourceGeneratedPlatformQueueActionAtHealthRoot.actionSeedExact
      recurrentBearer := by
        rw [sourceGeneratedPlatformQueueActionAtHealthRoot.queueActionExact]
        exact (sourceGeneratedEssentialAccessCriticalActualUpdateAt
          .platform).bearerCommutes }

def platformAppendTargetRoot := sequentialQueueAppendTargetRoot
  tenureAppendTargetRoot healthAppendExactEvent.occurrence healthAppendPrior
    healthQueueAction (healthAppendTemporalVisitAt 1) platformAppendPrior
      platformQueueAction platformAppendExactEvent

def platformQueueAppendTargetAt
    (exactSource : ExactTemporalCausalRootEventAt
      healthAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (healthAppendTemporalVisitAt 1)) :
    SourceNativeSequentialActualActionTargetAt healthAppendTargetRoot
      (healthAppendTemporalVisitAt 1) exactSource
      sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntry
      sourceGeneratedPlatformQueueActionAtHealthRoot.sourceAuthority :=
  sequentialQueueAppendTargetAt tenureAppendTargetRoot
    healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction
    (healthAppendTemporalVisitAt 1)
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntry
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceAuthority
    platformAppendPrior platformQueueAction rfl
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntryExact
    PlatformQueueAppendSourceSealAt platformQueueAppendSourceSealAt exactSource

@[simp] theorem platformQueueAppendTarget_root_exact :
    (platformQueueAppendTargetAt platformAppendExactEvent).targetRoot =
      appendLivingRoot healthAppendTargetRoot
        platformAppendExactEvent.occurrence platformAppendPrior
          platformQueueAction :=
  rfl

@[simp] theorem platformQueueAppendTarget_current_exact :
    (platformQueueAppendTargetAt platformAppendExactEvent
      ).firstSuccessor.targetCurrent =
      appendedCriticalSelectionCurrent platformAppendPrior
        platformQueueAction := by
  change appendNativeTarget platformAppendPrior platformQueueAction
    platformAppendPrior = _
  exact appendNativeTarget_initial platformAppendPrior platformQueueAction

end
end M14SourceGeneratedPlatformQueueAppendTarget
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformQueueAppendTarget.platformQueueAppendSourceSealAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformQueueAppendTarget.platformQueueAppendTargetAt
