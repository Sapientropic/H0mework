import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.Generic.SourceGeneratedSequentialCriticalActionAppendTarget

/-!
# Queue adapter for the carrier-native append target

Queue actions enter the common gearbox only through the transparent dependent
carrier adapter.  This file preserves the queue-facing API used by the tenure,
health and platform fixtures; it owns no second target implementation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialQueueAppendTarget

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedEssentialAccessCriticalActionQueue
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open M14SourceGeneratedSequentialCriticalActionAppendTarget

abbrev sequentialQueueAppendSourceCarrier
    {unit : ExactQueueUnit} (queueAction : QueueActionAt unit) :
    SourceGeneratedEssentialAccessCriticalActionCarrier :=
  criticalActionCarrierOfQueueAction queueAction

abbrev sequentialQueueAppendSourceRoot
    {PredecessorV : ConstructiveRoot.Vocabulary}
    (predecessorRoot : SourceNativeLivingRootClosure NewN PredecessorV)
    {predecessorCurrent : PredecessorV.Current}
    (predecessorOccurrence :
      predecessorRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        predecessorCurrent)
    {sourceUnit : ExactQueueUnit}
    (sourcePrior : EssentialAccessCriticalSelectionCurrent)
    (sourceQueueAction : QueueActionAt sourceUnit) :=
  sequentialCriticalActionAppendSourceRoot predecessorRoot
    predecessorOccurrence sourcePrior
      (sequentialQueueAppendSourceCarrier sourceQueueAction)

abbrev sequentialQueueAppendTargetRoot
    {PredecessorV : ConstructiveRoot.Vocabulary}
    (predecessorRoot : SourceNativeLivingRootClosure NewN PredecessorV)
    {predecessorCurrent : PredecessorV.Current}
    (predecessorOccurrence :
      predecessorRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        predecessorCurrent)
    {sourceUnit : ExactQueueUnit}
    (sourcePrior : EssentialAccessCriticalSelectionCurrent)
    (sourceQueueAction : QueueActionAt sourceUnit)
    (sourceVisit : SourceNativeTemporalVisitAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction).toAuthoritativeRoot.toLedgerRoot)
    (prior : EssentialAccessCriticalSelectionCurrent)
    {unit : ExactQueueUnit} (queueAction : QueueActionAt unit)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) :=
  sequentialCriticalActionAppendTargetRoot predecessorRoot
    predecessorOccurrence sourcePrior
    (sequentialQueueAppendSourceCarrier sourceQueueAction) sourceVisit prior
    (sequentialQueueAppendSourceCarrier queueAction) sourceEvent

abbrev SequentialQueueAppendReceiptCoreAt
    {PredecessorV : ConstructiveRoot.Vocabulary}
    (predecessorRoot : SourceNativeLivingRootClosure NewN PredecessorV)
    {predecessorCurrent : PredecessorV.Current}
    (predecessorOccurrence :
      predecessorRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        predecessorCurrent)
    {sourceUnit : ExactQueueUnit}
    (sourcePrior : EssentialAccessCriticalSelectionCurrent)
    (sourceQueueAction : QueueActionAt sourceUnit)
    (sourceVisit : SourceNativeTemporalVisitAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction).toAuthoritativeRoot.toLedgerRoot)
    (sourceEntry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport)
    (prior : EssentialAccessCriticalSelectionCurrent)
    {unit : ExactQueueUnit} (queueAction : QueueActionAt unit)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) :=
  SequentialCriticalActionAppendReceiptCoreAt predecessorRoot
    predecessorOccurrence sourcePrior
    (sequentialQueueAppendSourceCarrier sourceQueueAction) sourceVisit
    sourceEntry prior (sequentialQueueAppendSourceCarrier queueAction)
    sourceEvent

theorem sequentialQueueAppendReceiptCoreAt
    {PredecessorV : ConstructiveRoot.Vocabulary}
    (predecessorRoot : SourceNativeLivingRootClosure NewN PredecessorV)
    {predecessorCurrent : PredecessorV.Current}
    (predecessorOccurrence :
      predecessorRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        predecessorCurrent)
    {sourceUnit : ExactQueueUnit}
    (sourcePrior : EssentialAccessCriticalSelectionCurrent)
    (sourceQueueAction : QueueActionAt sourceUnit)
    (sourceVisit : SourceNativeTemporalVisitAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction).toAuthoritativeRoot.toLedgerRoot)
    (sourceEntry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport)
    (prior : EssentialAccessCriticalSelectionCurrent)
    {unit : ExactQueueUnit} (queueAction : QueueActionAt unit)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction).toAuthoritativeRoot.toLedgerRoot
      sourceVisit)
    (priorFromSource : prior = sourceVisit.current)
    (sourceEntryExact : sourceEntry = newRevisedEntry) :
    SequentialQueueAppendReceiptCoreAt predecessorRoot predecessorOccurrence
      sourcePrior sourceQueueAction sourceVisit sourceEntry prior queueAction
      sourceEvent :=
  sequentialCriticalActionAppendReceiptCoreAt predecessorRoot
    predecessorOccurrence sourcePrior
    (sequentialQueueAppendSourceCarrier sourceQueueAction) sourceVisit
    sourceEntry prior (sequentialQueueAppendSourceCarrier queueAction)
    sourceEvent priorFromSource sourceEntryExact

def sequentialQueueAppendTargetAt
    {PredecessorV : ConstructiveRoot.Vocabulary}
    (predecessorRoot : SourceNativeLivingRootClosure NewN PredecessorV)
    {predecessorCurrent : PredecessorV.Current}
    (predecessorOccurrence :
      predecessorRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        predecessorCurrent)
    {sourceUnit : ExactQueueUnit}
    (sourcePrior : EssentialAccessCriticalSelectionCurrent)
    (sourceQueueAction : QueueActionAt sourceUnit)
    (sourceVisit : SourceNativeTemporalVisitAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction).toAuthoritativeRoot.toLedgerRoot)
    (sourceEntry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport)
    (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction) sourceVisit sourceEntry)
    (prior : EssentialAccessCriticalSelectionCurrent)
    {unit : ExactQueueUnit} (queueAction : QueueActionAt unit)
    (priorFromSource : prior = sourceVisit.current)
    (sourceEntryExact : sourceEntry = newRevisedEntry)
    (SourceSealAt : (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) → Prop)
    (sourceSeal : ∀ sourceEvent, SourceSealAt sourceEvent)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction).toAuthoritativeRoot.toLedgerRoot
      sourceVisit) : SourceNativeSequentialActualActionTargetAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction) sourceVisit sourceEvent sourceEntry
      sourceAuthority :=
  sequentialCriticalActionAppendTargetAt predecessorRoot
    predecessorOccurrence sourcePrior
    (sequentialQueueAppendSourceCarrier sourceQueueAction) sourceVisit
    sourceEntry sourceAuthority prior
    (sequentialQueueAppendSourceCarrier queueAction) priorFromSource
    sourceEntryExact SourceSealAt sourceSeal sourceEvent

end
end M14SourceGeneratedSequentialQueueAppendTarget
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialQueueAppendTarget.sequentialQueueAppendReceiptCoreAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialQueueAppendTarget.sequentialQueueAppendTargetAt
