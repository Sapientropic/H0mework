import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.Generic.SourceGeneratedSequentialQueueAppendTarget
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.Generic.SourceGeneratedSequentialCriticalActionAppendProgram

/-! # Queue adapter for the carrier-native append program -/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialQueueAppendProgram

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedEssentialAccessCriticalActionQueue
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedSequentialQueueAppendTarget
open M14SourceGeneratedSequentialCriticalActionAppendProgram

def sequentialQueueAppendProgram
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
    (sourceSeal : ∀ sourceEvent, SourceSealAt sourceEvent) :
    SourceNativeSequentialActualActionProgramAt
      (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
        sourcePrior sourceQueueAction) sourceVisit sourceEntry
        sourceAuthority :=
  sequentialCriticalActionAppendProgram predecessorRoot predecessorOccurrence
    sourcePrior (sequentialQueueAppendSourceCarrier sourceQueueAction)
    sourceVisit sourceEntry sourceAuthority prior
    (sequentialQueueAppendSourceCarrier queueAction) priorFromSource
    sourceEntryExact SourceSealAt sourceSeal

def generatedSequentialQueueAppendAction
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
      sourceVisit) :=
  generatedSequentialCriticalActionAppendAction predecessorRoot
    predecessorOccurrence sourcePrior
    (sequentialQueueAppendSourceCarrier sourceQueueAction) sourceVisit
    sourceEntry sourceAuthority prior
    (sequentialQueueAppendSourceCarrier queueAction) priorFromSource
    sourceEntryExact SourceSealAt sourceSeal sourceEvent

def sequentialQueueAppendActualActionCompilation
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
      sourceVisit) : SourceNativeInquiryCompilationAt
    (sequentialQueueAppendSourceRoot predecessorRoot predecessorOccurrence
      sourcePrior sourceQueueAction) sourceVisit revisedInquiryU7
      revisedInquiryCalculus revisedInquiryTheory ()
      (ULift.up.{1, 0} ((sequentialQueueAppendSourceRoot predecessorRoot
        predecessorOccurrence sourcePrior sourceQueueAction).emitted
          sourceVisit.current)) sourceEntry sourceAuthority :=
  sequentialCriticalActionAppendActualActionCompilation predecessorRoot
    predecessorOccurrence sourcePrior
    (sequentialQueueAppendSourceCarrier sourceQueueAction) sourceVisit
    sourceEntry sourceAuthority prior
    (sequentialQueueAppendSourceCarrier queueAction) priorFromSource
    sourceEntryExact SourceSealAt sourceSeal sourceEvent

end
end M14SourceGeneratedSequentialQueueAppendProgram
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialQueueAppendProgram.generatedSequentialQueueAppendAction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialQueueAppendProgram.sequentialQueueAppendActualActionCompilation
