import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Continuation.Generic.SourceGeneratedCriticalActionAppendContinuation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.Generic.SourceGeneratedEssentialAccessCriticalActionCarrier

/-!
# Queue adapter for the carrier-native append continuation

The queue index is forgotten once, through the existing transparent carrier
adapter.  All temporal, authority and answered-selection structure is the
carrier-native continuation; this file preserves only the queue-facing names.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedQueueAppendContinuation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedEssentialAccessCriticalActionQueue
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedCriticalActionAppendContinuation

section

variable {SourceV : ConstructiveRoot.Vocabulary}
variable (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
variable {sourceCurrent : SourceV.Current}
variable (sourceOccurrence :
  sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    sourceCurrent)
variable {unit : ExactQueueUnit}
variable (prior : EssentialAccessCriticalSelectionCurrent)
variable (queueAction : QueueActionAt unit)

abbrev queueAppendTargetRoot :=
  criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction)

abbrev queueAppendRootVisitAt (depth : Nat) :=
  criticalActionAppendRootVisitAt sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction) depth

abbrev queueAppendTemporalVisitAt (depth : Nat) :=
  criticalActionAppendTemporalVisitAt sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction) depth

theorem queueAppendNextEqAt (depth : Nat) :
    ((queueAppendTargetRoot sourceRoot sourceOccurrence prior queueAction
      ).toAuthoritativeRoot.toRoot.evolutionAt
        (queueAppendRootVisitAt (sourceRoot := sourceRoot)
          (sourceOccurrence := sourceOccurrence) (prior := prior)
          (queueAction := queueAction) depth).current).nextCurrent? =
      some (queueAppendRootVisitAt (sourceRoot := sourceRoot)
        (sourceOccurrence := sourceOccurrence) (prior := prior)
        (queueAction := queueAction) (depth + 1)).current :=
  criticalActionAppendNextEqAt sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction) depth

@[simp] theorem queueAppendTemporalVisit_next_eq (depth : Nat) :
    (queueAppendTemporalVisitAt (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (queueAction := queueAction) depth).next
        (queueAppendNextEqAt (sourceRoot := sourceRoot)
          (sourceOccurrence := sourceOccurrence) (prior := prior)
          (queueAction := queueAction) depth) =
      queueAppendTemporalVisitAt (sourceRoot := sourceRoot)
        (sourceOccurrence := sourceOccurrence) (prior := prior)
        (queueAction := queueAction) (depth + 1) :=
  criticalActionAppendTemporalVisit_next_eq sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction) depth

@[simp] theorem queueAppendRootVisitAt_zero_current :
    (queueAppendRootVisitAt (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (queueAction := queueAction) 0).current =
        appendedCriticalSelectionCurrent prior queueAction :=
  criticalActionAppendRootVisitAt_zero_current sourceRoot sourceOccurrence
    prior (criticalActionCarrierOfQueueAction queueAction)

abbrev queueAppendEntryAt (depth : Nat) :=
  criticalActionAppendEntryAt depth

abbrev queueAppendAuthorityAt (depth : Nat) :=
  criticalActionAppendAuthorityAt sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction) depth

abbrev queueAppendAnswerFaceAt (selection : Fin 1) :=
  criticalActionAppendAnswerFaceAt sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction) selection

abbrev queueAppendAnswerConsumerAt (selection : Fin 1) :=
  criticalActionAppendAnswerConsumerAt sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction) selection

abbrev queueAppendAnsweredCompilationAt (selection : Fin 1) :=
  criticalActionAppendAnsweredCompilationAt sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction) selection

abbrev queueAppendInquiryStateAt (selection : Fin 1) :=
  criticalActionAppendInquiryStateAt sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction) selection

abbrev queueAppendPresentationAt (selection : Fin 1) :=
  criticalActionAppendPresentationAt sourceRoot sourceOccurrence prior
    (criticalActionCarrierOfQueueAction queueAction) selection

theorem queueAppendContinuation_directConsumer (selection : Fin 1) :
    (queueAppendInquiryStateAt (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (queueAction := queueAction) selection).compileInquiry () =
      SourceNativeInquiryCompilationAt.answered
        (queueAppendAnswerFaceAt (sourceRoot := sourceRoot)
          (sourceOccurrence := sourceOccurrence) (prior := prior)
          (queueAction := queueAction) selection)
        (queueAppendAnswerConsumerAt (sourceRoot := sourceRoot)
          (sourceOccurrence := sourceOccurrence) (prior := prior)
          (queueAction := queueAction) selection) :=
  criticalActionAppendContinuation_directConsumer sourceRoot sourceOccurrence
    prior (criticalActionCarrierOfQueueAction queueAction) selection

end
end
end M14SourceGeneratedQueueAppendContinuation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedQueueAppendContinuation.queueAppendAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedQueueAppendContinuation.queueAppendInquiryStateAt
