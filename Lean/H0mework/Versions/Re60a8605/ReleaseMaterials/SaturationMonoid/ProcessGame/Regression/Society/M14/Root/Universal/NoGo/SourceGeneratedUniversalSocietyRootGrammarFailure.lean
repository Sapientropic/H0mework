import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Universal.Producer.SourceGeneratedUniversalSocietyRootGrammar
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Lifecycle.NoGo.SourceGeneratedPaidExitLifecycleMaximumNoGo

/-!
# M14 full-capture search failure of the installed Society grammar

The search failure is the one classified continuation point already present
in the installed trace.  Its bearer is selected from the same emitted event,
then consumed by the existing post-settlement external-liability producer.
Search observes the actual whole-ledger write and generated next but cannot
write either one.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedUniversalSocietyRootGrammarFailure

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum
open M14SourceGeneratedPaidExitLifecycleMaximumNoGo
open M14SourceGeneratedUniversalSocietyRootGrammar

def universalSocietySearchFailureAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  (universalSocietyFullCaptureSearchFailureAuditAt oldVisit sourceIndex index
    ).failed

def universalSocietySearchActualExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PeriodicActualServiceExitAt
      (show Nat from
        (universalSocietyVisitAt oldVisit sourceIndex index).current) :=
  Classical.choice
    (universalSocietySearchFailureAt oldVisit sourceIndex index
      ).residualBearer.down

def universalSocietySearchRootConsumerAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
      (universalSocietySearchActualExitAt oldVisit sourceIndex index) :=
  Classical.choice
    (universalSocietySearchFailureAt oldVisit sourceIndex index).consumer.down

def universalSocietySearchAuditDispositionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PostSettlementFullCaptureAuditDispositionAt oldVisit sourceIndex
      ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
        (universalSocietyVisitAt oldVisit sourceIndex index).current)
      .fullCaptureSearch .bearerRoleIndependentContinuation
      (universalSocietySearchActualExitAt oldVisit sourceIndex index)
      (universalSocietySearchRootConsumerAt oldVisit sourceIndex index) :=
  Classical.choice
    (universalSocietySearchFailureAt oldVisit sourceIndex index
      ).disposition.down

theorem universalSocietySearchBearer_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    universalSocietySearchActualExitAt oldVisit sourceIndex index =
      Classical.choice
        ((universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).exactEvent.occurrence.2.periodicExitGenerated) :=
  rfl

theorem universalSocietySearchExternalLiabilityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
      (index + 1 + 1)
      (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
        ).exactEvent
      (universalSocietySearchActualExitAt oldVisit sourceIndex index) := by
  exact contributionCapacityPostSettlementGeneratedExternalLiabilityOfRootEventAt
    oldVisit sourceIndex (index + 1 + 1)
      (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
        ).exactEvent

theorem universalSocietyActualSearch_sameRootLedgerAndNext
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (universalSocietyActualGrammarAt oldVisit sourceIndex index).exactEvent =
        (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).exactEvent ∧
      (universalSocietyActualGrammarAt oldVisit sourceIndex index
          ).wholeLedgerWriteBack =
        (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).wholeLedgerWriteBack ∧
      (universalSocietyActualGrammarAt oldVisit sourceIndex index).generatedNext =
        (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).generatedNext :=
  ⟨rfl, rfl, rfl⟩

structure SourceGeneratedUniversalSocietyRootGrammarFailureAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 32 where
  private mk ::
  grammar : SourceGeneratedUniversalSocietyRootGrammarAt oldVisit sourceIndex
    index
  counterlife : ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit
    sourceIndex index
  failureAudit : SourceGeneratedFailedDependentFaceAuditAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index)
    .fullCaptureSearch
  failureAuditExact : failureAudit =
    universalSocietyFullCaptureSearchFailureAuditAt oldVisit sourceIndex index
  failedPointCannotPass : IsEmpty
    ((postSettlementSocietyVocabulary oldVisit sourceIndex).PassedAt
      ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
        (universalSocietyVisitAt oldVisit sourceIndex index).current)
      .fullCaptureSearch .bearerRoleIndependentContinuation)
  residualBearer : PeriodicActualServiceExitAt
    (show Nat from
      (universalSocietyVisitAt oldVisit sourceIndex index).current)
  residualBearerExact : residualBearer =
    universalSocietySearchActualExitAt oldVisit sourceIndex index
  sourceOwnedResidual :
    ContributionCapacityPostSettlementPaymentSourceOwnership
  rootConsumer :
    ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
      residualBearer
  auditDisposition : PostSettlementFullCaptureAuditDispositionAt oldVisit
    sourceIndex
    ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
      (universalSocietyVisitAt oldVisit sourceIndex index).current)
    .fullCaptureSearch .bearerRoleIndependentContinuation residualBearer
      rootConsumer
  externalLiability : PostSettlementGeneratedExternalLiabilityAt oldVisit
    sourceIndex (index + 1 + 1)
    (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
      ).exactEvent residualBearer
  searchNoActualWrite : IsEmpty
    (SourceNativeScenarioActualWriteAuthorityAt
      (postSettlementSocietyVocabulary oldVisit sourceIndex)
      .fullCaptureSearch)
  searchIdentityDisposition :
    @SourceNativeSearchIdentityDispositionAt
      (JointSettlementNAt oldVisit) (PostSettlementRenewalVAt oldVisit)
      (UniversalSocietyRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot.source
      (universalSocietyVisitAt oldVisit sourceIndex index).current
      ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
        (universalSocietyVisitAt oldVisit sourceIndex index).current)
  auditPreservesActualWriteBack :
    auditDisposition.applyToActualWriteBack
        ((universalSocietyActualGrammarAt oldVisit sourceIndex index
          ).wholeLedgerWriteBack) =
      (universalSocietyActualGrammarAt oldVisit sourceIndex index
        ).wholeLedgerWriteBack
  sameRootLedgerAndNext :
    (universalSocietyActualGrammarAt oldVisit sourceIndex index).exactEvent =
        (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).exactEvent ∧
      (universalSocietyActualGrammarAt oldVisit sourceIndex index
          ).wholeLedgerWriteBack =
        (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).wholeLedgerWriteBack ∧
      (universalSocietyActualGrammarAt oldVisit sourceIndex index).generatedNext =
        (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).generatedNext

def sourceGeneratedUniversalSocietyRootGrammarFailureAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit sourceIndex
      index := by
  let grammar :=
    sourceGeneratedUniversalSocietyRootGrammarAt oldVisit sourceIndex index
  let failureAudit :=
    universalSocietyFullCaptureSearchFailureAuditAt oldVisit sourceIndex index
  let failed := failureAudit.failed
  let bearer := universalSocietySearchActualExitAt oldVisit sourceIndex index
  let consumer :=
    universalSocietySearchRootConsumerAt oldVisit sourceIndex index
  exact
    { grammar := grammar
      counterlife := proofCarryingFullCapturePaidExitCounterlifeAt oldVisit
        sourceIndex index
      failureAudit := failureAudit
      failureAuditExact := rfl
      failedPointCannotPass := failed.passedEmpty
      residualBearer := bearer
      residualBearerExact := rfl
      sourceOwnedResidual := failed.sourceOwned
      rootConsumer := consumer
      auditDisposition :=
        universalSocietySearchAuditDispositionAt oldVisit sourceIndex index
      externalLiability :=
        universalSocietySearchExternalLiabilityAt oldVisit sourceIndex index
      searchNoActualWrite := grammar.searchHasNoActualWrite
      searchIdentityDisposition :=
        SourceGeneratedUniversalRootGrammarAt.searchIdentityDisposition
          (recognition := universalSocietyRecognitionAt oldVisit sourceIndex)
          (visit := universalSocietyVisitAt oldVisit sourceIndex index)
          (scenario := PostSettlementSocietyScenario.fullCaptureSearch)
          fullCaptureSearch_ne_actual
      auditPreservesActualWriteBack := rfl
      sameRootLedgerAndNext :=
        universalSocietyActualSearch_sameRootLedgerAndNext oldVisit
          sourceIndex index }

namespace SourceGeneratedUniversalSocietyRootGrammarFailureAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (failure : SourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit
    sourceIndex index)

include failure

theorem falselyReportedPass_isEmpty :
    IsEmpty ((postSettlementSocietyVocabulary oldVisit sourceIndex).PassedAt
      ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
        (universalSocietyVisitAt oldVisit sourceIndex index).current)
      .fullCaptureSearch .bearerRoleIndependentContinuation) :=
  failure.failedPointCannotPass

theorem residualBearerDeletion_isFalse :
    ¬ ExactFailedFaceResidualBearerDeletionAt failure.failureAudit.failed :=
  failedFaceResidualBearerDeletion_isFalse failure.failureAudit.failed

theorem sourceOwnershipDeletion_isFalse :
    ¬ ExactFailedFaceSourceOwnershipDeletionAt failure.failureAudit.failed :=
  failedFaceSourceOwnershipDeletion_isFalse failure.failureAudit.failed

theorem consumerDeletion_isFalse :
    ¬ ExactFailedFaceConsumerDeletionAt failure.failureAudit.failed :=
  failedFaceConsumerDeletion_isFalse failure.failureAudit.failed

theorem dispositionDeletion_isFalse :
    ¬ ExactFailedFaceDispositionDeletionAt failure.failureAudit.failed :=
  failedFaceDispositionDeletion_isFalse failure.failureAudit.failed

end SourceGeneratedUniversalSocietyRootGrammarFailureAt

end
end M14SourceGeneratedUniversalSocietyRootGrammarFailure
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedUniversalSocietyRootGrammarFailure.sourceGeneratedUniversalSocietyRootGrammarFailureAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedUniversalSocietyRootGrammarFailure.SourceGeneratedUniversalSocietyRootGrammarFailureAt.dispositionDeletion_isFalse
