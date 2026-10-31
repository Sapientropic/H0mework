import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Producer.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation

/-!
# Proof-carrying consumer of the cross-occurrence legislation span

This certificate consumes one generated span from the rooted observer
submission to the distinct external Payment.  It retains the source-local
empty-ledger no-go, exact external liability, Payment-side PCL consumer,
literal augmented U8 core and runtime consumption.  The forbidden occurrence
collapse and the forbidden section back to a local legislation bundle are
both empty.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Renewal Legislation
open M9ProofCarryingRenewalInquiryRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open UniversalRootGrammar

structure ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (transport :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary) : Prop where
  private mk ::
  sourceExactEvent :
    (sourceSubmission transport).exactEvent = (replay transport).rootEvent
  sourceRootedAuthority :
    Nonempty
      (SourceNativeObserverConsumerRootedAuthorityAt
        (sourceSubmission transport))
  sourceLocalLegislationEmpty :
    IsEmpty
      (CanonicalSubmissionLocalLegislationAt oldVisit sourceIndex boundary)
  sourceTargetOccurrencesDistinct :
    Sum.inl (sourceSubmission transport).exactEvent ≠
      Sum.inr (targetPaymentOccurrence transport).rootOccurrence
  externalSourceOwnedResidual :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership
  externalRootConsumer :
    Nonempty
      (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
        (replay transport).futureBirth.actualExit)
  targetPaymentRootOccurrenceExact :
    (targetPaymentOccurrence transport).rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (oldRootVisitAt oldVisit sourceIndex boundary))
  targetEntryAuthority : Nonempty
    (SourceNativeLivingTemporalCausalEntryAuthorityAt jointRoot
      (.finite (oldRootVisitAt oldVisit sourceIndex boundary))
      (targetEntry transport))
  targetPaymentAndLegislationShareRow : HEq
    (targetPaymentOccurrence transport).installed.payload.sourceEntry
    (sourceInstalled (targetExecution transport)).payload.sourceEntry
  targetLegislation :
    Nonempty (TargetLegislationAt transport)
  targetIndependentConsumer :
    Nonempty (TargetLegislationConsumerAt transport)
  targetLegislationOccurrenceIsPaymentOccurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt
      (M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.runtime
        (targetExecution transport)) 0
      ).1.state.base.root.toAuthoritativeRoot.toLedgerRoot
        |>.exactTemporalCausalEventAt
          (sourceGeneratedRuntimeInquiryCoordinateAt
            (M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.runtime
              (targetExecution transport)) 0).1.state.base.visit)
    (targetPaymentOccurrence transport).rootOccurrence
  targetCoreExact :
    (targetRevolutionaryConsumption transport).1.core =
      generatedU8CoreAt oldVisit sourceIndex boundary
  targetRuntimeConsumesCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      (generatedU8CoreAt oldVisit sourceIndex boundary)
      (runtimeAt oldVisit sourceIndex boundary) 0
  noLocalLegislationSection :
    IsEmpty
      (ProofCarryingPostSettlementObserverSubmissionFinalAuthorityAt
          oldVisit sourceIndex boundary →
        CanonicalSubmissionLocalLegislationAt oldVisit sourceIndex boundary)
  occurrenceCollapseEmpty :
    IsEmpty (IllegalCollapsedExternalPaymentLegislationAt transport)

/-- Direct consumer generated only from the source-produced span. -/
theorem proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (transport :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary) :
    ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislationAt
      transport where
  sourceExactEvent := sourceExactEvent_isReplayPostRootEvent transport
  sourceRootedAuthority := sourceRootedAuthority transport
  sourceLocalLegislationEmpty := sourceLocalLegislation_isEmpty transport
  sourceTargetOccurrencesDistinct := sourceTargetOccurrencesDistinct transport
  externalSourceOwnedResidual :=
    (externalLiability transport).sourceOwnedResidual
  externalRootConsumer :=
    (externalLiability transport).rootConsumer
  targetPaymentRootOccurrenceExact :=
    targetPaymentRootOccurrenceExact transport
  targetEntryAuthority := ⟨targetEntryAuthority transport⟩
  targetPaymentAndLegislationShareRow :=
    targetPaymentAndLegislation_shareRow transport
  targetLegislation := ⟨targetLegislation transport⟩
  targetIndependentConsumer := ⟨targetConsumer transport⟩
  targetLegislationOccurrenceIsPaymentOccurrence :=
    targetLegislationOccurrence_isPaymentOccurrence transport
  targetCoreExact := targetCore_isAugmentedCore transport
  targetRuntimeConsumesCore :=
    targetRuntimeConsumesAugmentedCore transport
  noLocalLegislationSection :=
    externalObserverLegislation_hasNoLocalSection oldVisit sourceIndex boundary
  occurrenceCollapseEmpty :=
    illegalCollapsedExternalPaymentLegislation_isEmpty transport

/-- Canonical closed span and its independent proof-carrying consumer. -/
abbrev AnyProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { transport :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary //
    ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislationAt
      transport }

def canonicalProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AnyProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary :=
  let transport :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary
  ⟨transport,
    proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
      transport⟩

end
end M14ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation.proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation.canonicalProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislationAt
