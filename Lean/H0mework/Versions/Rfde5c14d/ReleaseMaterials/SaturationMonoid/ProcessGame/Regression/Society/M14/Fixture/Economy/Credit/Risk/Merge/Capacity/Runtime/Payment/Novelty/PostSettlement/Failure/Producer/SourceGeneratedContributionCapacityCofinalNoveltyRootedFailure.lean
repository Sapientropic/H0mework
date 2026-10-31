import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Consumer.ProofCarryingContributionCapacityCofinalProductiveNovelty
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8Failure

/-!
# Cofinal novelty returns to the existing operational root failure

The post-root local ledger is empty and its law surface is `rootSemantic`, but
each rich Payment already carries an exact external payment occurrence in the
literal M9 joint root.  That root has the existing narrow operational theory
and the visit-polymorphic failure producer.  This file therefore restricts the
already paid novelty paths back to their exact external visits and consumes
the existing `failureFaceAt/rootedAt/cofaceAt`; it creates no new root,
failure mechanism, U7 calculus or revision court.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty

/-- Zero-field bridge that consumes one already generated cofinal novelty token.
All rooted-failure data remain projections of its two exact paid replays. -/
inductive SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary) :
    Type 31
  | private generated

def sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary) :
    SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
      novelty :=
  .generated

namespace SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  {novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary}
  (bridge : SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
    novelty)

def leftReplay := by
  cases bridge
  exact novelty.leftReplay

def rightReplay := by
  cases bridge
  exact novelty.rightReplay

def leftCurrent : Nat := (leftReplay bridge).2.current

def rightCurrent : Nat := (rightReplay bridge).2.current

def leftRootVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot :=
  rootVisitAt (leftCurrent bridge)

def rightRootVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot :=
  rootVisitAt (rightCurrent bridge)

def leftFailureFace :=
  failureFaceAt (leftRootVisit bridge)

def rightFailureFace :=
  failureFaceAt (rightRootVisit bridge)

def leftRootedFailure :=
  rootedAt (leftRootVisit bridge)

def rightRootedFailure :=
  rootedAt (rightRootVisit bridge)

def leftMinimalCoface :=
  cofaceAt (leftRootVisit bridge)

def rightMinimalCoface :=
  cofaceAt (rightRootVisit bridge)

theorem leftPaymentInstalled_exact :
    (leftReplay bridge).2.futureBirth.actualExit.paymentOccurrence.installed =
      installedUBIAt (leftCurrent bridge) :=
  (leftReplay bridge).2.futureBirth.externalLiability.paymentInstalledExact

theorem rightPaymentInstalled_exact :
    (rightReplay bridge).2.futureBirth.actualExit.paymentOccurrence.installed =
      installedUBIAt (rightCurrent bridge) :=
  (rightReplay bridge).2.futureBirth.externalLiability.paymentInstalledExact

/-- Exact external event, including the temporal visit, is the event used by
the existing joint-root failure face. -/
theorem leftPaymentRootOccurrence_exact :
    (leftReplay bridge).2.futureBirth.actualExit.paymentOccurrence.rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (leftRootVisit bridge)) :=
  (leftReplay bridge).2.futureBirth.externalLiability.paymentRootOccurrenceExact

theorem rightPaymentRootOccurrence_exact :
    (rightReplay bridge).2.futureBirth.actualExit.paymentOccurrence.rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (rightRootVisit bridge)) :=
  (rightReplay bridge).2.futureBirth.externalLiability.paymentRootOccurrenceExact

theorem leftRootedOccurrence_isPaymentOccurrence :
    (leftRootedFailure bridge).oldBoundaryEvolution.occurrence =
      ((leftReplay bridge).2.futureBirth.actualExit.paymentOccurrence
        ).rootOccurrence.occurrence := by
  rw [leftPaymentRootOccurrence_exact bridge]
  rfl

theorem rightRootedOccurrence_isPaymentOccurrence :
    (rightRootedFailure bridge).oldBoundaryEvolution.occurrence =
      ((rightReplay bridge).2.futureBirth.actualExit.paymentOccurrence
        ).rootOccurrence.occurrence := by
  rw [rightPaymentRootOccurrence_exact bridge]
  rfl

theorem leftFailureFace_isExistingVisitProducer :
    leftFailureFace bridge = failureFaceAt (leftRootVisit bridge) :=
  rfl

theorem rightFailureFace_isExistingVisitProducer :
    rightFailureFace bridge = failureFaceAt (rightRootVisit bridge) :=
  rfl

theorem rootedFailures_useExistingOperationalFailure :
    (leftRootedFailure bridge :
        RootedActualExpressibilityFailureAt jointRoot.toAuthoritativeRoot
          (.finite (leftRootVisit bridge)) U7
          RootInquiryU8CompletionRegression.failure) =
        rootedAt (leftRootVisit bridge) ∧
      (rightRootedFailure bridge :
        RootedActualExpressibilityFailureAt jointRoot.toAuthoritativeRoot
          (.finite (rightRootVisit bridge)) U7
          RootInquiryU8CompletionRegression.failure) =
        rootedAt (rightRootVisit bridge) :=
  ⟨rfl, rfl⟩

/-- The two same-visible novelty paths remain different exact external visits;
the rooted bridge does not collapse their occurrence identity. -/
theorem externalVisits_ne :
    (temporalVisitAt (leftCurrent bridge)) ≠
      temporalVisitAt (rightCurrent bridge) := by
  intro equality
  have currentEquality := temporalVisitAt_injective equality
  have authorityEquality := congrArg periodicActualServiceExitOccurrenceAt
    currentEquality
  exact (novelty.kernelPair.authority_ne) authorityEquality

theorem bothRootedFailuresGenerated :
    Nonempty
        (RootedActualExpressibilityFailureAt jointRoot.toAuthoritativeRoot
          (.finite (leftRootVisit bridge)) U7
          RootInquiryU8CompletionRegression.failure) ∧
      Nonempty
        (RootedActualExpressibilityFailureAt jointRoot.toAuthoritativeRoot
          (.finite (rightRootVisit bridge)) U7
          RootInquiryU8CompletionRegression.failure) :=
  ⟨⟨leftRootedFailure bridge⟩, ⟨rightRootedFailure bridge⟩⟩

theorem bothMinimalCofacesGenerated :
    Nonempty (GeneratedMinimalCofaceAt (leftRootedFailure bridge)) ∧
      Nonempty (GeneratedMinimalCofaceAt (rightRootedFailure bridge)) :=
  ⟨⟨leftMinimalCoface bridge⟩, ⟨rightMinimalCoface bridge⟩⟩

end SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt

/-- Pointwise cofinal rooted-failure restriction.  No family of failures is
stored in the root or in the result. -/
theorem contributionCapacityCofinalNovelty_generatesExistingRootedFailure
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ∀ boundary : Nat,
      let novelty :=
        sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
          sourceIndex boundary
      Nonempty
        (SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
          novelty) :=
  fun boundary =>
    ⟨sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
      (sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary)⟩

theorem cofinalNoveltyRootedFailure_hasNoCallerFailureOrRevision
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : True := by
  let novelty :=
    sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary
  let bridge :=
    sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
  fail_if_success exact bridge.failure
  fail_if_success exact bridge.face
  fail_if_success exact bridge.coface
  fail_if_success exact bridge.revision
  fail_if_success exact bridge.recoveryCourt
  fail_if_success exact bridge.targetRoot
  fail_if_success exact bridge.future
  fail_if_success exact bridge.registry
  trivial

end
end M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure.sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure.SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt.leftRootedOccurrence_isPaymentOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure.SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt.bothMinimalCofacesGenerated
