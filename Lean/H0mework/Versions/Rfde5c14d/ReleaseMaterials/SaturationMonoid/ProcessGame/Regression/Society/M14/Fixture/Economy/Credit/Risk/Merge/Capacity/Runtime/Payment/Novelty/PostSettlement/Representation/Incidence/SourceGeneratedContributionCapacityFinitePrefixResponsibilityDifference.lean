import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Observer.SourceGeneratedContributionCapacityFinitePrefixAuthorityObserver
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Consumer.ProofCarryingContributionCapacityCofinalProductiveNovelty
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRoot

/-!
# Responsibility-relevant finite-prefix difference

One private source token binds the later finite-observer kernel pair to both
exact Payments, every essential-access witness return, the right external M9
Payment visit, its installed source row, source ownership and independent root
consumer.  The finite-representation failure downstream is indexed by this
token; a naked observer collision cannot inhabit that failure producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M9ProofCarryingRenewalInquiryRoot
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14ProofCarryingContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedContributionCapacityFinitePrefixAuthorityObserver

/-- Proof-relevant source incidence.  All payload is regenerated from its
indices; the constructor accepts no pair, failure, branch or future. -/
inductive SourceGeneratedFinitePrefixResponsibilityDifferenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 30
  | private generated

def sourceGeneratedFinitePrefixResponsibilityDifferenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit sourceIndex
      boundary :=
  .generated

namespace SourceGeneratedFinitePrefixResponsibilityDifferenceAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  (incidence : SourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit
    sourceIndex boundary)

theorem eq_generated :
    incidence =
      sourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit
        sourceIndex boundary := by
  cases incidence
  rfl

def novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary := by
  cases incidence
  exact sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
    sourceIndex boundary

def consumed :
    ConsumedContributionCapacityCofinalProductiveNoveltyAt oldVisit
      sourceIndex boundary := by
  cases incidence
  exact proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
    sourceIndex boundary

def finiteKernelPair : AuthorityKernelPair
    (finitePrefixReplayAuthorityObserverAt oldVisit sourceIndex boundary) := by
  cases incidence
  let novelty :=
    sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary
  exact
    { left := novelty.leftReplay
      right := novelty.rightReplay
      occurrence_ne := novelty.kernelPair.occurrence_ne
      visible_eq := by
        apply Prod.ext
        · exact finitePrefixHistorySlot_afterBoundary boundary 0 |>.trans
            (finitePrefixHistorySlot_afterBoundary boundary 1).symm
        · apply Fin.ext
          rfl
      authority_ne := novelty.kernelPair.authority_ne }

def leftReplay := (consumed incidence).2.leftReplay
def rightReplay := (consumed incidence).2.rightReplay
def leftPayment := (consumed incidence).2.leftPayment
def rightPayment := (consumed incidence).2.rightPayment
def leftPaidStep := (consumed incidence).2.leftPaidStep
def rightPaidStep := (consumed incidence).2.rightPaidStep

def rightCurrent : Nat := (rightReplay incidence).2.current

def rightRootVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot :=
  rootVisitAt (rightCurrent incidence)

def rightTemporalVisit : SourceNativeTemporalVisitAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite (rightRootVisit incidence)

def rightExactRootEvent : ExactTemporalCausalRootEventAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot
    (rightTemporalVisit incidence) :=
  jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
    (rightTemporalVisit incidence)

def rightActualExit := (rightReplay incidence).2.futureBirth.actualExit

def rightRootConsumer :
    ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
      (rightActualExit incidence) :=
  Classical.choice
    (rightReplay incidence).2.futureBirth.externalLiability.rootConsumer

@[simp] theorem leftReplay_index_exact :
    (leftReplay incidence).1 = boundary + 1 := by
  cases incidence
  rfl

@[simp] theorem rightReplay_index_exact :
    (rightReplay incidence).1 = boundary + 2 := by
  cases incidence
  rfl

theorem bothStrictlyLater :
    boundary < (leftReplay incidence).2.current ∧
      boundary < (rightReplay incidence).2.current :=
  (consumed incidence).2.bothStrictlyLater

/-- The left witness is already actual before the right Q occurrence opens
the representation inquiry. -/
theorem leftCurrent_lt_rightCurrent :
    (leftReplay incidence).2.current < (rightReplay incidence).2.current := by
  rw [(leftReplay incidence).2.current_exact,
    (rightReplay incidence).2.current_exact]
  change
    contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex +
        (boundary + 1) <
      contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex +
        (boundary + 2)
  omega

theorem actualPathsDifferent :
    (leftReplay incidence).2.actualPath ≠
      (rightReplay incidence).2.actualPath :=
  (consumed incidence).2.actualPathsDifferent

theorem sameRealNormalFormDifferentActualK :
    let observer :=
      contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex
    observer.forget (leftReplay incidence) =
        observer.forget (rightReplay incidence) ∧
      observer.authorityK (leftReplay incidence) ≠
        observer.authorityK (rightReplay incidence) :=
  (consumed incidence).2.sameRealNormalForm_differentActualK

theorem sameFinitePrefixVisibleDifferentK :
    let observer :=
      finitePrefixReplayAuthorityObserverAt oldVisit sourceIndex boundary
    observer.forget (leftReplay incidence) =
        observer.forget (rightReplay incidence) ∧
      observer.authorityK (leftReplay incidence) ≠
        observer.authorityK (rightReplay incidence) :=
  ⟨(finiteKernelPair incidence).visible_eq,
    (finiteKernelPair incidence).authority_ne⟩

theorem exactPaymentsConsumed :
    (leftPaidStep incidence).2.sourcePayment = leftPayment incidence ∧
      (rightPaidStep incidence).2.sourcePayment = rightPayment incidence :=
  (consumed incidence).2.exactPaymentsConsumed

def leftChannel (channel : EssentialAccessChannel) :=
  (consumed incidence).2.leftChannel channel

def rightChannel (channel : EssentialAccessChannel) :=
  (consumed incidence).2.rightChannel channel

theorem channelWitnessesReturnToEachSource
    (channel : EssentialAccessChannel) :
    ((consumed incidence).2.leftWitnessReturn channel).1.actor
          M14EssentialAccessRelationFixture.essentialAccessRelationCompiler =
        channelActor channel ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
          ((consumed incidence).2.leftWitnessReturn channel).1 =
        channelRelation channel ∧
      ((consumed incidence).2.rightWitnessReturn channel).1.actor
          M14EssentialAccessRelationFixture.essentialAccessRelationCompiler =
        channelActor channel ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
          ((consumed incidence).2.rightWitnessReturn channel).1 =
        channelRelation channel :=
  (consumed incidence).2.channelWitnessesReturnToEachSource channel

theorem channelPaymentsReturnToEachActualExit
    (channel : EssentialAccessChannel) :
    (leftChannel incidence channel).2.rootReadCarrier.existingPaymentOccurrence =
        (leftReplay incidence).2.futureBirth.actualExit.paymentOccurrence ∧
      (rightChannel incidence channel).2.rootReadCarrier.existingPaymentOccurrence =
        (rightReplay incidence).2.futureBirth.actualExit.paymentOccurrence :=
  (consumed incidence).2.channelPaymentsReturnToEachActualExit channel

theorem rightPaymentRootOccurrence_exact :
    (rightActualExit incidence).paymentOccurrence.rootOccurrence =
      rightExactRootEvent incidence :=
  (rightReplay incidence).2.futureBirth.externalLiability
    |>.paymentRootOccurrenceExact

theorem rightPaymentInstalled_exact :
    (rightActualExit incidence).paymentOccurrence.installed =
      installedUBIAt (rightCurrent incidence) :=
  (rightReplay incidence).2.futureBirth.externalLiability
    |>.paymentInstalledExact

theorem rightPaymentSourceEntry_exact :
    (rightActualExit incidence).paymentOccurrence.installed.payload.sourceEntry =
      RootInquiryU8CompletionRegression.entry := by
  calc
    (rightActualExit incidence).paymentOccurrence.installed.payload.sourceEntry =
        (installedUBIAt (rightCurrent incidence)).payload.sourceEntry :=
      congrArg (fun installed => installed.payload.sourceEntry)
        incidence.rightPaymentInstalled_exact
    _ = RootInquiryU8CompletionRegression.entry :=
      (periodicUBISourceAt (rightCurrent incidence)).sourceEntryExact

include incidence in
theorem sourceOwnedResidual :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership :=
  (rightReplay incidence).2.futureBirth.externalLiability.sourceOwnedResidual

theorem rootConsumerIsInstalled :
    Nonempty
      (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
        (rightActualExit incidence)) :=
  ⟨rightRootConsumer incidence⟩

end SourceGeneratedFinitePrefixResponsibilityDifferenceAt

end
end M14SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference.sourceGeneratedFinitePrefixResponsibilityDifferenceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference.SourceGeneratedFinitePrefixResponsibilityDifferenceAt.sameFinitePrefixVisibleDifferentK
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference.SourceGeneratedFinitePrefixResponsibilityDifferenceAt.rightPaymentRootOccurrence_exact
