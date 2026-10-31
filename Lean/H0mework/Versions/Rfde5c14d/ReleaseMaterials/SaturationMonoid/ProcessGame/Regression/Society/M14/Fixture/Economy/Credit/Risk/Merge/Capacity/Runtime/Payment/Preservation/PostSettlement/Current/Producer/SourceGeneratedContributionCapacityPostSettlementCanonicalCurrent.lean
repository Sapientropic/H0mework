import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Channel.Consumer.ProofCarryingContributionCapacityPostSettlementChannelFamily
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Payment.Consumer.ProofCarryingContributionCapacityPostSettlementNoNullPayment

/-!
# Source-generated canonical post-settlement current

One reachable post-root current regenerates its exact event, native payment,
whole-ledger write, external liability, bearer exit, future birth and every
existing essential-access channel consumer.  The token has no fields: callers
cannot supply a target, coverage proof, normalizer, observer label or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open Observer
open M3FiniteExchangeFixture
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14ProofCarryingContributionCapacityPostSettlementNoNullPayment

def contributionCapacityPostSettlementCanonicalCurrentDepthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Nat :=
  contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
    index

/-- A current whose complete installed authority is regenerated from the exact
post-root occurrence at `index`. -/
inductive SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 23
  | private canonical

def sourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
      oldVisit sourceIndex index :=
  .canonical

namespace SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (current :
    SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
      oldVisit sourceIndex index)

theorem eq_canonical :
    current =
      sourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
        oldVisit sourceIndex index := by
  cases current
  rfl

def rootEvent := by
  cases current
  exact contributionCapacityPostSettlementExactRootEventAt oldVisit
    sourceIndex index

def actualExit : PeriodicActualServiceExitAt
    (contributionCapacityPostSettlementCanonicalCurrentDepthAt oldVisit
      sourceIndex index) := by
  cases current
  exact contributionCapacityPostSettlementActualExitOfRootEventAt oldVisit
    sourceIndex index
    (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
      index)

def payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
    index := by
  cases current
  exact sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
    oldVisit sourceIndex index

def wholeLedgerWriteBack := (rootEvent current).wholeLedgerWriteBack

def successor := (payment current).successor

def externalLiability := (payment current).liability

def macroFutureBirth :
    SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index := by
  cases current
  exact sourceGeneratedContributionCapacityPostSettlementFutureBirthAt
    oldVisit sourceIndex index

def bearerExit := (macroFutureBirth current).bearerExit

def consumedChannel (channel : EssentialAccessChannel) :
    ConsumedContributionCapacityPostSettlementChannelAt oldVisit sourceIndex
      index channel := by
  cases current
  exact proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
    sourceIndex index channel

def nextPaidBy := (payment current).nextPaidBy

theorem eventOccurrence_exact :
    (rootEvent current).occurrence =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementCanonicalCurrentDepthAt oldVisit
          sourceIndex index) :=
  rfl

theorem compilerWrite_exact :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile (rootEvent current).occurrence =
      .nativeWrite (payment current).write :=
  (payment current).compilerWriteExact

theorem actualExit_fromPaymentWrite :
    actualExit current = Classical.choice (payment current).write.down :=
  (payment current).actualExitFromWrite

theorem localLedger_isEmpty :
    IsEmpty
      (OpenResponsibilityAt (JointSettlementNAt oldVisit)
        (rootEvent current).occurrence.1) :=
  (payment current).occurrenceLocalLedgerEmpty

theorem externalPaymentAndConsumer_nonempty :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (actualExit current)) := by
  have actualExitEq : actualExit current =
      contributionCapacityPostSettlementActualExitOfRootEventAt oldVisit
        sourceIndex index (rootEvent current) := by
    exact Subsingleton.elim _ _
  constructor
  · exact (externalLiability current).sourceOwnedResidual
  · cases actualExitEq
    exact (externalLiability current).rootConsumer

theorem bearerExitPayment_exact :
    (bearerExit current).existingPaymentOccurrence =
      (actualExit current).paymentOccurrence := by
  have actualExitEq : (macroFutureBirth current).actualExit =
      actualExit current := Subsingleton.elim _ _
  rw [← actualExitEq]
  exact (macroFutureBirth current).bearerExitPayment_exact

theorem bearerExitService_exact :
    (bearerExit current).existingActualSettlement =
      (actualExit current).actualSettlement := by
  have actualExitEq : (macroFutureBirth current).actualExit =
      actualExit current := Subsingleton.elim _ _
  rw [← actualExitEq]
  exact (macroFutureBirth current).bearerExitService_exact

theorem everyChannel_consumed :
    ∀ channel : EssentialAccessChannel,
      Nonempty
        (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
          sourceIndex index channel) :=
  fun channel =>
    ⟨proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex index channel⟩

theorem channelAudit (channel : EssentialAccessChannel) :
    let consumed := consumedChannel current channel
    (consumed.2.relationWitnessReturn).1.actor
          essentialAccessRelationCompiler = channelActor channel ∧
      essentialAccessRelationCompiler.relationOf
          (consumed.2.relationWitnessReturn).1 = channelRelation channel ∧
      consumed.2.rootReadCarrier.existingPaymentOccurrence =
        consumed.1.actualExit.paymentOccurrence ∧
      consumed.2.rootReadCarrier.existingActualSettlement =
        consumed.1.actualExit.actualSettlement ∧
      consumed.1.actualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes ∧
      consumed.2.actualNext =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (contributionCapacityPostSettlementCanonicalCurrentDepthAt oldVisit
              sourceIndex index +
            1) := by
  cases current
  exact proofCarryingContributionCapacityPostSettlement_channelAuditAt oldVisit
    sourceIndex index channel

theorem protectedInterest_noChannelSection :
    ¬ ∃ reconstruct : M3FiniteExchangeFixture.V.ProtectedInterest →
        AnyContributionCapacityPostSettlementEssentialAccessChannelAt oldVisit
          sourceIndex index,
      Function.LeftInverse reconstruct
        (contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex index).forget :=
  contributionCapacityPostSettlementChannel_noOccurrenceReconstruction oldVisit
    sourceIndex index

theorem protectedInterest_noAuthorityFactorization :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex index)) :=
  contributionCapacityPostSettlementChannel_noAuthorityFactorization oldVisit
    sourceIndex index

/-- The current payment generates exactly the next root event. -/
theorem nextPaidBy_is_nextRootEvent :
    HEq (nextPaidBy current)
      (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
        (index + 1)).occurrence :=
  contributionCapacityPostSettlementNextPaidBy_is_nextRootEvent oldVisit
    sourceIndex index

end SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt

theorem contributionCapacityPostSettlementCanonicalCurrent_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let current :=
    sourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
      oldVisit sourceIndex index
  fail_if_success exact current.target
  fail_if_success exact current.coverage
  fail_if_success exact current.normalizer
  fail_if_success exact current.registry
  fail_if_success exact current.schedule
  fail_if_success exact current.future
  trivial

end
end M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent.sourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent.SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.channelAudit
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent.SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.nextPaidBy_is_nextRootEvent
