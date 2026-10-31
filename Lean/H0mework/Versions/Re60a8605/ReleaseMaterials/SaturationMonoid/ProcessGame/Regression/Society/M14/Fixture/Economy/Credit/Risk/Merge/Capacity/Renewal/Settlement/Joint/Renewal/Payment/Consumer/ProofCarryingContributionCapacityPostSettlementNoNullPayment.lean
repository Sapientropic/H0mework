import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Payment.Producer.SourceGeneratedContributionCapacityPostSettlementOccurrencePayment

/-!
# Direct consumer of post-settlement no-null payment

Every reachable post-settlement event has a payment before it has a paid
next.  The target occurrence is projected from the payment successor and is
the exact next root event; paid-next occurrences cannot be replayed across
indices.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityPostSettlementNoNullPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment.PostSettlementOccurrencePaymentAt

theorem contributionCapacityPostSettlementReachableCurrent_next_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
          index +
        1 =
      contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (index + 1) := by
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact]
  omega

/-- `NextPaidBy` is exactly the occurrence of the next reachable root event,
not a target field stored in payment. -/
theorem contributionCapacityPostSettlementNextPaidBy_is_nextRootEvent
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    HEq
      (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
        oldVisit sourceIndex index).nextPaidBy
      (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
        (index + 1)).occurrence := by
  have currentExact :=
    contributionCapacityPostSettlementReachableCurrent_next_exact oldVisit
      sourceIndex index
  cases currentExact
  rfl

/-- Existing heterogeneous occurrence carrier; no paid-next registry is
introduced. -/
def contributionCapacityPostSettlementPaidNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AnyContributionCapacityPostSettlementRenewalOccurrenceAt oldVisit
      sourceIndex :=
  let payment :=
    sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index
  ⟨payment.successor.targetCurrent, payment.nextPaidBy⟩

theorem contributionCapacityPostSettlementPaidNextOccurrences_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (contributionCapacityPostSettlementPaidNextOccurrenceAt oldVisit
        sourceIndex) := by
  intro left right occurrenceEquality
  have currentEquality := congrArg Sigma.fst occurrenceEquality
  change
    contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
          left +
        1 =
      contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
          right +
        1 at currentEquality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
  omega

/-- Neither the event-selected liability nor the successor token alone is a
payment.  The private payment constructor requires both in one exact event. -/
theorem bareWrite_liability_or_successor_cannot_retype_asPayment
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let rootEvent :=
    contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
      index
  let actualExit :=
    contributionCapacityPostSettlementActualExitOfRootEventAt oldVisit
      sourceIndex index rootEvent
  let liability :=
    contributionCapacityPostSettlementGeneratedExternalLiabilityOfRootEventAt
      oldVisit sourceIndex index rootEvent
  let payment :=
    sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index
  fail_if_success
    exact (liability : CanonicalPostSettlementOccurrencePaymentAt oldVisit
      sourceIndex index)
  fail_if_success
    exact (payment.write : CanonicalPostSettlementOccurrencePaymentAt oldVisit
      sourceIndex index)
  fail_if_success
    exact (payment.successor : CanonicalPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index)
  trivial

structure ProofCarryingContributionCapacityPostSettlementNoNullPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  everyPayment : ∀ index : Nat,
    Nonempty
      (CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex index)
  everyWholeLedgerSuccessor : ∀ index : Nat,
    let rootEvent :=
      contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
        index
    Nonempty (SourceNativeLedgerGeneratedSuccessorAt rootEvent.occurrence
      rootEvent.wholeLedgerWriteBack)
  everyWriteExact : ∀ index : Nat,
    let rootEvent :=
      contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
        index
    let payment :=
      sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
        oldVisit sourceIndex index
    payment.write = PLift.up rootEvent.occurrence.2.periodicExitGenerated
  everyCompilerWriteExact : ∀ index : Nat,
    let rootEvent :=
      contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
        index
    let payment :=
      sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
        oldVisit sourceIndex index
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile rootEvent.occurrence =
        .nativeWrite payment.write
  everyActualExitFromWrite : ∀ index : Nat,
    let payment :=
      sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
        oldVisit sourceIndex index
    contributionCapacityPostSettlementActualExitOfRootEventAt oldVisit
        sourceIndex index
        (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
          index) =
      Classical.choice payment.write.down
  everyEventGeneratedLiability : ∀ index : Nat,
    let rootEvent :=
      contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
        index
    PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex index
      rootEvent
      (contributionCapacityPostSettlementActualExitOfRootEventAt oldVisit
        sourceIndex index rootEvent)
  everyNextPaidByExact : ∀ index : Nat,
    HEq
      (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
        oldVisit sourceIndex index).nextPaidBy
      (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
        (index + 1)).occurrence
  paidNextOccurrencesInjective : Function.Injective
    (contributionCapacityPostSettlementPaidNextOccurrenceAt oldVisit
      sourceIndex)

theorem proofCarryingContributionCapacityPostSettlementNoNullPayment
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityPostSettlementNoNullPaymentAt oldVisit
      sourceIndex where
  everyPayment := fun index =>
    ⟨sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index⟩
  everyWholeLedgerSuccessor := fun index =>
    ⟨(sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index).successor⟩
  everyWriteExact := fun index =>
    (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index).writeExact
  everyCompilerWriteExact := fun index =>
    (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index).compilerWriteExact
  everyActualExitFromWrite := fun index =>
    (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index).actualExitFromWrite
  everyEventGeneratedLiability := fun index =>
    (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index).liability
  everyNextPaidByExact :=
    contributionCapacityPostSettlementNextPaidBy_is_nextRootEvent oldVisit
      sourceIndex
  paidNextOccurrencesInjective :=
    contributionCapacityPostSettlementPaidNextOccurrences_injective oldVisit
      sourceIndex

end
end M14ProofCarryingContributionCapacityPostSettlementNoNullPayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPostSettlementNoNullPayment.contributionCapacityPostSettlementNextPaidBy_is_nextRootEvent
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPostSettlementNoNullPayment.proofCarryingContributionCapacityPostSettlementNoNullPayment
