import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Preservation.PostSettlement.Current.Producer.SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Coherence.ProofCarryingContributionCapacityNoDivergentPaidNext

/-!
# Canonical post-settlement paid step

An arbitrary existing payment at one exact post-root event generates its own
whole-ledger successor.  Proof-selection coherence identifies that successor's
`NextPaidBy` with the exact next root event, whose canonical-current token then
regenerates every mandatory installed face.  No target current, coverage proof
or next is accepted as a premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment.PostSettlementOccurrencePaymentAt
open M14ProofCarryingContributionCapacityPostSettlementNoNullPayment
open M14ProofCarryingContributionCapacityNoDivergentPaidNext
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent

/-- One payment-indexed source step.  The payment is the sole public index;
the target canonical current is regenerated internally. -/
inductive SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index) : Type 24
  | private paid

def sourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index) :
    SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
      oldVisit sourceIndex index payment :=
  .paid

namespace SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  {payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
    index}
  (step : SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
    oldVisit sourceIndex index payment)

theorem eq_paid :
    step =
      sourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex index payment := by
  cases step
  rfl

def sourceCurrent :
    SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
      oldVisit sourceIndex index := by
  cases step
  exact sourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
    oldVisit sourceIndex index

def sourcePayment : CanonicalPostSettlementOccurrencePaymentAt oldVisit
    sourceIndex index := by
  cases step
  exact payment

def sourceSuccessor := (sourcePayment step).successor

def sourceWholeLedgerWriteBack :=
  (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
    (sourceCurrent step)).wholeLedgerWriteBack

def targetCurrent :
    SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
      oldVisit sourceIndex (index + 1) := by
  cases step
  exact sourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
    oldVisit sourceIndex (index + 1)

def targetRootEvent :=
  SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
    (targetCurrent step)

def targetPayment :=
  SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.payment
    (targetCurrent step)

def targetFutureBirth :=
  SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.macroFutureBirth
    (targetCurrent step)

def targetChannel (channel :
    M14SourceGeneratedContributionCapacityEssentialAccessChannel.EssentialAccessChannel) :=
  SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.consumedChannel
    (targetCurrent step) channel

/-- The caller's exact payment, not a canonical proof chosen by this file,
generates the source successor used by the step. -/
theorem sourceSuccessor_isPaymentSuccessor :
    sourceSuccessor step = (sourcePayment step).successor :=
  rfl

/-- Main preservation square: arbitrary proof selection at the source payment
still lands on the exact next canonical-current occurrence. -/
theorem nextPaidBy_isTargetCanonicalOccurrence :
    HEq (sourcePayment step).nextPaidBy
      (targetRootEvent step).occurrence := by
  have nextProofIndependent :=
    postSettlement_nextPaidBy_proofIndependent
      (sourcePayment step)
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.payment
        (sourceCurrent step))
  rw [nextProofIndependent]
  exact
    SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.nextPaidBy_is_nextRootEvent
      (sourceCurrent step)

theorem targetCompilerWrite_exact :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile (targetRootEvent step).occurrence =
      .nativeWrite (targetPayment step).write :=
  SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.compilerWrite_exact
    (targetCurrent step)

theorem targetLocalLedger_isEmpty :
    IsEmpty
      (OpenResponsibilityAt
        (M14SourceGeneratedContributionCapacityJointSettlementWorld.JointSettlementNAt
          oldVisit)
        (targetRootEvent step).occurrence.1) :=
  SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.localLedger_isEmpty
    (targetCurrent step)

theorem targetExternalPaymentAndConsumer_nonempty :
    Nonempty
        M14SourceGeneratedContributionCapacityPostSettlementExternalLiability.ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (M14SourceGeneratedContributionCapacityPostSettlementExternalLiability.ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.actualExit
            (targetCurrent step))) :=
  SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.externalPaymentAndConsumer_nonempty
    (targetCurrent step)

theorem targetEveryChannel_consumed :
    ∀ channel :
        M14SourceGeneratedContributionCapacityEssentialAccessChannel.EssentialAccessChannel,
      Nonempty
        (M14ProofCarryingContributionCapacityPostSettlementChannelFamily.ConsumedContributionCapacityPostSettlementChannelAt
          oldVisit sourceIndex (index + 1) channel) :=
  SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.everyChannel_consumed
    (oldVisit := oldVisit) (sourceIndex := sourceIndex) (index := index + 1)

theorem targetProtectedInterest_noChannelSection :
    ¬ ∃ reconstruct : M3FiniteExchangeFixture.V.ProtectedInterest →
        M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection.AnyContributionCapacityPostSettlementEssentialAccessChannelAt
          oldVisit sourceIndex (index + 1),
      Function.LeftInverse reconstruct
        (M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection.contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex (index + 1)).forget :=
  SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.protectedInterest_noChannelSection
    (oldVisit := oldVisit) (sourceIndex := sourceIndex) (index := index + 1)

/-- The generated target payment immediately yields the next source-native
paid step.  This is pointwise recursion, not a stored infinite history. -/
def generatedNextPaidStep :
    SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
      oldVisit sourceIndex (index + 1) (targetPayment step) := by
  cases step
  exact sourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
    oldVisit sourceIndex (index + 1)
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.payment
        (sourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt
          oldVisit sourceIndex (index + 1)))

theorem generatedNextStep_source_isTarget :
    SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt.sourceCurrent
        (generatedNextPaidStep step) =
      targetCurrent step :=
  rfl

end SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt

theorem contributionCapacityPostSettlementCanonicalPaidStep_hasNoCallerTarget
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index) : True := by
  let step :=
    sourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
      oldVisit sourceIndex index payment
  fail_if_success exact step.target
  fail_if_success exact step.coverage
  fail_if_success exact step.normalizer
  fail_if_success exact step.next
  fail_if_success exact step.registry
  fail_if_success exact step.history
  fail_if_success exact step.future
  trivial

end
end M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep.sourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep.SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt.nextPaidBy_isTargetCanonicalOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep.SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt.generatedNextPaidStep
