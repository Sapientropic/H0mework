import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Preservation.PostSettlement.Step.Producer.SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep

/-!
# Proof-carrying canonical post-settlement paid-step invariant

The direct consumer is dependent on the exact source payment and paid-step
token.  It audits the whole-ledger successor, target canonical current,
installed channel family and recursive next step.  Bare writes, liabilities,
successor tokens, observer readouts and future births cannot retype as a paid
step.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M3FiniteExchangeFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep

inductive ProofCarryingContributionCapacityPostSettlementCanonicalPaidStepConsumerAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index}
    (step : SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
      oldVisit sourceIndex index payment) : Type 25
  | private consumed

def proofCarryingContributionCapacityPostSettlementCanonicalPaidStepConsumerAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index}
    (step : SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
      oldVisit sourceIndex index payment) :
    ProofCarryingContributionCapacityPostSettlementCanonicalPaidStepConsumerAt
      step :=
  .consumed

namespace ProofCarryingContributionCapacityPostSettlementCanonicalPaidStepConsumerAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  {payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
    index}
  {step : SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
    oldVisit sourceIndex index payment}
  (consumer :
    ProofCarryingContributionCapacityPostSettlementCanonicalPaidStepConsumerAt
      step)

def sourcePayment := by
  cases consumer
  exact step.sourcePayment

def sourceCurrent := by
  cases consumer
  exact step.sourceCurrent

def sourceSuccessor := by
  cases consumer
  exact step.sourceSuccessor

def targetCurrent := by
  cases consumer
  exact step.targetCurrent

def targetPayment := by
  cases consumer
  exact step.targetPayment

def targetFutureBirth := by
  cases consumer
  exact step.targetFutureBirth

def targetChannel (channel : EssentialAccessChannel) :
    ConsumedContributionCapacityPostSettlementChannelAt oldVisit sourceIndex
      (index + 1) channel := by
  cases consumer
  exact step.targetChannel channel

def nextStep := by
  cases consumer
  exact step.generatedNextPaidStep

theorem paidNext_isTargetCanonicalOccurrence :
    HEq (sourcePayment consumer).nextPaidBy
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        (targetCurrent consumer)).occurrence :=
  step.nextPaidBy_isTargetCanonicalOccurrence

theorem targetCompilerWrite_exact :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile
        (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
          (targetCurrent consumer)).occurrence =
      .nativeWrite (targetPayment consumer).write :=
  step.targetCompilerWrite_exact

theorem targetEveryChannel_consumed :
    ∀ channel : EssentialAccessChannel,
      Nonempty
        (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
          sourceIndex (index + 1) channel) :=
  fun channel =>
    ⟨proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex (index + 1) channel⟩

theorem targetChannelAudit (channel : EssentialAccessChannel) :
    let consumed := targetChannel consumer channel
    (consumed.2.relationWitnessReturn).1.actor
          M14EssentialAccessRelationFixture.essentialAccessRelationCompiler =
        channelActor channel ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
          (consumed.2.relationWitnessReturn).1 = channelRelation channel ∧
      consumed.2.rootReadCarrier.existingPaymentOccurrence =
        consumed.1.actualExit.paymentOccurrence ∧
      consumed.2.rootReadCarrier.existingActualSettlement =
        consumed.1.actualExit.actualSettlement ∧
      consumed.1.actualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes ∧
      consumed.2.actualNext =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (contributionCapacityPostSettlementCanonicalCurrentDepthAt oldVisit
              sourceIndex (index + 1) +
            1) := by
  cases consumer
  exact
    SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.channelAudit
      step.targetCurrent channel

theorem recursiveSource_isTarget :
    SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt.sourceCurrent
        (nextStep consumer) =
      targetCurrent consumer :=
  step.generatedNextStep_source_isTarget

end ProofCarryingContributionCapacityPostSettlementCanonicalPaidStepConsumerAt

abbrev ConsumedContributionCapacityPostSettlementCanonicalPaidStepAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index) :=
  Sigma fun step :
      SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex index payment =>
    ProofCarryingContributionCapacityPostSettlementCanonicalPaidStepConsumerAt
      step

def proofCarryingContributionCapacityPostSettlementCanonicalPaidStepAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index) :
    ConsumedContributionCapacityPostSettlementCanonicalPaidStepAt oldVisit
      sourceIndex index payment :=
  let step :=
    sourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
      oldVisit sourceIndex index payment
  ⟨step,
    proofCarryingContributionCapacityPostSettlementCanonicalPaidStepConsumerAt
      step⟩

theorem contributionCapacityPostSettlementEveryPayment_preservesCanonicalCurrent
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ∀ index : Nat,
      ∀ payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit
        sourceIndex index,
        Nonempty
          (ConsumedContributionCapacityPostSettlementCanonicalPaidStepAt
            oldVisit sourceIndex index payment) :=
  fun index payment =>
    ⟨proofCarryingContributionCapacityPostSettlementCanonicalPaidStepAt oldVisit
      sourceIndex index payment⟩

theorem contributionCapacityPostSettlementEveryPayment_nextCanonical
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index) :
    let consumed :=
      proofCarryingContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex index payment
    HEq consumed.2.sourcePayment.nextPaidBy
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        consumed.2.targetCurrent).occurrence :=
  (proofCarryingContributionCapacityPostSettlementCanonicalPaidStepAt oldVisit
    sourceIndex index payment).2.paidNext_isTargetCanonicalOccurrence

theorem contributionCapacityPostSettlementPaidStep_recursive
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index) :
    let consumed :=
      proofCarryingContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex index payment
    SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt.sourceCurrent
        consumed.2.nextStep =
      consumed.2.targetCurrent :=
  (proofCarryingContributionCapacityPostSettlementCanonicalPaidStepAt oldVisit
    sourceIndex index payment).2.recursiveSource_isTarget

structure ProofCarryingContributionCapacityPostSettlementCanonicalPaidStepInvariantAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  everyPaymentPreserves : ∀ index : Nat,
    ∀ payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index,
      Nonempty
        (ConsumedContributionCapacityPostSettlementCanonicalPaidStepAt oldVisit
          sourceIndex index payment)
  everyPaidNextCanonical : ∀ index : Nat,
    ∀ payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index,
      let consumed :=
        proofCarryingContributionCapacityPostSettlementCanonicalPaidStepAt
          oldVisit sourceIndex index payment
      HEq consumed.2.sourcePayment.nextPaidBy
        (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
          consumed.2.targetCurrent).occurrence
  everyTargetChannel : ∀ index : Nat,
    ∀ payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index,
      ∀ channel : EssentialAccessChannel,
        Nonempty
          (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
            sourceIndex (index + 1) channel)
  everyStepRecurses : ∀ index : Nat,
    ∀ payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      index,
      let consumed :=
        proofCarryingContributionCapacityPostSettlementCanonicalPaidStepAt
          oldVisit sourceIndex index payment
      SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt.sourceCurrent
          consumed.2.nextStep =
        consumed.2.targetCurrent
  targetObserverStillHasNoSection : ∀ index : Nat,
    ¬ ∃ reconstruct : M3FiniteExchangeFixture.V.ProtectedInterest →
        AnyContributionCapacityPostSettlementEssentialAccessChannelAt oldVisit
          sourceIndex (index + 1),
      Function.LeftInverse reconstruct
        (contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex (index + 1)).forget

theorem proofCarryingContributionCapacityPostSettlementCanonicalPaidStepInvariant
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityPostSettlementCanonicalPaidStepInvariantAt
      oldVisit sourceIndex where
  everyPaymentPreserves :=
    contributionCapacityPostSettlementEveryPayment_preservesCanonicalCurrent
      oldVisit sourceIndex
  everyPaidNextCanonical := fun index payment =>
    contributionCapacityPostSettlementEveryPayment_nextCanonical oldVisit
      sourceIndex index payment
  everyTargetChannel := fun index payment =>
    fun channel =>
      ⟨proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
        sourceIndex (index + 1) channel⟩
  everyStepRecurses := fun index payment =>
    contributionCapacityPostSettlementPaidStep_recursive oldVisit sourceIndex
      index payment
  targetObserverStillHasNoSection := fun index =>
    contributionCapacityPostSettlementChannel_noOccurrenceReconstruction
      oldVisit sourceIndex (index + 1)

set_option linter.unusedVariables false in
theorem barePaymentFragmentsCannotRetypeAsCanonicalPaidStep
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let payment :=
    sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index
  fail_if_success exact
    (payment.write :
      SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex index payment)
  fail_if_success exact
    (payment.liability :
      SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex index payment)
  fail_if_success exact
    (payment.successor :
      SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex index payment)
  fail_if_success exact
    (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index :
      SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex index payment)
  fail_if_success exact
    (M14EssentialAccessSectorRegression.protectedInterestReadout
        M14EssentialAccessSectorRegression.tenureAuthority :
      SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex index payment)
  fail_if_success exact
    (M14SourceGeneratedContributionCapacityJointSettlementConsumer.canonicalContributionCapacityJointSettlementSearchTick :
      SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex index payment)
  trivial

end
end M14ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep.proofCarryingContributionCapacityPostSettlementCanonicalPaidStepInvariant
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep.contributionCapacityPostSettlementEveryPayment_nextCanonical
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep.barePaymentFragmentsCannotRetypeAsCanonicalPaidStep
