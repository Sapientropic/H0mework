import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Channel.Producer.SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection

/-!
# Proof-carrying post-settlement channel family

Every exact post-root event and every existing essential-access relation
authority generates its own Type-valued consumer.  The consumer exposes the
root-read carrier, relation witness, payment, route, service, responsibility
consumer and actual paid next.  Tenure and health are independently consumed;
their authority differs although their legacy readout agrees, and both commute
to the one compiler-generated next of the shared actual occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityPostSettlementChannelFamily

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open Observer
open M3FiniteExchangeFixture
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection

/-- A direct dependent consumer.  It accepts only the root-generated channel
token and carries no alternative actor, relation, payment, service or next. -/
inductive ProofCarryingContributionCapacityPostSettlementChannelConsumerAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {channel : EssentialAccessChannel}
    (generated :
      SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
        oldVisit sourceIndex index channel) : Type 22
  | private consumed

def proofCarryingContributionCapacityPostSettlementChannelConsumerAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {channel : EssentialAccessChannel}
    (generated :
      SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
        oldVisit sourceIndex index channel) :
    ProofCarryingContributionCapacityPostSettlementChannelConsumerAt
      generated :=
  .consumed

namespace ProofCarryingContributionCapacityPostSettlementChannelConsumerAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  {channel : EssentialAccessChannel}
  {generated :
    SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
      oldVisit sourceIndex index channel}
  (consumer :
    ProofCarryingContributionCapacityPostSettlementChannelConsumerAt generated)

def rootInstalledFace := by
  cases consumer
  exact generated.installedFace

def rootReadCarrier := by
  cases consumer
  exact generated.channelCarrier

def relationInterest := by
  cases consumer
  exact generated.relationInterest

def targetRoleGenerated := by
  cases consumer
  exact generated.targetRoleGenerated

def paymentReceipt := by
  cases consumer
  exact generated.paymentReceipt

def routeReceipt := by
  cases consumer
  exact generated.routeReceipt

def serviceReceipt := by
  cases consumer
  exact generated.serviceReceipt

def responsibilityConsumer := by
  cases consumer
  exact generated.rootConsumer

def rootFactorization := by
  cases consumer
  exact generated.rootFactorization

def relationWitnessReturn := by
  cases consumer
  exact generated.witnessReturn

def actualNext := by
  cases consumer
  exact generated.actualNext

theorem rootReadCarrier_exact :
    rootReadCarrier consumer = generated.channelCarrier :=
  rfl

theorem relationWitnessReturn_exact :
    (relationWitnessReturn consumer).1.actor essentialAccessRelationCompiler =
        channelActor channel ∧
      essentialAccessRelationCompiler.relationOf
          (relationWitnessReturn consumer).1 =
        channelRelation channel :=
  M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel.SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt.relationWitness_returns_exactSource
    generated

theorem paymentOccurrence_exact :
    (rootReadCarrier consumer).existingPaymentOccurrence =
      (generated.actualExit).paymentOccurrence :=
  M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel.SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt.channelCarrierPayment_exact
    generated

theorem actualSettlement_exact :
    (rootReadCarrier consumer).existingActualSettlement =
      (generated.actualExit).actualSettlement :=
  M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel.SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt.channelCarrierSettlement_exact
    generated

theorem phase_relationGenerated :
    essentialAccessRelationCompiler.phaseStep (channelRelation channel) =
        channelPhase channel ∧
      rootReadCarrier consumer = rootReadCarrier consumer :=
  ⟨(rootReadCarrier consumer).phaseGenerated, rfl⟩

theorem role_relationGenerated :
    essentialAccessRelationCompiler.RelationRoleAt
        (channelActor channel) (channelRelation channel) .target
          (channelTargetRole channel) ∧
      rootReadCarrier consumer = rootReadCarrier consumer :=
  ⟨(rootReadCarrier consumer).targetRoleGenerated, rfl⟩

@[simp] theorem actualNext_commutes :
    actualNext consumer =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
            oldVisit sourceIndex index +
          1) :=
  M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel.SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt.actualNext_exact
    generated

theorem paymentNext_is_consumerNext :
    generated.postPayment.nextPaidBy = actualNext consumer :=
  M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel.SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt.postPaymentNext_eq_actualNext
    generated

end ProofCarryingContributionCapacityPostSettlementChannelConsumerAt

abbrev ConsumedContributionCapacityPostSettlementChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :=
  Sigma fun generated :
      SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
        oldVisit sourceIndex index channel =>
    ProofCarryingContributionCapacityPostSettlementChannelConsumerAt generated

def proofCarryingContributionCapacityPostSettlementChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :
    ConsumedContributionCapacityPostSettlementChannelAt oldVisit sourceIndex
      index channel :=
  let generated :=
    sourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
      oldVisit sourceIndex index channel
  ⟨generated,
    proofCarryingContributionCapacityPostSettlementChannelConsumerAt generated⟩

def proofCarryingContributionCapacityPostSettlementTenureChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ConsumedContributionCapacityPostSettlementChannelAt oldVisit sourceIndex
      index tenureAuthority :=
  proofCarryingContributionCapacityPostSettlementChannelAt oldVisit sourceIndex
    index tenureAuthority

def proofCarryingContributionCapacityPostSettlementHealthChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ConsumedContributionCapacityPostSettlementChannelAt oldVisit sourceIndex
      index healthAuthority :=
  proofCarryingContributionCapacityPostSettlementChannelAt oldVisit sourceIndex
    index healthAuthority

/-- The family consumer is total over the existing relation-authority fibre
and over every canonical post-root index. -/
theorem proofCarryingContributionCapacityPostSettlement_everyChannelConsumed
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ∀ index : Nat, ∀ channel : EssentialAccessChannel,
      Nonempty
        (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
          sourceIndex index channel) :=
  fun index channel =>
    ⟨proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex index channel⟩

/-- One independently consumed channel strictly beyond an arbitrary absolute
macro-history boundary.  The carrier contains one generated later occurrence,
not a completed channel schedule. -/
structure ProofCarryingLaterContributionCapacityPostSettlementChannelAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : EssentialAccessChannel) : Type 23 where
  private mk ::
  index : Nat
  consumed : ConsumedContributionCapacityPostSettlementChannelAt oldVisit
    sourceIndex index channel
  later : boundary <
    contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
      oldVisit sourceIndex index

def proofCarryingLaterContributionCapacityPostSettlementChannelAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : EssentialAccessChannel) :
    ProofCarryingLaterContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex boundary channel :=
  let laterBirth :=
    sourceGeneratedLaterContributionCapacityMacroFutureBirthAt oldVisit
      sourceIndex boundary
  { index := laterBirth.index
    consumed :=
      proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
        sourceIndex laterBirth.index channel
    later := laterBirth.later }

/-- Cofinal channel propagation: after every finite absolute boundary, every
existing relation-generated channel has a later actual paid consumer. -/
theorem proofCarryingContributionCapacityPostSettlement_channelsCofinal
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ∀ boundary : Nat, ∀ channel : EssentialAccessChannel,
      Nonempty
        (ProofCarryingLaterContributionCapacityPostSettlementChannelAt oldVisit
          sourceIndex boundary channel) :=
  fun boundary channel =>
    ⟨proofCarryingLaterContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex boundary channel⟩

/-- Full pointwise audit mouth.  The returned relation witness, payment,
settlement, responsibility factorization and next all belong to the one
root-installed channel token consumed here. -/
theorem proofCarryingContributionCapacityPostSettlement_channelAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :
    let consumed :=
      proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
        sourceIndex index channel
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
          (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
              oldVisit sourceIndex index +
            1) := by
  dsimp only
  exact ⟨(proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex index channel).2.relationWitnessReturn_exact |>.1,
    (proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex index channel).2.relationWitnessReturn_exact |>.2,
    (proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex index channel).2.paymentOccurrence_exact,
    (proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex index channel).2.actualSettlement_exact,
    (proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex index channel).2.rootFactorization,
    (proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
      sourceIndex index channel).2.actualNext_commutes⟩

theorem proofCarryingContributionCapacityPostSettlement_tenureConsumerNext
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (proofCarryingContributionCapacityPostSettlementTenureChannelAt oldVisit
        sourceIndex index).2.actualNext =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
            oldVisit sourceIndex index +
          1) :=
  (proofCarryingContributionCapacityPostSettlementTenureChannelAt oldVisit
    sourceIndex index).2.actualNext_commutes

theorem proofCarryingContributionCapacityPostSettlement_healthConsumerNext
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (proofCarryingContributionCapacityPostSettlementHealthChannelAt oldVisit
        sourceIndex index).2.actualNext =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
            oldVisit sourceIndex index +
          1) :=
  (proofCarryingContributionCapacityPostSettlementHealthChannelAt oldVisit
    sourceIndex index).2.actualNext_commutes

theorem proofCarryingContributionCapacityPostSettlement_independentConsumers_sameActualNext
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (proofCarryingContributionCapacityPostSettlementTenureChannelAt oldVisit
        sourceIndex index).2.actualNext =
      (proofCarryingContributionCapacityPostSettlementHealthChannelAt oldVisit
        sourceIndex index).2.actualNext := by
  rw [proofCarryingContributionCapacityPostSettlement_tenureConsumerNext,
    proofCarryingContributionCapacityPostSettlement_healthConsumerNext]

structure ProofCarryingContributionCapacityPostSettlementChannelFamilyCertificate
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  everyChannelConsumed : ∀ index : Nat,
    ∀ channel : EssentialAccessChannel,
      Nonempty
        (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
          sourceIndex index channel)
  channelsCofinal : ∀ boundary : Nat, ∀ channel : EssentialAccessChannel,
    Nonempty
      (ProofCarryingLaterContributionCapacityPostSettlementChannelAt oldVisit
        sourceIndex boundary channel)
  everyChannelAudited : ∀ index : Nat, ∀ channel : EssentialAccessChannel,
    let consumed :=
      proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
        sourceIndex index channel
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
          (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
              oldVisit sourceIndex index +
            1)
  sameVisibleDifferentK : ∀ index : Nat,
    let observer :=
      contributionCapacityPostSettlementEssentialAccessChannelObserverAt
        oldVisit sourceIndex index
    observer.forget
        (contributionCapacityPostSettlementTenureChannelAt oldVisit sourceIndex
          index) =
      observer.forget
        (contributionCapacityPostSettlementHealthChannelAt oldVisit sourceIndex
          index) ∧
    observer.authorityK
        (contributionCapacityPostSettlementTenureChannelAt oldVisit sourceIndex
          index) ≠
      observer.authorityK
        (contributionCapacityPostSettlementHealthChannelAt oldVisit sourceIndex
          index)
  serviceSlotsDifferent : ∀ index : Nat,
    channelSlotAt
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
          oldVisit sourceIndex index) tenureAuthority ≠
      channelSlotAt
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
          oldVisit sourceIndex index) healthAuthority
  independentConsumerNext : ∀ index : Nat,
    (proofCarryingContributionCapacityPostSettlementTenureChannelAt oldVisit
        sourceIndex index).2.actualNext =
      (proofCarryingContributionCapacityPostSettlementHealthChannelAt oldVisit
        sourceIndex index).2.actualNext
  noOccurrenceSection : ∀ index : Nat,
    ¬ ∃ reconstruct : M3FiniteExchangeFixture.V.ProtectedInterest →
        AnyContributionCapacityPostSettlementEssentialAccessChannelAt oldVisit
          sourceIndex index,
      Function.LeftInverse reconstruct
        (contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex index).forget
  noAuthorityFactor : ∀ index : Nat,
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex index))

theorem proofCarryingContributionCapacityPostSettlementChannelFamily
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityPostSettlementChannelFamilyCertificate
      oldVisit sourceIndex where
  everyChannelConsumed :=
    proofCarryingContributionCapacityPostSettlement_everyChannelConsumed
      oldVisit sourceIndex
  channelsCofinal :=
    proofCarryingContributionCapacityPostSettlement_channelsCofinal oldVisit
      sourceIndex
  everyChannelAudited := fun index channel =>
    proofCarryingContributionCapacityPostSettlement_channelAuditAt oldVisit
      sourceIndex index channel
  sameVisibleDifferentK := fun index =>
    contributionCapacityPostSettlement_sameVisible_differentChannelK oldVisit
      sourceIndex index
  serviceSlotsDifferent := fun index =>
    contributionCapacityPostSettlementTenureHealthSlots_distinct oldVisit
      sourceIndex index
  independentConsumerNext := fun index =>
    proofCarryingContributionCapacityPostSettlement_independentConsumers_sameActualNext
      oldVisit sourceIndex index
  noOccurrenceSection := fun index =>
    contributionCapacityPostSettlementChannel_noOccurrenceReconstruction
      oldVisit sourceIndex index
  noAuthorityFactor := fun index =>
    contributionCapacityPostSettlementChannel_noAuthorityFactorization oldVisit
      sourceIndex index

set_option linter.unusedVariables false in
theorem bareReadoutsCannotRetypeAsPostSettlementChannel
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let generated :=
    sourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
      oldVisit sourceIndex index tenureAuthority
  fail_if_success exact
    ((protectedInterestReadout tenureAuthority) :
      SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
        oldVisit sourceIndex index tenureAuthority)
  fail_if_success exact
    (generated.actualExit.paymentOccurrence :
      SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
        oldVisit sourceIndex index tenureAuthority)
  fail_if_success exact
    (generated.channelCarrier.serviceReceipt :
      SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
        oldVisit sourceIndex index tenureAuthority)
  fail_if_success exact
    (generated.channelCarrier.rootConsumer :
      SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
        oldVisit sourceIndex index tenureAuthority)
  trivial

end
end M14ProofCarryingContributionCapacityPostSettlementChannelFamily
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPostSettlementChannelFamily.proofCarryingContributionCapacityPostSettlementChannelFamily
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPostSettlementChannelFamily.proofCarryingContributionCapacityPostSettlement_independentConsumers_sameActualNext
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPostSettlementChannelFamily.bareReadoutsCannotRetypeAsPostSettlementChannel
