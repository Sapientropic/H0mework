import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Channel.Consumer.ProofCarryingContributionCapacityPostSettlementChannelFamily

/-!
# Independent necessity of service-beneficiary/bearer alignment

One exact post-settlement occurrence already installs three dependent faces:
the bearer-aligned exit and the tenure/health essential-access channels.  The
health face retains a genuine middle-slot service, Payment, route, channel
consumer, factorization, external liability and the same paid next, but its
`.t2` service actor is not the `.t1` Payment/exit/original-birth bearer.  The
tenure face is the positive `.t1` comparator; canonical carrier invariants
identify its first-slot receipt literally with the bearer-exit receipt.

Every compared value below is read from those existing root faces.  The sole
producer accepts only the existing root indices; it accepts no channel,
actor, bearer, slot, Payment, target or future.  The post-root local ledger is
empty, so this module preserves external liability and successor authority
without inventing a live residual row.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily

/-! ## Canonical same-occurrence objects -/

def serviceBeneficiaryAlignmentCurrentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Nat :=
  contributionCapacityPostSettlementEssentialAccessChannelCurrentAt oldVisit
    sourceIndex index

abbrev CanonicalServiceAlignmentFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
    sourceIndex index

def canonicalServiceAlignmentFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalServiceAlignmentFutureBirthAt oldVisit sourceIndex index :=
  sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
    sourceIndex index

def serviceBeneficiaryAlignmentActualExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PeriodicActualServiceExitAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index) :=
  contributionCapacityPostSettlementEssentialAccessChannelActualExitAt
    oldVisit sourceIndex index

abbrev ServiceBeneficiaryAlignmentBearerExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedContributionCapacityBirthBearerExitAt
    (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
    (serviceBeneficiaryAlignmentActualExitAt oldVisit sourceIndex index)

abbrev ServiceBeneficiaryAlignmentChannelCarrierAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :=
  SourceGeneratedContributionCapacityEssentialAccessChannelAt
    (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
    channel
    (serviceBeneficiaryAlignmentActualExitAt oldVisit sourceIndex index)

abbrev ServiceBeneficiaryAlignmentChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :=
  SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
    oldVisit sourceIndex index channel

def serviceBeneficiaryAlignmentBearerFaceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index) :=
  contributionCapacityPostSettlementFutureBirthBearerExitFaceAt oldVisit
    sourceIndex index

def serviceBeneficiaryAlignmentChannelFaceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index) :=
  contributionCapacityPostSettlementEssentialAccessChannelFaceAt oldVisit
    sourceIndex index channel

def serviceBeneficiaryAlignmentBearerRootReadAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PLift (Nonempty
      (ServiceBeneficiaryAlignmentBearerExitAt oldVisit sourceIndex index)) :=
  contributionCapacityPostSettlementFutureBirthInstalledBearerExitAt oldVisit
    sourceIndex index

def serviceBeneficiaryAlignmentChannelRootReadAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :
    PLift (Nonempty
      (ServiceBeneficiaryAlignmentChannelCarrierAt oldVisit sourceIndex index
        channel)) :=
  contributionCapacityPostSettlementInstalledEssentialAccessChannelAt oldVisit
    sourceIndex index channel

def serviceBeneficiaryAlignmentBearerExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ServiceBeneficiaryAlignmentBearerExitAt oldVisit sourceIndex index :=
  Classical.choice
    (serviceBeneficiaryAlignmentBearerRootReadAt oldVisit sourceIndex index).down

def serviceBeneficiaryAlignmentChannelCarrierAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :
    ServiceBeneficiaryAlignmentChannelCarrierAt oldVisit sourceIndex index
      channel :=
  Classical.choice
    (serviceBeneficiaryAlignmentChannelRootReadAt oldVisit sourceIndex index
      channel).down

def serviceBeneficiaryAlignmentChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :
    ServiceBeneficiaryAlignmentChannelAt oldVisit sourceIndex index channel :=
  sourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
    oldVisit sourceIndex index channel

/-! ## Exact service-beneficiary alignment fibre -/

/-- The alignment fibre itself consumes both root reads.  A bare actor or
service receipt cannot inhabit it. -/
structure ExactServiceBeneficiaryBearerAlignmentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) : Type 23 where
  private mk ::
  bearerFace : SourceNativeRootSemanticFaceAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  bearerFaceExact : bearerFace =
    serviceBeneficiaryAlignmentBearerFaceAt oldVisit sourceIndex index
  bearerRootRead : PLift (Nonempty
    (ServiceBeneficiaryAlignmentBearerExitAt oldVisit sourceIndex index))
  bearerRootReadExact : bearerRootRead =
    serviceBeneficiaryAlignmentBearerRootReadAt oldVisit sourceIndex index
  bearerExit :
    ServiceBeneficiaryAlignmentBearerExitAt oldVisit sourceIndex index
  bearerExitFromRootRead : bearerExit =
    Classical.choice bearerRootRead.down
  channelFace : SourceNativeRootSemanticFaceAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  channelFaceExact : channelFace =
    serviceBeneficiaryAlignmentChannelFaceAt oldVisit sourceIndex index channel
  channelRootRead : PLift (Nonempty
    (ServiceBeneficiaryAlignmentChannelCarrierAt oldVisit sourceIndex index
      channel))
  channelRootReadExact : channelRootRead =
    serviceBeneficiaryAlignmentChannelRootReadAt oldVisit sourceIndex index
      channel
  channelCarrier :
    ServiceBeneficiaryAlignmentChannelCarrierAt oldVisit sourceIndex index
      channel
  channelCarrierFromRootRead : channelCarrier =
    Classical.choice channelRootRead.down
  bearerFeasibleCanonicalExact : bearerExit.feasibleEdge =
    birthBearerFirstFeasibleExitAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
  channelSlot : Fin
    (anomiePhaseAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
      ).served.length
  channelSlotFromRootRead : channelSlot =
    channelSlotAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index) channel
  channelServiceReceipt :
    (serviceCompilerAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
      ).ServesAt
        ((anomiePhaseAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
          ).served.get
            (channelSlotAt
              (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
              channel))
        (run.events.get
          (Fin.cast
            (actualSettlementAt
              (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
              ).eventsLength_eq_allocated.symm
            (channelSlotAt
              (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
              channel)))
  channelServiceReceiptFromRootRead : channelServiceReceipt =
    channelCarrier.serviceReceipt
  channelServiceReceiptCanonicalExact : channelCarrier.serviceReceipt =
    channelServiceReceiptAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index) channel
  channelFeasible : ExactFeasibleExitEdgeAt
    (geometryCompilerAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))
    ExitFutureCode.leave
    (channelSlotAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index) channel)
  channelFeasibleFromRootRead : channelFeasible = channelCarrier.feasible
  channelFeasibleCanonicalExact : channelCarrier.feasible =
    channelFeasibleExitAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index) channel
  channelSlot_eq_exitSlot : channelSlot =
    firstSlotAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
  channelServiceReceipt_eq_exitServiceReceipt :
    HEq channelServiceReceipt bearerExit.feasibleEdge.serviceReceipt
  channelRelationWitness : EssentialAccessChannelWitnessReturnAt channel
  channelRelationWitnessFromRootRead : channelRelationWitness =
    channelCarrier.witnessReturn
  channelRelationWitnessActorExact :
    channelRelationWitness.1.actor essentialAccessRelationCompiler =
      channelActor channel
  relationWitnessActor_eq_exitWorker :
    channelRelationWitness.1.actor essentialAccessRelationCompiler =
      birthBearerWorker
  channelPayment_eq_bearerPayment :
    channelCarrier.existingPaymentOccurrence =
      bearerExit.existingPaymentOccurrence
  channelSettlement_eq_bearerSettlement :
    channelCarrier.existingActualSettlement =
      bearerExit.existingActualSettlement
  channelActor_eq_exitWorker :
    channelActor channel = birthBearerWorker
  bearerStandingCounterparty_eq_exitWorker :
    PurchasingPowerStandingAt.counterparty
        birthBearerExitCapacityProgram.purchasingPowerStanding =
      birthBearerWorker
  bearerWorker_eq_existingParent :
    exchangeLaw.bearerOfActor birthBearerWorker =
      sourceGeneratedLossAllocationMaterial.parentBearer
  channelBearer_eq_originalBirthBearer :
    exchangeLaw.bearerOfActor (channelActor channel) =
      ((canonicalServiceAlignmentFutureBirthAt oldVisit sourceIndex index
        ).reopeningFutureBirth.birthAdmission).obligation.bearer

abbrev HealthServiceBeneficiaryBearerAlignmentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  ExactServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index
    healthAuthority

abbrev TenureServiceBeneficiaryBearerAlignmentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  ExactServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index
    tenureAuthority

theorem tenureChannelActor_eq_birthBearerWorker :
    channelActor tenureAuthority = birthBearerWorker := by
  apply Subtype.ext
  rfl

theorem healthChannelActor_ne_birthBearerWorker :
    channelActor healthAuthority ≠ birthBearerWorker := by
  intro equality
  have values := congrArg Subtype.val equality
  cases values

theorem healthServiceBeneficiaryBearerAlignment_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index) :=
  ⟨fun alignment =>
    healthChannelActor_ne_birthBearerWorker
      alignment.channelActor_eq_exitWorker⟩

/-- Positive alignment generated without a channel/actor/slot argument.  The
tenure channel and bearer exit are both selected by this occurrence's fixed
projection law. -/
def tenureServiceBeneficiaryBearerAlignmentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    TenureServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index := by
  let futureBirth :=
    canonicalServiceAlignmentFutureBirthAt oldVisit sourceIndex index
  let bearerRootRead :=
    serviceBeneficiaryAlignmentBearerRootReadAt oldVisit sourceIndex index
  let channelRootRead :=
    serviceBeneficiaryAlignmentChannelRootReadAt oldVisit sourceIndex index
      tenureAuthority
  let bearerExit := Classical.choice bearerRootRead.down
  let channelCarrier := Classical.choice channelRootRead.down
  exact
    { bearerFace :=
        serviceBeneficiaryAlignmentBearerFaceAt oldVisit sourceIndex index
      bearerFaceExact := rfl
      bearerRootRead := bearerRootRead
      bearerRootReadExact := rfl
      bearerExit := bearerExit
      bearerExitFromRootRead := rfl
      channelFace :=
        serviceBeneficiaryAlignmentChannelFaceAt oldVisit sourceIndex index
          tenureAuthority
      channelFaceExact := rfl
      channelRootRead := channelRootRead
      channelRootReadExact := rfl
      channelCarrier := channelCarrier
      channelCarrierFromRootRead := rfl
      bearerFeasibleCanonicalExact := bearerExit.feasibleEdgeExact
      channelSlot :=
        channelSlotAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
          tenureAuthority
      channelSlotFromRootRead := rfl
      channelServiceReceipt := channelCarrier.serviceReceipt
      channelServiceReceiptFromRootRead := rfl
      channelServiceReceiptCanonicalExact :=
        channelCarrier.serviceReceiptExact
      channelFeasible := channelCarrier.feasible
      channelFeasibleFromRootRead := rfl
      channelFeasibleCanonicalExact := channelCarrier.feasibleExact
      channelSlot_eq_exitSlot := rfl
      channelServiceReceipt_eq_exitServiceReceipt := by
        rw [channelCarrier.serviceReceiptExact,
          bearerExit.feasibleEdgeExact]
        rfl
      channelRelationWitness := channelCarrier.witnessReturn
      channelRelationWitnessFromRootRead := rfl
      channelRelationWitnessActorExact :=
        channelCarrier.witnessReturn_exact.1
      relationWitnessActor_eq_exitWorker :=
        channelCarrier.witnessReturn_exact.1.trans
          tenureChannelActor_eq_birthBearerWorker
      channelPayment_eq_bearerPayment :=
        channelCarrier.paymentOccurrence_eq_input.trans
          bearerExit.paymentOccurrence_eq_input.symm
      channelSettlement_eq_bearerSettlement :=
        channelCarrier.actualSettlement_eq_input.trans
          bearerExit.actualSettlement_eq_input.symm
      channelActor_eq_exitWorker :=
        tenureChannelActor_eq_birthBearerWorker
      bearerStandingCounterparty_eq_exitWorker :=
        bearerExit.standingCounterparty_eq_worker
      bearerWorker_eq_existingParent :=
        bearerExit.workerBearer_eq_parent
      channelBearer_eq_originalBirthBearer := by
        rw [tenureChannelActor_eq_birthBearerWorker]
        exact futureBirth.paymentWorkerBirthBearer_exact.2 }

/-! ## Full same-occurrence countermodel -/

structure SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 24 where
  private mk ::
  futureBirth : CanonicalServiceAlignmentFutureBirthAt oldVisit sourceIndex
    index
  futureBirthExact : futureBirth =
    canonicalServiceAlignmentFutureBirthAt oldVisit sourceIndex index
  outerRootEvent : ExactTemporalCausalRootEventAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
      ).toAuthoritativeRoot.toLedgerRoot
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  outerRootEventExact : outerRootEvent = futureBirth.postRootEvent
  postPayment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
    index
  postPaymentExact : postPayment = futureBirth.postPayment
  actualExit : PeriodicActualServiceExitAt
    (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
  actualExitExact : actualExit = futureBirth.actualExit
  embeddedM9Payment : PeriodicSourceBackedPaymentAt
    (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
  embeddedM9PaymentExact : embeddedM9Payment = actualExit.paymentOccurrence
  embeddedM9RootEvent : ExactTemporalCausalRootEventAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot
    (temporalVisitAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))
  embeddedM9RootEventExact : embeddedM9RootEvent =
    embeddedM9Payment.rootOccurrence
  originalBirthAdmission :
    ExactGeneratedContributionCapacityResidualBirthAdmissionAt oldVisit
  originalBirthAdmissionExact : originalBirthAdmission =
    futureBirth.reopeningFutureBirth.birthAdmission
  originalBirthAdmissionSourceExact : originalBirthAdmission =
    sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
  originalBirthObligationExact : originalBirthAdmission.obligation =
    contributionCapacityU8ObligationAt oldVisit
      exactSourceGeneratedLossAllocationMaterialWitness
      (contributionCapacityU8GeneratedResidual oldVisit)
  originalBirthBearerExisting : originalBirthAdmission.obligation.bearer =
    contributionCapacityU8BearerAt oldVisit
      exactSourceGeneratedLossAllocationMaterialWitness
      (contributionCapacityU8GeneratedResidual oldVisit)
  exitWorkerBearer_eq_originalBirthBearer :
    exchangeLaw.bearerOfActor birthBearerWorker =
      originalBirthAdmission.obligation.bearer
  healthFace : SourceNativeRootSemanticFaceAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  healthFaceExact : healthFace =
    serviceBeneficiaryAlignmentChannelFaceAt oldVisit sourceIndex index
      healthAuthority
  healthRootRead : PLift (Nonempty
    (ServiceBeneficiaryAlignmentChannelCarrierAt oldVisit sourceIndex index
      healthAuthority))
  healthRootReadExact : healthRootRead =
    serviceBeneficiaryAlignmentChannelRootReadAt oldVisit sourceIndex index
      healthAuthority
  healthCarrier :
    ServiceBeneficiaryAlignmentChannelCarrierAt oldVisit sourceIndex index
      healthAuthority
  healthCarrierFromRootRead : healthCarrier =
    Classical.choice healthRootRead.down
  positiveTenureAlignment :
    TenureServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index
  tenureChannel : ServiceBeneficiaryAlignmentChannelAt oldVisit sourceIndex
    index tenureAuthority
  tenureChannelExact : tenureChannel =
    serviceBeneficiaryAlignmentChannelAt oldVisit sourceIndex index
      tenureAuthority
  healthChannel : ServiceBeneficiaryAlignmentChannelAt oldVisit sourceIndex
    index healthAuthority
  healthChannelExact : healthChannel =
    serviceBeneficiaryAlignmentChannelAt oldVisit sourceIndex index
      healthAuthority
  tenureChannelCarrierFromRootRead :
    HEq tenureChannel.channelCarrier positiveTenureAlignment.channelCarrier
  healthChannelCarrierFromRootRead :
    HEq healthChannel.channelCarrier healthCarrier
  futureBirthBearerExitFromRootRead : futureBirth.bearerExit =
    positiveTenureAlignment.bearerExit
  tenureConsumer :
    ProofCarryingContributionCapacityPostSettlementChannelConsumerAt
      tenureChannel
  healthConsumer :
    ProofCarryingContributionCapacityPostSettlementChannelConsumerAt
      healthChannel
  tenureConsumerRootReadCarrierExact :
    HEq tenureConsumer.rootReadCarrier positiveTenureAlignment.channelCarrier
  healthConsumerRootReadCarrierExact :
    HEq healthConsumer.rootReadCarrier healthCarrier
  tenureConsumerFactorization :
    (tenureChannel.actualExit.paymentOccurrence.installed
      ).RootAnswerAndNextFactorizes
  healthConsumerFactorization :
    (healthChannel.actualExit.paymentOccurrence.installed
      ).RootAnswerAndNextFactorizes
  tenureConsumerPaymentNextExact :
    tenureChannel.postPayment.nextPaidBy = tenureConsumer.actualNext
  healthConsumerPaymentNextExact :
    healthChannel.postPayment.nextPaidBy = healthConsumer.actualNext
  tenureConsumerNextExact : tenureConsumer.actualNext = postPayment.nextPaidBy
  healthConsumerNextExact : healthConsumer.actualNext = postPayment.nextPaidBy
  externalLiability : PostSettlementGeneratedExternalLiabilityAt oldVisit
    sourceIndex index outerRootEvent actualExit
  externalLiabilityFromPostPayment :
    HEq externalLiability postPayment.liability
  crossRootOccurrenceDistinct :
    (Sum.inl outerRootEvent :
      ExactTemporalCausalRootEventAt
          (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
            ).toAuthoritativeRoot.toLedgerRoot
          (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
            index) ⊕
        ExactTemporalCausalRootEventAt
          jointRoot.toAuthoritativeRoot.toLedgerRoot
          (temporalVisitAt
            (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))) ≠
      Sum.inr embeddedM9RootEvent
  externalSourceOwnership :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership
  externalRootConsumer : Nonempty
    (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt actualExit)
  localLedgerEmpty : IsEmpty
    (OpenResponsibilityAt (JointSettlementNAt oldVisit)
      outerRootEvent.occurrence.1)
  tenureNextExact : tenureChannel.actualNext = postPayment.nextPaidBy
  healthNextExact : healthChannel.actualNext = postPayment.nextPaidBy
  nextPaidByExact : postPayment.nextPaidBy =
    contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index + 1)
  healthAlignmentDeleted : IsEmpty
    (HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)

/-- Sole producer.  `oldVisit/sourceIndex/index` select one exact existing
post-root occurrence; every face, service, Payment, consumer and next is read
from it. -/
def sourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
      oldVisit sourceIndex index := by
  let futureBirth :=
    canonicalServiceAlignmentFutureBirthAt oldVisit sourceIndex index
  let actualExit :=
    serviceBeneficiaryAlignmentActualExitAt oldVisit sourceIndex index
  let healthRootRead :=
    serviceBeneficiaryAlignmentChannelRootReadAt oldVisit sourceIndex index
      healthAuthority
  let healthCarrier := Classical.choice healthRootRead.down
  let positiveTenureAlignment :=
    tenureServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index
  let tenureChannel :=
    serviceBeneficiaryAlignmentChannelAt oldVisit sourceIndex index
      tenureAuthority
  let healthChannel :=
    serviceBeneficiaryAlignmentChannelAt oldVisit sourceIndex index
      healthAuthority
  let tenureConsumer :=
    proofCarryingContributionCapacityPostSettlementChannelConsumerAt
      tenureChannel
  let healthConsumer :=
    proofCarryingContributionCapacityPostSettlementChannelConsumerAt
      healthChannel
  let externalLiability := futureBirth.externalLiability
  exact
    { futureBirth := futureBirth
      futureBirthExact := rfl
      outerRootEvent := futureBirth.postRootEvent
      outerRootEventExact := rfl
      postPayment := futureBirth.postPayment
      postPaymentExact := rfl
      actualExit := actualExit
      actualExitExact := rfl
      embeddedM9Payment := actualExit.paymentOccurrence
      embeddedM9PaymentExact := rfl
      embeddedM9RootEvent := actualExit.paymentOccurrence.rootOccurrence
      embeddedM9RootEventExact := rfl
      originalBirthAdmission :=
        futureBirth.reopeningFutureBirth.birthAdmission
      originalBirthAdmissionExact := rfl
      originalBirthAdmissionSourceExact := rfl
      originalBirthObligationExact :=
        futureBirth.reopeningFutureBirth.birthAdmission.obligationExact
      originalBirthBearerExisting :=
        futureBirth.reopeningFutureBirth.birthAdmission.bearerExisting
      exitWorkerBearer_eq_originalBirthBearer :=
        futureBirth.paymentWorkerBirthBearer_exact.2
      healthFace :=
        serviceBeneficiaryAlignmentChannelFaceAt oldVisit sourceIndex index
          healthAuthority
      healthFaceExact := rfl
      healthRootRead := healthRootRead
      healthRootReadExact := rfl
      healthCarrier := healthCarrier
      healthCarrierFromRootRead := rfl
      positiveTenureAlignment := positiveTenureAlignment
      tenureChannel := tenureChannel
      tenureChannelExact := rfl
      healthChannel := healthChannel
      healthChannelExact := rfl
      tenureChannelCarrierFromRootRead := HEq.rfl
      healthChannelCarrierFromRootRead := HEq.rfl
      futureBirthBearerExitFromRootRead := rfl
      tenureConsumer := tenureConsumer
      healthConsumer := healthConsumer
      tenureConsumerRootReadCarrierExact := HEq.rfl
      healthConsumerRootReadCarrierExact := HEq.rfl
      tenureConsumerFactorization := tenureConsumer.rootFactorization
      healthConsumerFactorization := healthConsumer.rootFactorization
      tenureConsumerPaymentNextExact :=
        tenureConsumer.paymentNext_is_consumerNext
      healthConsumerPaymentNextExact :=
        healthConsumer.paymentNext_is_consumerNext
      tenureConsumerNextExact := rfl
      healthConsumerNextExact := rfl
      externalLiability := externalLiability
      externalLiabilityFromPostPayment := HEq.rfl
      crossRootOccurrenceDistinct :=
        externalLiability.crossRootOccurrenceDistinct
      externalSourceOwnership :=
        externalLiability.sourceOwnedResidual
      externalRootConsumer :=
        externalLiability.rootConsumer
      localLedgerEmpty := futureBirth.localLedgerEmpty
      tenureNextExact := rfl
      healthNextExact := rfl
      nextPaidByExact := futureBirth.nextPaidOccurrence_exact
      healthAlignmentDeleted :=
        healthServiceBeneficiaryBearerAlignment_isEmpty oldVisit sourceIndex
          index }

namespace SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (countermodel :
    SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
      oldVisit sourceIndex index)

include countermodel

/-- All three authority faces inhabit one root and visit. -/
theorem sameOuterOccurrenceFaces :
    countermodel.positiveTenureAlignment.bearerFace.projection =
        ContributionCapacityPostSettlementRenewalProjection.birthBearerExit ∧
      countermodel.positiveTenureAlignment.channelFace.projection =
        ContributionCapacityPostSettlementRenewalProjection.essentialAccessChannel
          tenureAuthority ∧
      countermodel.healthFace.projection =
        ContributionCapacityPostSettlementRenewalProjection.essentialAccessChannel
          healthAuthority ∧
      countermodel.positiveTenureAlignment.bearerFace.projection ≠
        countermodel.positiveTenureAlignment.channelFace.projection ∧
      countermodel.positiveTenureAlignment.channelFace.projection ≠
        countermodel.healthFace.projection := by
  rw [countermodel.positiveTenureAlignment.bearerFaceExact,
    countermodel.positiveTenureAlignment.channelFaceExact,
    countermodel.healthFaceExact]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro equality
    cases equality
  · intro equality
    cases equality

/-- The health countermodel keeps every operational axis except alignment to
this particular `.t1` bearer. -/
theorem healthPaymentRouteServiceConsumerRemain :
    Nonempty (ExactFeasibleExitEdgeAt
        (geometryCompilerAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))
        ExitFutureCode.leave
        (channelSlotAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
          healthAuthority)) ∧
      Nonempty (RenewalResponsibilityConsumerAt
        (countermodel.actualExit.paymentOccurrence.installed
          ).operationalAuthority) ∧
      (countermodel.actualExit.paymentOccurrence.installed
        ).RootAnswerAndNextFactorizes ∧
      (channelSlotAt
        (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
        healthAuthority).val = 1 ∧
      IsEmpty (HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
        index) :=
  ⟨⟨countermodel.healthCarrier.feasible⟩,
    ⟨countermodel.healthCarrier.rootConsumer⟩,
    countermodel.healthCarrier.rootFactorization,
    rfl,
    countermodel.healthAlignmentDeleted⟩

/-- Tenure and health root reads share the event-selected embedded Payment
and settlement; their independently generated channel consumers return the
same outer paid next. -/
theorem channelsSharePaymentSettlementAndNext :
    countermodel.positiveTenureAlignment.channelCarrier.existingPaymentOccurrence =
        countermodel.actualExit.paymentOccurrence ∧
      countermodel.healthCarrier.existingPaymentOccurrence =
        countermodel.actualExit.paymentOccurrence ∧
      countermodel.positiveTenureAlignment.channelCarrier.existingActualSettlement =
        countermodel.actualExit.actualSettlement ∧
      countermodel.healthCarrier.existingActualSettlement =
        countermodel.actualExit.actualSettlement ∧
      countermodel.tenureChannel.actualNext =
        countermodel.healthChannel.actualNext ∧
      countermodel.tenureChannel.actualNext =
        countermodel.postPayment.nextPaidBy := by
  rw [countermodel.actualExitExact, countermodel.futureBirthExact]
  refine ⟨?_, ?_, ?_, ?_, ?_, countermodel.tenureNextExact⟩
  · exact
      countermodel.positiveTenureAlignment.channelCarrier
        |>.paymentOccurrence_eq_input
  · exact countermodel.healthCarrier.paymentOccurrence_eq_input
  · exact
      countermodel.positiveTenureAlignment.channelCarrier
        |>.actualSettlement_eq_input
  · exact countermodel.healthCarrier.actualSettlement_eq_input
  · exact countermodel.tenureNextExact.trans countermodel.healthNextExact.symm

/-- The bearer used by the positive service alignment is read from the
original admitted birth obligation.  No current live residual row is claimed. -/
theorem originalBirthBearerProvenance :
    countermodel.originalBirthAdmission =
        sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit ∧
      countermodel.originalBirthAdmission.obligation =
        contributionCapacityU8ObligationAt oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness
          (contributionCapacityU8GeneratedResidual oldVisit) ∧
      countermodel.originalBirthAdmission.obligation.bearer =
        contributionCapacityU8BearerAt oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness
          (contributionCapacityU8GeneratedResidual oldVisit) ∧
      exchangeLaw.bearerOfActor birthBearerWorker =
        countermodel.originalBirthAdmission.obligation.bearer :=
  ⟨countermodel.originalBirthAdmissionSourceExact,
    countermodel.originalBirthObligationExact,
    countermodel.originalBirthBearerExisting,
    countermodel.exitWorkerBearer_eq_originalBirthBearer⟩

/-- The outer post-root event owns the native write, external liability,
empty local ledger and successor.  The embedded M9 event remains separate. -/
theorem outerPaymentLiabilityAndNextRemain :
    countermodel.postPayment.write = PLift.up
        countermodel.outerRootEvent.occurrence.2.periodicExitGenerated ∧
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.compile
          countermodel.outerRootEvent.occurrence =
        .nativeWrite countermodel.postPayment.write ∧
      Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          countermodel.actualExit) ∧
      IsEmpty (OpenResponsibilityAt (JointSettlementNAt oldVisit)
        countermodel.outerRootEvent.occurrence.1) ∧
      countermodel.postPayment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index + 1) :=
  ⟨countermodel.postPayment.writeExact,
    countermodel.postPayment.compilerWriteExact,
    countermodel.externalSourceOwnership,
    countermodel.externalRootConsumer,
    countermodel.localLedgerEmpty,
    countermodel.nextPaidByExact⟩

/-- The old protected-interest observer sees the same value while only the
tenure root read aligns to the `.t1` bearer. -/
theorem sameVisiblePositiveAndNegative :
    protectedInterestReadout tenureAuthority =
        protectedInterestReadout healthAuthority ∧
      Nonempty (TenureServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
        index) ∧
      IsEmpty (HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
        index) :=
  ⟨protectedInterestReadout_same,
    ⟨countermodel.positiveTenureAlignment⟩,
    countermodel.healthAlignmentDeleted⟩

/-- Explicit outer/embedded stratification. -/
theorem outerAndEmbeddedOccurrencesRemainLayered :
    countermodel.outerRootEvent = countermodel.futureBirth.postRootEvent ∧
      countermodel.embeddedM9RootEvent =
        countermodel.embeddedM9Payment.rootOccurrence ∧
      countermodel.embeddedM9Payment =
        countermodel.actualExit.paymentOccurrence :=
  ⟨countermodel.outerRootEventExact,
    countermodel.embeddedM9RootEventExact,
    countermodel.embeddedM9PaymentExact⟩

end SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt

/-! ## No reconstruction and anti-smuggling controls -/

theorem remainingAuthorityCannotReconstructHealthAlignment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
          oldVisit sourceIndex index →
        HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index) :=
  ⟨fun reconstruct =>
    let countermodel :=
      sourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
        oldVisit sourceIndex index
    countermodel.healthAlignmentDeleted.false (reconstruct countermodel)⟩

theorem healthCarrierCannotReconstructHealthAlignment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (ServiceBeneficiaryAlignmentChannelCarrierAt oldVisit sourceIndex index
          healthAuthority →
        HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index) :=
  ⟨fun reconstruct =>
    let countermodel :=
      sourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
        oldVisit sourceIndex index
    countermodel.healthAlignmentDeleted.false
      (reconstruct countermodel.healthCarrier)⟩

theorem serviceBeneficiaryBearerAlignment_negativeControls
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let countermodel :=
    sourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
      oldVisit sourceIndex index
  fail_if_success exact
    (countermodel.healthCarrier :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.healthCarrier.serviceReceipt :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.healthCarrier.feasible :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.healthCarrier.paymentReceipt :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.healthCarrier.routeReceipt :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.healthCarrier.rootConsumer :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.healthConsumer :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.postPayment :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.externalLiability :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.postPayment.nextPaidBy :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.positiveTenureAlignment :
      HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  fail_if_success exact
    (countermodel.outerRootEvent :
      ExactTemporalCausalRootEventAt jointRoot.toAuthoritativeRoot.toLedgerRoot
        (temporalVisitAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)))
  fail_if_success exact
    (countermodel.embeddedM9RootEvent :
      ExactTemporalCausalRootEventAt
        (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
          ).toAuthoritativeRoot.toLedgerRoot
        (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
          index))
  fail_if_success exact countermodel.channel
  fail_if_success exact countermodel.actor
  fail_if_success exact countermodel.slot
  fail_if_success exact countermodel.registry
  fail_if_success exact countermodel.coverage
  fail_if_success exact countermodel.future
  fail_if_success exact countermodel.residualCarry
  fail_if_success exact countermodel.residualRow
  trivial

end
end M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity.sourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity.tenureServiceBeneficiaryBearerAlignmentAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity.SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt.healthPaymentRouteServiceConsumerRemain
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity.SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt.outerPaymentLiabilityAndNextRemain
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity.remainingAuthorityCannotReconstructHealthAlignment
