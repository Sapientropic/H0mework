import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Service.Producer.SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity

/-!
# Direct consumer of service-beneficiary/bearer alignment necessity

The tenure and health services are genuine root-read channels of one exact
post-settlement occurrence.  Tenure's first-slot receipt is now literally the
receipt carried by the root-read bearer exit and its relation witness names
the `.t1` Payment/exit/original-birth bearer.  Health keeps its own genuine
middle-slot service, Payment, route, consumer, factorization, external
liability and paid next, but cannot align to that bearer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth
open M14SourceGeneratedContributionCapacitySettlementConsumer
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity

abbrev CanonicalServiceBeneficiaryAlignmentCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
    oldVisit sourceIndex index

def canonicalServiceBeneficiaryAlignmentCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalServiceBeneficiaryAlignmentCountermodelAt oldVisit sourceIndex
      index :=
  sourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
    oldVisit sourceIndex index

abbrev CanonicalHealthServiceReceiptAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  (serviceCompilerAt
    (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
    ).ServesAt
      ((anomiePhaseAt
        (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
        ).served.get
          (channelSlotAt
            (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
            healthAuthority))
      (run.events.get
        (Fin.cast
          (actualSettlementAt
            (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
            ).eventsLength_eq_allocated.symm
          (channelSlotAt
            (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
            healthAuthority)))

abbrev CanonicalHealthFeasibleExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  ExactFeasibleExitEdgeAt
    (geometryCompilerAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))
    ExitFutureCode.leave
    (channelSlotAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
      healthAuthority)

structure ServiceBeneficiaryBearerAlignmentAuditAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (countermodel : CanonicalServiceBeneficiaryAlignmentCountermodelAt
      oldVisit sourceIndex index) : Prop where
  sameOuterFaces :
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
        countermodel.healthFace.projection
  positiveRootReads :
    countermodel.positiveTenureAlignment.bearerExit =
        Classical.choice
          countermodel.positiveTenureAlignment.bearerRootRead.down ∧
      countermodel.positiveTenureAlignment.channelCarrier =
        Classical.choice
          countermodel.positiveTenureAlignment.channelRootRead.down ∧
      countermodel.futureBirth.bearerExit =
        countermodel.positiveTenureAlignment.bearerExit
  positiveSlotAndLiteralService :
    countermodel.positiveTenureAlignment.channelSlot =
        firstSlotAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index) ∧
      HEq countermodel.positiveTenureAlignment.channelServiceReceipt
        countermodel.positiveTenureAlignment.bearerExit.feasibleEdge.serviceReceipt
  positiveRelationWitnessAndBearer :
    countermodel.positiveTenureAlignment.channelRelationWitness.1.actor
          essentialAccessRelationCompiler = birthBearerWorker ∧
      PurchasingPowerStandingAt.counterparty
          birthBearerExitCapacityProgram.purchasingPowerStanding =
        birthBearerWorker ∧
      exchangeLaw.bearerOfActor birthBearerWorker =
        sourceGeneratedLossAllocationMaterial.parentBearer ∧
      exchangeLaw.bearerOfActor
          (channelActor tenureAuthority) =
        ((countermodel.futureBirth.reopeningFutureBirth
          ).birthAdmission).obligation.bearer
  positivePaymentAndSettlement :
    countermodel.positiveTenureAlignment.channelCarrier.existingPaymentOccurrence =
        countermodel.positiveTenureAlignment.bearerExit.existingPaymentOccurrence ∧
      countermodel.positiveTenureAlignment.channelCarrier.existingActualSettlement =
        countermodel.positiveTenureAlignment.bearerExit.existingActualSettlement
  healthRootReadAndGenuineService :
    countermodel.healthCarrier = Classical.choice countermodel.healthRootRead.down ∧
      countermodel.healthCarrier.serviceReceipt =
        channelServiceReceiptAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
          healthAuthority ∧
      countermodel.healthCarrier.feasible =
        channelFeasibleExitAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
          healthAuthority ∧
      (channelSlotAt
        (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
        healthAuthority).val = 1
  healthOperationalAxes :
    Nonempty (ExactFeasibleExitEdgeAt
      (geometryCompilerAt
        (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))
      ExitFutureCode.leave
      (channelSlotAt
        (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
        healthAuthority)) ∧
      Nonempty (RenewalResponsibilityConsumerAt
        countermodel.actualExit.paymentOccurrence.installed.operationalAuthority) ∧
      countermodel.actualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes
  healthAlignmentEmpty : IsEmpty
    (HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  channelConsumersOwnRootReads :
    HEq countermodel.tenureConsumer.rootReadCarrier
        countermodel.positiveTenureAlignment.channelCarrier ∧
      HEq countermodel.healthConsumer.rootReadCarrier
        countermodel.healthCarrier ∧
      (countermodel.tenureChannel.actualExit.paymentOccurrence.installed
        ).RootAnswerAndNextFactorizes ∧
      (countermodel.healthChannel.actualExit.paymentOccurrence.installed
        ).RootAnswerAndNextFactorizes
  channelsSharePaymentSettlementAndNext :
    countermodel.positiveTenureAlignment.channelCarrier.existingPaymentOccurrence =
        countermodel.actualExit.paymentOccurrence ∧
      countermodel.healthCarrier.existingPaymentOccurrence =
        countermodel.actualExit.paymentOccurrence ∧
      countermodel.positiveTenureAlignment.channelCarrier.existingActualSettlement =
        countermodel.actualExit.actualSettlement ∧
      countermodel.healthCarrier.existingActualSettlement =
        countermodel.actualExit.actualSettlement ∧
      countermodel.tenureConsumer.actualNext = countermodel.postPayment.nextPaidBy ∧
      countermodel.healthConsumer.actualNext = countermodel.postPayment.nextPaidBy
  externalLiabilityExact : HEq countermodel.externalLiability
    countermodel.postPayment.liability
  externalResponsibility :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          countermodel.actualExit)
  crossRootOccurrenceDistinct :
    (Sum.inl countermodel.outerRootEvent :
      ExactTemporalCausalRootEventAt
          (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
            ).toAuthoritativeRoot.toLedgerRoot
          (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
            index) ⊕
        ExactTemporalCausalRootEventAt
          jointRoot.toAuthoritativeRoot.toLedgerRoot
          (temporalVisitAt
            (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))) ≠
      Sum.inr countermodel.embeddedM9RootEvent
  outerPaymentAndEmptyLedger :
    countermodel.postPayment.write =
        PLift.up countermodel.outerRootEvent.occurrence.2.periodicExitGenerated ∧
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.compile
          countermodel.outerRootEvent.occurrence =
        .nativeWrite countermodel.postPayment.write ∧
      IsEmpty (OpenResponsibilityAt (JointSettlementNAt oldVisit)
        countermodel.outerRootEvent.occurrence.1)
  nextPaidByExact : countermodel.postPayment.nextPaidBy =
    contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index + 1)
  originalBirthIsSettledProvenance :
    countermodel.originalBirthAdmission =
        sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit ∧
      (countermodel.futureBirth.reopeningFutureBirth
        ).residualCarry.sourceEntry =
        (settlementResidualCurrentAt oldVisit sourceIndex).entry ∧
      countermodel.futureBirth.residualTerminalReceipt =
        countermodel.futureBirth.residualSettlement.receipt ∧
      Nonempty (ProofCarryingContributionCapacityJointSettlementCertificateAt
        oldVisit sourceIndex)
  sameVisiblePositiveAndNegative :
    protectedInterestReadout tenureAuthority =
        protectedInterestReadout healthAuthority ∧
      Nonempty (TenureServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
        index) ∧
      IsEmpty (HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
        index)
  remainingCannotReconstruct : IsEmpty
    (CanonicalServiceBeneficiaryAlignmentCountermodelAt oldVisit sourceIndex
      index →
        HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)
  healthCarrierCannotReconstruct : IsEmpty
    (ServiceBeneficiaryAlignmentChannelCarrierAt oldVisit sourceIndex index
      healthAuthority →
        HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index)

theorem serviceBeneficiaryBearerAlignmentAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ServiceBeneficiaryBearerAlignmentAuditAt
      (canonicalServiceBeneficiaryAlignmentCountermodelAt oldVisit sourceIndex
        index) := by
  let countermodel :=
    canonicalServiceBeneficiaryAlignmentCountermodelAt oldVisit sourceIndex
      index
  exact
    { sameOuterFaces := countermodel.sameOuterOccurrenceFaces
      positiveRootReads :=
        ⟨countermodel.positiveTenureAlignment.bearerExitFromRootRead,
          countermodel.positiveTenureAlignment.channelCarrierFromRootRead,
          countermodel.futureBirthBearerExitFromRootRead⟩
      positiveSlotAndLiteralService :=
        ⟨countermodel.positiveTenureAlignment.channelSlot_eq_exitSlot,
          countermodel.positiveTenureAlignment
            |>.channelServiceReceipt_eq_exitServiceReceipt⟩
      positiveRelationWitnessAndBearer :=
        ⟨countermodel.positiveTenureAlignment
            |>.relationWitnessActor_eq_exitWorker,
          countermodel.positiveTenureAlignment
            |>.bearerStandingCounterparty_eq_exitWorker,
          countermodel.positiveTenureAlignment
            |>.bearerWorker_eq_existingParent,
          countermodel.positiveTenureAlignment
            |>.channelBearer_eq_originalBirthBearer⟩
      positivePaymentAndSettlement :=
        ⟨countermodel.positiveTenureAlignment
            |>.channelPayment_eq_bearerPayment,
          countermodel.positiveTenureAlignment
            |>.channelSettlement_eq_bearerSettlement⟩
      healthRootReadAndGenuineService :=
        ⟨countermodel.healthCarrierFromRootRead,
          countermodel.healthCarrier.serviceReceiptExact,
          countermodel.healthCarrier.feasibleExact,
          rfl⟩
      healthOperationalAxes :=
        ⟨⟨countermodel.healthCarrier.feasible⟩,
          ⟨countermodel.healthCarrier.rootConsumer⟩,
          countermodel.healthCarrier.rootFactorization⟩
      healthAlignmentEmpty := countermodel.healthAlignmentDeleted
      channelConsumersOwnRootReads :=
        ⟨countermodel.tenureConsumerRootReadCarrierExact,
          countermodel.healthConsumerRootReadCarrierExact,
          countermodel.tenureConsumerFactorization,
          countermodel.healthConsumerFactorization⟩
      channelsSharePaymentSettlementAndNext :=
        ⟨(countermodel.channelsSharePaymentSettlementAndNext).1,
          (countermodel.channelsSharePaymentSettlementAndNext).2.1,
          (countermodel.channelsSharePaymentSettlementAndNext).2.2.1,
          (countermodel.channelsSharePaymentSettlementAndNext).2.2.2.1,
          countermodel.tenureConsumerNextExact,
          countermodel.healthConsumerNextExact⟩
      externalLiabilityExact :=
        countermodel.externalLiabilityFromPostPayment
      externalResponsibility :=
        ⟨countermodel.externalSourceOwnership,
          countermodel.externalRootConsumer⟩
      crossRootOccurrenceDistinct := countermodel.crossRootOccurrenceDistinct
      outerPaymentAndEmptyLedger :=
        ⟨countermodel.postPayment.writeExact,
          countermodel.postPayment.compilerWriteExact,
          countermodel.localLedgerEmpty⟩
      nextPaidByExact := countermodel.nextPaidByExact
      originalBirthIsSettledProvenance :=
        ⟨countermodel.originalBirthAdmissionSourceExact,
          countermodel.futureBirth.carriedResidual_eq_settlementOrigin,
          countermodel.futureBirth.residualTerminalReceipt_exact,
          ⟨countermodel.futureBirth.jointSettlementComplete⟩⟩
      sameVisiblePositiveAndNegative :=
        countermodel.sameVisiblePositiveAndNegative
      remainingCannotReconstruct :=
        remainingAuthorityCannotReconstructHealthAlignment oldVisit
          sourceIndex index
      healthCarrierCannotReconstruct :=
        healthCarrierCannotReconstructHealthAlignment oldVisit sourceIndex
          index }

theorem serviceReceiptConsumerLiabilityOrNextCannotReconstructHealthAlignment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let countermodel :=
      canonicalServiceBeneficiaryAlignmentCountermodelAt oldVisit sourceIndex
        index
    IsEmpty
        (CanonicalHealthServiceReceiptAt oldVisit sourceIndex index →
          HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index) ∧
      IsEmpty
        (CanonicalHealthFeasibleExitAt oldVisit sourceIndex index →
          HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index) ∧
      IsEmpty
        ((ServiceBeneficiaryAlignmentChannelCarrierAt oldVisit sourceIndex index
            healthAuthority) →
          HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index) ∧
      IsEmpty
        ((ProofCarryingContributionCapacityPostSettlementChannelConsumerAt
            countermodel.healthChannel) →
          HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index) ∧
      IsEmpty
        ((PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex index
            countermodel.outerRootEvent countermodel.actualExit) →
          HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index) ∧
      IsEmpty
        ((countermodel.postPayment.nextPaidBy =
            contributionCapacityPostSettlementRenewalEmitted oldVisit
              sourceIndex
              (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index +
                1)) →
          HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index) := by
  let countermodel :=
    canonicalServiceBeneficiaryAlignmentCountermodelAt oldVisit sourceIndex
      index
  exact
    ⟨⟨fun reconstruct => countermodel.healthAlignmentDeleted.false
        (reconstruct countermodel.healthCarrier.serviceReceipt)⟩,
      ⟨fun reconstruct => countermodel.healthAlignmentDeleted.false
        (reconstruct countermodel.healthCarrier.feasible)⟩,
      healthCarrierCannotReconstructHealthAlignment oldVisit sourceIndex index,
      ⟨fun reconstruct => countermodel.healthAlignmentDeleted.false
        (reconstruct countermodel.healthConsumer)⟩,
      ⟨fun reconstruct => countermodel.healthAlignmentDeleted.false
        (reconstruct countermodel.externalLiability)⟩,
      ⟨fun reconstruct => countermodel.healthAlignmentDeleted.false
        (reconstruct countermodel.nextPaidByExact)⟩⟩

structure ProofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityCertificate :
    Prop where
  everyCountermodel : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty (CanonicalServiceBeneficiaryAlignmentCountermodelAt oldVisit
      sourceIndex index)
  everyAudit : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    ServiceBeneficiaryBearerAlignmentAuditAt
      (canonicalServiceBeneficiaryAlignmentCountermodelAt oldVisit sourceIndex
        index)
  everyFragmentNoReconstruction :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      let countermodel :=
        canonicalServiceBeneficiaryAlignmentCountermodelAt oldVisit sourceIndex
          index
      IsEmpty
          (CanonicalHealthServiceReceiptAt oldVisit sourceIndex index →
            HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
              index) ∧
        IsEmpty
          (CanonicalHealthFeasibleExitAt oldVisit sourceIndex index →
            HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
              index) ∧
        IsEmpty
          ((ServiceBeneficiaryAlignmentChannelCarrierAt oldVisit sourceIndex
              index healthAuthority) →
            HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
              index) ∧
        IsEmpty
          ((ProofCarryingContributionCapacityPostSettlementChannelConsumerAt
              countermodel.healthChannel) →
            HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
              index) ∧
        IsEmpty
          ((PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
              index countermodel.outerRootEvent countermodel.actualExit) →
            HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
              index) ∧
        IsEmpty
          ((countermodel.postPayment.nextPaidBy =
              contributionCapacityPostSettlementRenewalEmitted oldVisit
                sourceIndex
                (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex
                    index +
                  1)) →
            HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
              index)

theorem proofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityDirectConsumer :
    ProofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityCertificate where
  everyCountermodel := fun oldVisit sourceIndex index =>
    ⟨canonicalServiceBeneficiaryAlignmentCountermodelAt oldVisit sourceIndex
      index⟩
  everyAudit := serviceBeneficiaryBearerAlignmentAuditAt
  everyFragmentNoReconstruction :=
    serviceReceiptConsumerLiabilityOrNextCannotReconstructHealthAlignment

theorem serviceBeneficiaryBearerAlignmentNecessity_negativeControls
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True :=
  serviceBeneficiaryBearerAlignment_negativeControls oldVisit sourceIndex index

end
end M14ProofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityRegression.serviceBeneficiaryBearerAlignmentAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityRegression.serviceReceiptConsumerLiabilityOrNextCannotReconstructHealthAlignment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityRegression.proofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityDirectConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityRegression.serviceBeneficiaryBearerAlignmentNecessity_negativeControls
