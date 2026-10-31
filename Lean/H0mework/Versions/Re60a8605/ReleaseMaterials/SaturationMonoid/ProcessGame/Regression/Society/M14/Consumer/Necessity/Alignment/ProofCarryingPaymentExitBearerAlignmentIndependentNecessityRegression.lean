import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Alignment.Producer.SourceGeneratedPaymentExitBearerAlignmentIndependentNecessity
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Payment.Consumer.ProofCarryingContributionCapacityReopeningRuntimePayment

/-!
# Direct consumer of Payment--exit--bearer alignment necessity

One exact reopening occurrence supplies two dependent faces.  The legacy
renewal keeps an embedded source-backed M9 Payment, route, actual service and
capacity one but does not align its `.t0` exit worker with the Payment
counterparty and carried residual bearer.  The installed bearer face consumes
the same embedded Payment and settlement and supplies the positive `.t1`
alignment.  The outer occurrence alone owns the Fin-3 write, consumer and
generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPaymentExitBearerAlignmentIndependentNecessityRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Exchange Settlement Money UBI Renewal
open Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacityReopeningResidualCarry
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth
open M14ProofCarryingContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth
open M14SourceGeneratedPaymentExitBearerAlignmentIndependentNecessity

abbrev CanonicalAlignmentCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt oldVisit
    sourceIndex index

def canonicalAlignmentCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalAlignmentCountermodelAt oldVisit sourceIndex index :=
  sourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt oldVisit
    sourceIndex index

structure PaymentExitBearerAlignmentAuditAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (countermodel : CanonicalAlignmentCountermodelAt oldVisit sourceIndex
      index) : Prop where
  sameOuterFaces :
    countermodel.renewalFace.projection =
        ContributionCapacityReopeningProjection.renewal ∧
      countermodel.bearerFace.projection =
        ContributionCapacityReopeningProjection.birthBearerExit ∧
      countermodel.renewalFace.projection ≠
        countermodel.bearerFace.projection
  outerRootEventExact :
    countermodel.outerRootEvent =
      contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
        sourceIndex index
  legacyRootReadExact : countermodel.legacyRootRead =
    contributionCapacityReopeningRootGeneratedRenewalAt oldVisit sourceIndex
      (index + 1)
  legacyActualExitFromRootRead : countermodel.legacyActualExit =
    Classical.choice countermodel.legacyRootRead
  bearerRootReadExact : countermodel.alignedBearerExit =
    Classical.choice countermodel.futureBirth.installedBearerExitAuthority.down
  positiveAlignmentFromBearerRootRead :
    countermodel.positiveAlignment.installedBearerExit =
      countermodel.alignedBearerExit
  positiveEmbeddedPaymentMatchesBearerFace :
    (paymentExitAlignmentLegacyActualExitAt oldVisit sourceIndex index
      ).paymentOccurrence =
      countermodel.positiveAlignment.installedBearerExit.existingPaymentOccurrence
  embeddedPaymentAndService :
    countermodel.legacyActualExit.paymentOccurrence =
        countermodel.futureBirth.actualExit.paymentOccurrence ∧
      countermodel.alignedBearerExit.existingPaymentOccurrence =
        countermodel.legacyActualExit.paymentOccurrence ∧
      countermodel.alignedBearerExit.existingActualSettlement =
        countermodel.legacyActualExit.actualSettlement ∧
      countermodel.legacyActualExit.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt
            (contributionCapacityFutureBirthDepth sourceIndex index))
  legacyFeasibleExit : Nonempty (ExactFeasibleExitEdgeAt
    (geometryCompilerAt
      (contributionCapacityFutureBirthDepth sourceIndex index))
    ExitFutureCode.leave
    (firstSlotAt (contributionCapacityFutureBirthDepth sourceIndex index)))
  alignedFeasibleExit : Nonempty (ExactFeasibleExitEdgeAt
    (birthBearerGeometryCompilerAt
      (contributionCapacityFutureBirthDepth sourceIndex index))
    ExitFutureCode.leave
    (firstSlotAt (contributionCapacityFutureBirthDepth sourceIndex index)))
  legacyActionableRenewal : Nonempty
    ((geometryCompilerAt
      (contributionCapacityFutureBirthDepth sourceIndex index)
      ).SourceGeneratedActionableExitRenewalAt)
  alignedActionableRenewal : Nonempty
    ((birthBearerGeometryCompilerAt
      (contributionCapacityFutureBirthDepth sourceIndex index)
      ).SourceGeneratedActionableExitRenewalAt)
  legacyUncaptured : ¬ noCapture.Captures ExitFutureCode.leave
  alignedUncaptured : ¬ birthBearerNoCapture.Captures ExitFutureCode.leave
  embeddedRootFactorization :
    countermodel.legacyActualExit.paymentOccurrence.installed
      |>.RootAnswerAndNextFactorizes
  sameVisibleCapacityOne :
    (geometryCompilerAt
        (contributionCapacityFutureBirthDepth sourceIndex index)
      ).actionableExitCapacity = 1 ∧
      (birthBearerGeometryCompilerAt
        (contributionCapacityFutureBirthDepth sourceIndex index)
      ).actionableExitCapacity = 1
  rootReceiptNativeWriteExact :
    (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
      sourceIndex index).wholeLedgerWriteBack =
      (CanonicalReopeningCompilerAt oldVisit sourceIndex).compile
        (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
          sourceIndex index).occurrence
  everyOuterRowEvolved : ∀ entryIndex : Fin 3,
    (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
      sourceIndex index).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityReopeningCurrentEntryAt oldVisit
          (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
            sourceIndex index) entryIndex) =
      .evolved
        (contributionCapacityReopeningRuntimePaymentRowEvolutionAt oldVisit
          sourceIndex index entryIndex)
  compilerNativeWriteExact :
    (CanonicalReopeningCompilerAt oldVisit sourceIndex).compile
        (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
          sourceIndex index).occurrence =
      .nativeWrite
        (contributionCapacityReopeningRuntimePaymentAt oldVisit sourceIndex
          index) rfl
        (contributionCapacityReopeningEmitted oldVisit sourceIndex
          (AlignmentReopeningSourceEventAt oldVisit sourceIndex)
          (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
            sourceIndex index + 1))
        (contributionCapacityReopeningEvolution oldVisit sourceIndex
          (AlignmentReopeningSourceEventAt oldVisit sourceIndex)
          (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
            sourceIndex index).occurrence)
  residualRowExact :
    contributionCapacityReopeningCurrentEntryAt oldVisit
        (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
          sourceIndex index) (2 : Fin 3) =
      countermodel.residualCarry.sourceEntry
  consumerProjectionExact : countermodel.residualConsumer.projection =
    ContributionCapacityReopeningProjection.consumer
  birthAdmissionSourceExact : countermodel.birthAdmission =
    sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
  residualCarryRuntimeExact : countermodel.residualCarry =
    contributionCapacityReopeningRuntimeResidualCarryAt oldVisit sourceIndex
      index
  birthObligationExact : countermodel.birthAdmission.obligation =
    contributionCapacityU8ObligationAt oldVisit
      exactSourceGeneratedLossAllocationMaterialWitness
      (contributionCapacityU8GeneratedResidual oldVisit)
  residualBirthToCarryBearer :
    countermodel.birthAdmission.obligation.bearer =
        contributionCapacityU8BearerAt oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness
          (contributionCapacityU8GeneratedResidual oldVisit) ∧
      contributionCapacityU8BearerAt oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness
          (contributionCapacityU8GeneratedResidual oldVisit) =
        sourceGeneratedLossAllocationMaterial.parentBearer ∧
      countermodel.birthAdmission.obligation.bearer =
        sourceGeneratedLossAllocationMaterial.parentBearer
  consumerUsesOuterOccurrence :
    contributionCapacityReopenedInquiryEventAt oldVisit sourceIndex index =
      ULift.up
        (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
          sourceIndex index).occurrence
  outerSuccessor : Nonempty
    (SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
        sourceIndex index).occurrence
      (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
        sourceIndex index).wholeLedgerWriteBack)
  generatedNextExact :
    contributionCapacityReopeningRuntimeNextPaidBy oldVisit sourceIndex index =
      contributionCapacityReopeningEmitted oldVisit sourceIndex
        (AlignmentReopeningSourceEventAt oldVisit sourceIndex)
        (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
          sourceIndex index + 1)
  legacyAlignmentEmpty :
    IsEmpty (LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth)
  positiveAlignment :
    Nonempty (PositivePaymentExitBearerAlignmentAt countermodel.futureBirth)
  remainingCannotReconstruct : IsEmpty
    ((remaining : CanonicalAlignmentCountermodelAt oldVisit sourceIndex index) →
      LegacyPaymentExitBearerAlignmentAt remaining.futureBirth)

theorem paymentExitBearerAlignmentAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaymentExitBearerAlignmentAuditAt
      (canonicalAlignmentCountermodelAt oldVisit sourceIndex index) := by
  let countermodel :=
    canonicalAlignmentCountermodelAt oldVisit sourceIndex index
  exact
    { sameOuterFaces := countermodel.sameOuterOccurrenceFaces
      outerRootEventExact := by
        rw [countermodel.outerRootEventExact, countermodel.futureBirthExact]
      legacyRootReadExact := countermodel.legacyRootReadExact
      legacyActualExitFromRootRead := Subsingleton.elim _ _
      bearerRootReadExact := countermodel.alignedBearerExitFromRootRead
      positiveAlignmentFromBearerRootRead :=
        countermodel.positiveAlignment.installedBearerExitFromRootRead.trans
          countermodel.alignedBearerExitFromRootRead.symm
      positiveEmbeddedPaymentMatchesBearerFace :=
        countermodel.positiveAlignment.embeddedPaymentMatchesInstalled
      embeddedPaymentAndService :=
        countermodel.embeddedPaymentAndServiceRemain
      legacyFeasibleExit := ⟨countermodel.legacyActualExit.feasibleEdge⟩
      alignedFeasibleExit := ⟨countermodel.alignedBearerExit.feasibleEdge⟩
      legacyActionableRenewal :=
        ⟨countermodel.legacyActualExit.actionableRenewal⟩
      alignedActionableRenewal :=
        ⟨countermodel.alignedBearerExit.actionableRenewal⟩
      legacyUncaptured := by simp [noCapture]
      alignedUncaptured := by simp [birthBearerNoCapture]
      embeddedRootFactorization :=
        countermodel.legacyActualExit.rootFactorization
      sameVisibleCapacityOne :=
        ⟨countermodel.legacyActualExit.exactCapacity,
          countermodel.alignedBearerExit.exactCapacity⟩
      rootReceiptNativeWriteExact :=
        countermodel.outerRuntimePayment.rootReceiptNativeWriteExact
      everyOuterRowEvolved :=
        countermodel.outerRuntimePayment.everyRowEvolved
      compilerNativeWriteExact :=
        countermodel.outerRuntimePayment.compilerNativeWriteExact
      residualRowExact := by
        rw [countermodel.residualCarryExact]
        exact countermodel.futureBirth.laterRootEvent_entry_eq_residualCarry
      consumerProjectionExact := by
        rw [countermodel.residualConsumerExact]
        rfl
      birthAdmissionSourceExact := countermodel.birthAdmissionSourceExact
      residualCarryRuntimeExact := countermodel.residualCarryRuntimeExact
      birthObligationExact := countermodel.birthObligationExact
      residualBirthToCarryBearer :=
        ⟨countermodel.birthObligationBearerExact,
          countermodel.carriedResidualBearerExact,
          countermodel.birthBearerCarriedParentExact⟩
      consumerUsesOuterOccurrence := rfl
      outerSuccessor :=
        ⟨contributionCapacityReopeningRuntimePaymentSuccessorAt oldVisit
          sourceIndex index⟩
      generatedNextExact :=
        contributionCapacityReopeningRuntimeNextPaidBy_exact oldVisit
          sourceIndex index
      legacyAlignmentEmpty := countermodel.deletedLegacyAlignment
      positiveAlignment := ⟨countermodel.positiveAlignment⟩
      remainingCannotReconstruct :=
        remainingAuthorityCannotReconstructLegacyAlignment oldVisit
          sourceIndex index }

theorem rawCapacityPaymentRouteOrServiceCannotReconstructAlignment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let countermodel :=
      canonicalAlignmentCountermodelAt oldVisit sourceIndex index
    IsEmpty
        (((geometryCompilerAt
            (contributionCapacityFutureBirthDepth sourceIndex index)
          ).actionableExitCapacity = 1) →
          LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth) ∧
      IsEmpty
        (PeriodicSourceBackedPaymentAt
            (contributionCapacityFutureBirthDepth sourceIndex index) →
          LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth) ∧
      IsEmpty
        (ExactServedCrossingDebitedRunAt
            (anomiePhaseAt
              (contributionCapacityFutureBirthDepth sourceIndex index))
            debited
            (serviceCompilerAt
              (contributionCapacityFutureBirthDepth sourceIndex index)) →
          LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth) ∧
      IsEmpty
        (ExactFeasibleExitEdgeAt
            (geometryCompilerAt
              (contributionCapacityFutureBirthDepth sourceIndex index))
            ExitFutureCode.leave
            (firstSlotAt
              (contributionCapacityFutureBirthDepth sourceIndex index)) →
          LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth) := by
  let countermodel :=
    canonicalAlignmentCountermodelAt oldVisit sourceIndex index
  exact
    ⟨⟨fun reconstruct => countermodel.deletedLegacyAlignment.false
        (reconstruct countermodel.legacyActualExit.exactCapacity)⟩,
      ⟨fun reconstruct => countermodel.deletedLegacyAlignment.false
        (reconstruct countermodel.embeddedM9Payment)⟩,
      ⟨fun reconstruct => countermodel.deletedLegacyAlignment.false
        (reconstruct countermodel.legacyActualExit.actualSettlement)⟩,
      ⟨fun reconstruct => countermodel.deletedLegacyAlignment.false
        (reconstruct countermodel.legacyActualExit.feasibleEdge)⟩⟩

theorem outerAndEmbeddedAuthorities_cannot_retype
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let countermodel :=
    canonicalAlignmentCountermodelAt oldVisit sourceIndex index
  fail_if_success exact
    (countermodel.outerRootEvent :
      ExactTemporalCausalRootEventAt jointRoot.toAuthoritativeRoot.toLedgerRoot
        (temporalVisitAt
          (contributionCapacityFutureBirthDepth sourceIndex index)))
  fail_if_success exact
    (countermodel.embeddedM9RootEvent :
      ExactTemporalCausalRootEventAt
        (AlignmentReopeningRootAt oldVisit sourceIndex
          ).toAuthoritativeRoot.toLedgerRoot
        (contributionCapacityReopenedVisitAt oldVisit sourceIndex index))
  fail_if_success exact countermodel.outerRootEvent.embeddedPayment
  fail_if_success exact countermodel.embeddedM9RootEvent.wholeLedgerWriteBack
  trivial

structure ProofCarryingPaymentExitBearerAlignmentIndependentNecessityCertificate :
    Prop where
  everyCountermodel : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty (CanonicalAlignmentCountermodelAt oldVisit sourceIndex index)
  everyAudit : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    PaymentExitBearerAlignmentAuditAt
      (canonicalAlignmentCountermodelAt oldVisit sourceIndex index)
  everyRawAxisNoReconstruction :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      let countermodel :=
        canonicalAlignmentCountermodelAt oldVisit sourceIndex index
      IsEmpty
          (((geometryCompilerAt
              (contributionCapacityFutureBirthDepth sourceIndex index)
            ).actionableExitCapacity = 1) →
            LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth) ∧
        IsEmpty
          (PeriodicSourceBackedPaymentAt
              (contributionCapacityFutureBirthDepth sourceIndex index) →
            LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth) ∧
        IsEmpty
          (ExactServedCrossingDebitedRunAt
              (anomiePhaseAt
                (contributionCapacityFutureBirthDepth sourceIndex index))
              debited
              (serviceCompilerAt
                (contributionCapacityFutureBirthDepth sourceIndex index)) →
            LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth) ∧
        IsEmpty
          (ExactFeasibleExitEdgeAt
              (geometryCompilerAt
                (contributionCapacityFutureBirthDepth sourceIndex index))
              ExitFutureCode.leave
              (firstSlotAt
                (contributionCapacityFutureBirthDepth sourceIndex index)) →
            LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth)

theorem proofCarryingPaymentExitBearerAlignmentIndependentNecessityDirectConsumer :
    ProofCarryingPaymentExitBearerAlignmentIndependentNecessityCertificate where
  everyCountermodel := fun oldVisit sourceIndex index =>
    ⟨canonicalAlignmentCountermodelAt oldVisit sourceIndex index⟩
  everyAudit := paymentExitBearerAlignmentAuditAt
  everyRawAxisNoReconstruction :=
    rawCapacityPaymentRouteOrServiceCannotReconstructAlignment

theorem paymentExitBearerAlignmentNecessity_negativeControls
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  exact paymentExitBearerAlignment_negativeControls oldVisit sourceIndex index

end
end M14ProofCarryingPaymentExitBearerAlignmentIndependentNecessityRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaymentExitBearerAlignmentIndependentNecessityRegression.paymentExitBearerAlignmentAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaymentExitBearerAlignmentIndependentNecessityRegression.rawCapacityPaymentRouteOrServiceCannotReconstructAlignment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaymentExitBearerAlignmentIndependentNecessityRegression.proofCarryingPaymentExitBearerAlignmentIndependentNecessityDirectConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaymentExitBearerAlignmentIndependentNecessityRegression.paymentExitBearerAlignmentNecessity_negativeControls
