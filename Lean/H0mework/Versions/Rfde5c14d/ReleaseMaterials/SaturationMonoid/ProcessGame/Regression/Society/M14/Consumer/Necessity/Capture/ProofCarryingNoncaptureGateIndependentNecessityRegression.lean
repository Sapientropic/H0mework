import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Capture.Producer.SourceGeneratedNoncaptureGateIndependentNecessity

/-!
# Direct consumer of noncapture-gate independent necessity

At every canonical visit, an actual source-installed remove-capture reform
starts from a genuinely captured policy.  Payment, route, service, standing,
tenure, residual responsibility, row/ledger authority, generated next, and
all remaining renewal projections survive, but the source noncapture fibre
and actionable exit are empty.  The typed target disposition is not current
authority; its program and capacity one are realized by the generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingNoncaptureGateIndependentNecessityRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money Renewal
open UBI Policy Revision Capacity Space CrossingCost
open Settlement.SourceOwnedSettlementCompiler
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14EssentialAccessRelationFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14CaptureResponsibilityDispositionRegression
open M14ZeroCapacityCausalNonidentifiabilityRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14SourceRouteOutageRestoration
open M14PeriodicRouteOutageRestoration
open M14SourceGeneratedNoncaptureGateIndependentNecessity
open M14SourceGeneratedNoncaptureGateIndependentNecessity.SourceGeneratedNoncaptureGateIndependentNecessityAt

abbrev CanonicalNoncaptureGateCountermodelAt (depth : Nat) :=
  SourceGeneratedNoncaptureGateIndependentNecessityAt depth

def canonicalNoncaptureGateCountermodelAt
    (depth : Nat) : CanonicalNoncaptureGateCountermodelAt depth :=
  sourceGeneratedNoncaptureGateIndependentNecessityAt depth

abbrev NoncaptureRemainingEconomicAuthorityAt (depth : Nat) : Prop :=
  essentialAccessRelationCompiler.GeneratedInterestAt
      tenureActor tenureRelation ∧
    tenureActor = Money.exactCounterpartyActor exactResidualActivation ∧
    essentialAccessRelationCompiler.phaseStep tenureRelation = .tenure ∧
    essentialAccessRelationCompiler.RelationRoleAt
      tenureActor tenureRelation .target .tenureProvider ∧
    capturedProgram.purchasingPowerStanding =
      exitCapacityProgram.purchasingPowerStanding ∧
    Nonempty ((capturedGeometryCompilerAt depth).PaysForAt
      capturedProgram.purchasingPowerStanding ExitFutureCode.leave) ∧
    Nonempty ((capturedGeometryCompilerAt depth).RoutesAt
      ExitFutureCode.leave (firstServicedCrossingAt depth)) ∧
    Nonempty (ActualServiceAt depth)

abbrev NoncaptureResidualResponsibilityRemains : Prop :=
  fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured =
      exactOpenSettlement exactResidualActivation ∧
    OpenSettlementAt.residualBearer
        (fullCapture.captureSettlement ExitFutureCode.leave
          leave_is_captured) =
      OpenSettlementAt.residualBearer
        (exactOpenSettlement exactResidualActivation) ∧
    Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
      (exactOpenSettlement exactResidualActivation)) ∧
    Nonempty (SourceOwnsResponsibilityIncidence M3FiniteExchangeFixture.V
      (M3FiniteExchangeFixture.P.boundarySource
        capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
      (exactOpenSettlement exactResidualActivation).obligation) ∧
    capturedProgram.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
      capturedProgram.payment.nextGenerated

abbrev NoncaptureRemainingProjectionFactorizationsAt
    (depth : Nat) : Prop :=
  let countermodel := canonicalNoncaptureGateCountermodelAt depth
  countermodel.renewal.source.installed.RootAnswerAndNextFactorizes ∧
    countermodel.proofCarrying.RootAnswerAndNextFactorizes ∧
    countermodel.recognitionWitness.RootAnswerAndNextFactorizes ∧
    countermodel.mandate.RootAnswerAndNextFactorizes ∧
    countermodel.essentialService.RootAnswerAndNextFactorizes ∧
    countermodel.route.RootAnswerAndNextFactorizes ∧
    countermodel.commonClearing.RootAnswerAndNextFactorizes ∧
    countermodel.clearingBackstop.RootAnswerAndNextFactorizes

abbrev NoncaptureRemainingProjectionOutcomesAt
    (depth : Nat) : Prop :=
  let countermodel := canonicalNoncaptureGateCountermodelAt depth
  ubiRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.renewal.source.installed.active,
        countermodel.renewal.source.installed.payload⟩ ∧
    jointRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.proofCarrying.active,
        countermodel.proofCarrying.payload⟩ ∧
    recognitionWitnessRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.recognitionWitness.active,
        countermodel.recognitionWitness.payload⟩ ∧
    mandateRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.mandate.active, countermodel.mandate.payload⟩ ∧
    essentialServiceRestorationRecognition.law.toProjectionLaw.outcomeAt
        PUnit.unit (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.essentialService.active,
        countermodel.essentialService.payload⟩ ∧
    routeOutageRestorationRecognition.law.toProjectionLaw.outcomeAt
        PUnit.unit (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.route.active, countermodel.route.payload⟩ ∧
    commonClearingRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.commonClearing.active,
        countermodel.commonClearing.payload⟩ ∧
    clearingBackstopRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.clearingBackstop.active,
        countermodel.clearingBackstop.payload⟩

theorem noncaptureGateSourceDeleted_targetRealizedByGeneratedNext
    (depth : Nat) :
    IsEmpty (DeletedSourceNoncaptureAuthorityAt depth) ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
      IsEmpty
        ((capturedGeometryCompilerAt depth
          ).SourceGeneratedActionableExitRenewalAt) ∧
      temporalVisitAt depth ≠ temporalVisitAt (depth + 1) ∧
      (¬ noCapture.Captures ExitFutureCode.leave) ∧
      (canonicalNoncaptureGateCountermodelAt depth
        ).renewal.generatedNext.visit = temporalVisitAt (depth + 1) ∧
      (installedUBIAt (depth + 1)).payload.consumer.programAt =
        (canonicalNoncaptureGateCountermodelAt depth
          ).renewal.source.installed.payload.disposition.targetProgramAt ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 :=
  let countermodel := canonicalNoncaptureGateCountermodelAt depth
  ⟨countermodel.sourceNoncaptureDeleted,
    captured_nominal_capacity_eq_zero_at depth,
    capturedSourceActionableExit_isEmpty depth,
    SourceGeneratedNoncaptureGateIndependentNecessityAt.sourceAndTargetVisitsDistinct
      (depth := depth),
    countermodel.targetDispositionAndGeneratedNext.1,
    countermodel.targetDispositionAndGeneratedNext.2.1,
    countermodel.targetDispositionAndGeneratedNext.2.2.1,
    countermodel.targetDispositionAndGeneratedNext.2.2.2⟩

structure ProofCarryingNoncaptureGateIndependentNecessityCertificate : Prop where
  existingActualRepair : ProofCarryingExitRepairRenewalCertificate
  existingAccountedCapture : CaptureResponsibilityDispositionCertificate
  everyDepthCountermodel : ∀ depth : Nat,
    Nonempty (CanonicalNoncaptureGateCountermodelAt depth)
  everyDepthExactRootAndPayment : ∀ depth : Nat,
    let countermodel := canonicalNoncaptureGateCountermodelAt depth
    countermodel.renewal.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      (periodicSourceBackedPaymentAt depth).rootOccurrence =
        countermodel.renewal.rootOccurrence
  everyDepthSourceCaptureExact : ∀ depth : Nat,
    PriceCaptureSignatureAt depth
  everyDepthRemainingEconomicAuthority : ∀ depth : Nat,
    NoncaptureRemainingEconomicAuthorityAt depth
  residualResponsibilityRemains :
    NoncaptureResidualResponsibilityRemains
  everyDepthRowLedgerConsumerNext : ∀ depth : Nat,
    let countermodel := canonicalNoncaptureGateCountermodelAt depth
    countermodel.renewal.source.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      countermodel.renewal.ordinarySelectedWrite =
        countermodel.renewal.source.installed.temporalSelectedRow ∧
      countermodel.renewal.ordinarySelectedWrite.sourceRow.CommutesWithWorld ∧
      countermodel.renewal.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      Nonempty (RenewalResponsibilityConsumerAt
        countermodel.renewal.source.installed.operationalAuthority) ∧
      countermodel.renewal.source.installed.RootAnswerAndNextFactorizes ∧
      countermodel.renewal.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  everyDepthRemainingProjectionOutcomes : ∀ depth : Nat,
    NoncaptureRemainingProjectionOutcomesAt depth
  everyDepthRemainingProjectionFactorizations : ∀ depth : Nat,
    NoncaptureRemainingProjectionFactorizationsAt depth
  everyDepthDeletedAndTargetRealized : ∀ depth : Nat,
    IsEmpty (DeletedSourceNoncaptureAuthorityAt depth) ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
      IsEmpty
        ((capturedGeometryCompilerAt depth
          ).SourceGeneratedActionableExitRenewalAt) ∧
      temporalVisitAt depth ≠ temporalVisitAt (depth + 1) ∧
      (¬ noCapture.Captures ExitFutureCode.leave) ∧
      (canonicalNoncaptureGateCountermodelAt depth
        ).renewal.generatedNext.visit = temporalVisitAt (depth + 1) ∧
      (installedUBIAt (depth + 1)).payload.consumer.programAt =
        (canonicalNoncaptureGateCountermodelAt depth
          ).renewal.source.installed.payload.disposition.targetProgramAt ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  everyDepthNoRemainingReconstruction : ∀ depth : Nat,
    IsEmpty
      (CanonicalNoncaptureGateCountermodelAt depth →
        DeletedSourceNoncaptureAuthorityAt depth)

theorem proofCarryingNoncaptureGateIndependentNecessityDirectConsumer :
    ProofCarryingNoncaptureGateIndependentNecessityCertificate where
  existingActualRepair := proofCarryingExitRepairRenewalDirectConsumer
  existingAccountedCapture := captureResponsibilityDispositionDirectConsumer
  everyDepthCountermodel := fun depth =>
    ⟨canonicalNoncaptureGateCountermodelAt depth⟩
  everyDepthExactRootAndPayment := fun depth =>
    (canonicalNoncaptureGateCountermodelAt depth).exactRootAndPaymentRemain
  everyDepthSourceCaptureExact := fun depth =>
    (canonicalNoncaptureGateCountermodelAt depth).sourceSignature
  everyDepthRemainingEconomicAuthority := fun depth =>
    (canonicalNoncaptureGateCountermodelAt depth
      ).paymentStandingRouteServiceAndTenureRemain
  residualResponsibilityRemains :=
    (canonicalNoncaptureGateCountermodelAt 0
      ).residualBearerAndConsumerRemain
  everyDepthRowLedgerConsumerNext := fun depth =>
    (canonicalNoncaptureGateCountermodelAt depth
      ).rowLedgerConsumerAndNextRemain
  everyDepthRemainingProjectionOutcomes := fun depth =>
    (canonicalNoncaptureGateCountermodelAt depth
      ).everyRemainingProjectionActiveAtExactOccurrence
  everyDepthRemainingProjectionFactorizations := fun depth =>
    (canonicalNoncaptureGateCountermodelAt depth
      ).everyRemainingProjectionFactorizes
  everyDepthDeletedAndTargetRealized :=
    noncaptureGateSourceDeleted_targetRealizedByGeneratedNext
  everyDepthNoRemainingReconstruction :=
    remainingAuthorityCannotReconstructSourceNoncapture

theorem noncaptureGateNecessity_negativeControls (depth : Nat) : True := by
  let countermodel := canonicalNoncaptureGateCountermodelAt depth
  fail_if_success exact
    (countermodel.renewal : CanonicalNoncaptureGateCountermodelAt depth)
  fail_if_success exact
    (countermodel.route : CanonicalNoncaptureGateCountermodelAt depth)
  fail_if_success exact
    (countermodel.sourceSignature.captured :
      DeletedSourceNoncaptureAuthorityAt depth)
  fail_if_success exact
    (countermodel.renewal.source.installed.payload.disposition
      |>.target_uncaptured : DeletedSourceNoncaptureAuthorityAt depth)
  fail_if_success exact
    ((0 : Nat) : CanonicalNoncaptureGateCountermodelAt depth)
  fail_if_success exact countermodel.gateKind
  fail_if_success exact countermodel.coverage
  fail_if_success exact countermodel.history
  fail_if_success exact countermodel.future
  fail_if_success exact countermodel.completedFuture
  trivial

end
end M14ProofCarryingNoncaptureGateIndependentNecessityRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingNoncaptureGateIndependentNecessityRegression.noncaptureGateSourceDeleted_targetRealizedByGeneratedNext
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingNoncaptureGateIndependentNecessityRegression.proofCarryingNoncaptureGateIndependentNecessityDirectConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingNoncaptureGateIndependentNecessityRegression.noncaptureGateNecessity_negativeControls
