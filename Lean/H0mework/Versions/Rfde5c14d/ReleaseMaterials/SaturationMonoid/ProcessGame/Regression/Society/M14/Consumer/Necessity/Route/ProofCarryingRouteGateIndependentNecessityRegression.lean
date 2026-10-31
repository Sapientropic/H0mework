import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Route.Producer.SourceGeneratedRouteGateIndependentNecessity
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Route.ProofCarryingPeriodicRouteOutageRestorationRegression

/-!
# Direct consumer of route-gate independent necessity

At every canonical finite visit, the source route authority is absent and
the exact exit geometry has capacity zero.  This does not erase the literal
root occurrence, periodic Payment, standing, tenure, noncapture, service,
row, whole ledger, consumer, next, or any of the seven other installed
renewal projections.  No function from that complete remaining carrier can
reconstruct the source route.  The route receipt appears only at the
Payment-generated next visit, where capacity is one.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingRouteGateIndependentNecessityRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement Money Renewal UBI Policy
open Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14EssentialAccessRelationFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceRouteOutageRestoration
open M14PeriodicRouteOutageRestoration
open M14ProofCarryingPeriodicRouteOutageRestorationRegression
open M14SourceGeneratedRouteGateIndependentNecessity
open M14SourceGeneratedRouteGateIndependentNecessity.SourceGeneratedRouteGateIndependentNecessityAt

abbrev CanonicalRouteGateCountermodelAt (depth : Nat) :=
  SourceGeneratedRouteGateIndependentNecessityAt depth

def canonicalRouteGateCountermodelAt
    (depth : Nat) : CanonicalRouteGateCountermodelAt depth :=
  sourceGeneratedRouteGateIndependentNecessityAt depth

abbrev RouteGateRemainingEconomicAuthorityAt (depth : Nat) : Prop :=
  essentialAccessRelationCompiler.GeneratedInterestAt
      tenureActor tenureRelation ∧
    tenureActor = Money.exactCounterpartyActor exactResidualActivation ∧
    essentialAccessRelationCompiler.phaseStep tenureRelation = .tenure ∧
    essentialAccessRelationCompiler.RelationRoleAt
      tenureActor tenureRelation .target .tenureProvider ∧
    (¬ noCapture.Captures ExitFutureCode.leave) ∧
    Nonempty (SourceBackedUBIPaymentReceiptAt
      exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave) ∧
    Nonempty (ExactServedCrossingDebitedRunAt
      (anomiePhaseAt depth) debited (serviceCompilerAt depth))

abbrev RouteGateSiblingFactorizationsAt (depth : Nat) : Prop :=
  let countermodel := canonicalRouteGateCountermodelAt depth
  countermodel.proofCarrying.RootAnswerAndNextFactorizes ∧
    countermodel.ubi.RootAnswerAndNextFactorizes ∧
    countermodel.recognitionWitness.RootAnswerAndNextFactorizes ∧
    countermodel.mandate.RootAnswerAndNextFactorizes ∧
    countermodel.essentialService.RootAnswerAndNextFactorizes ∧
    countermodel.commonClearing.RootAnswerAndNextFactorizes ∧
    countermodel.clearingBackstop.RootAnswerAndNextFactorizes

abbrev RouteGateSiblingActiveOutcomesAt (depth : Nat) : Prop :=
  let countermodel := canonicalRouteGateCountermodelAt depth
  jointRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.proofCarrying.active,
        countermodel.proofCarrying.payload⟩ ∧
    ubiRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.ubi.active, countermodel.ubi.payload⟩ ∧
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
    commonClearingRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.commonClearing.active,
        countermodel.commonClearing.payload⟩ ∧
    clearingBackstopRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      .inl ⟨countermodel.clearingBackstop.active,
        countermodel.clearingBackstop.payload⟩

abbrev RouteProjectionIndependentFromCurrentSiblings : Prop :=
  jointRouteOutageRestorationProjection ≠
      jointEssentialServiceRestorationProjection ∧
    jointRouteOutageRestorationProjection ≠ jointMandateProjection ∧
    jointRouteOutageRestorationProjection ≠
      jointRecognitionWitnessProjection ∧
    jointRouteOutageRestorationProjection ≠ jointUBIProjection ∧
    jointRouteOutageRestorationProjection ≠
      jointProofCarryingProjection ∧
    jointRouteOutageRestorationProjection ≠ jointInquiryProjection ∧
    jointRouteOutageRestorationProjection ≠ jointFailureProjection ∧
    jointRouteOutageRestorationProjection ≠ jointCommonClearingProjection ∧
    jointRouteOutageRestorationProjection ≠ jointClearingBackstopProjection

theorem routeGateRemainingEconomicAuthorityAt (depth : Nat) :
    RouteGateRemainingEconomicAuthorityAt depth :=
  (canonicalRouteGateCountermodelAt depth
    ).paymentStandingTenureAndServiceRemain

theorem routeGateSiblingActiveOutcomesAt (depth : Nat) :
    RouteGateSiblingActiveOutcomesAt depth :=
  (canonicalRouteGateCountermodelAt depth
    ).everySiblingActiveAtExactOccurrence

theorem routeGateSiblingFactorizationsAt (depth : Nat) :
    RouteGateSiblingFactorizationsAt depth :=
  (canonicalRouteGateCountermodelAt depth).everySiblingFactorizes

theorem routeProjectionIndependentFromCurrentSiblings :
    RouteProjectionIndependentFromCurrentSiblings :=
  (canonicalRouteGateCountermodelAt 0
    ).routeProjectionDistinctFromEverySibling

theorem routeGateSourceDeleted_targetGeneratedOnlyAfterNext
    (depth : Nat) :
    IsEmpty (DeletedRouteAuthorityAt depth) ∧
      (routeNecessitySourceGeometryAt depth).actionableExitCapacity = 0 ∧
      IsEmpty
        ((routeNecessitySourceGeometryAt depth
          ).SourceGeneratedActionableExitRenewalAt) ∧
      temporalVisitAt depth ≠ temporalVisitAt (depth + 1) ∧
      Nonempty (SourceGeneratedUBIRouteReceiptAt ExitFutureCode.leave
        (routeRestorationTargetCrossingAt depth)) ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 :=
  let countermodel := canonicalRouteGateCountermodelAt depth
  ⟨countermodel.sourceRouteDeleted,
    routeNecessitySourceCapacity_eq_zero depth,
    routeNecessitySourceActionableExit_isEmpty depth,
    SourceGeneratedRouteGateIndependentNecessityAt.sourceAndTargetVisitsDistinct
      (depth := depth),
    ⟨countermodel.restoration.targetRouteReceipt⟩,
    countermodel.restoration.targetCapacityExact⟩

structure ProofCarryingRouteGateIndependentNecessityCertificate : Prop where
  existingActualRestoration :
    ProofCarryingPeriodicRouteOutageRestorationCertificate
  everyDepthCountermodel : ∀ depth : Nat,
    Nonempty (CanonicalRouteGateCountermodelAt depth)
  everyDepthRootAndPaymentExact : ∀ depth : Nat,
    let countermodel := canonicalRouteGateCountermodelAt depth
    countermodel.restoration.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      (periodicSourceBackedPaymentAt depth).rootOccurrence =
        countermodel.restoration.rootOccurrence
  everyDepthRemainingEconomicAuthority : ∀ depth : Nat,
    RouteGateRemainingEconomicAuthorityAt depth
  everyDepthRowLedgerConsumerNext : ∀ depth : Nat,
    let countermodel := canonicalRouteGateCountermodelAt depth
    countermodel.restoration.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq countermodel.restoration.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      HEq countermodel.restoration.installed.payload.successor
        (installedUBIAt depth).payload.successor ∧
      countermodel.restoration.applied.selectedWrite =
        countermodel.restoration.installed.temporalSelectedRow ∧
      (countermodel.restoration.applied.selectedWrite.sourceRow
        ).CommutesWithWorld ∧
      countermodel.restoration.applied.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      countermodel.restoration.installed.RootAnswerAndNextFactorizes ∧
      countermodel.restoration.applied.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  everyDepthSiblingActive : ∀ depth : Nat,
    RouteGateSiblingActiveOutcomesAt depth
  everyDepthSiblingFactorizes : ∀ depth : Nat,
    RouteGateSiblingFactorizationsAt depth
  routeProjectionIndependent :
    RouteProjectionIndependentFromCurrentSiblings
  everyDepthDeletedAndTargetGenerated : ∀ depth : Nat,
    IsEmpty (DeletedRouteAuthorityAt depth) ∧
      (routeNecessitySourceGeometryAt depth).actionableExitCapacity = 0 ∧
      IsEmpty
        ((routeNecessitySourceGeometryAt depth
          ).SourceGeneratedActionableExitRenewalAt) ∧
      temporalVisitAt depth ≠ temporalVisitAt (depth + 1) ∧
      Nonempty (SourceGeneratedUBIRouteReceiptAt ExitFutureCode.leave
        (routeRestorationTargetCrossingAt depth)) ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  everyDepthNoRemainingReconstruction : ∀ depth : Nat,
    IsEmpty
      (CanonicalRouteGateCountermodelAt depth →
        DeletedRouteAuthorityAt depth)

theorem proofCarryingRouteGateIndependentNecessityDirectConsumer :
    ProofCarryingRouteGateIndependentNecessityCertificate where
  existingActualRestoration :=
    proofCarryingPeriodicRouteOutageRestorationDirectConsumer
  everyDepthCountermodel := fun depth =>
    ⟨canonicalRouteGateCountermodelAt depth⟩
  everyDepthRootAndPaymentExact := fun depth =>
    ⟨(canonicalRouteGateCountermodelAt depth).exactRootOccurrence,
      (canonicalRouteGateCountermodelAt depth).actualPaymentSharesRoot⟩
  everyDepthRemainingEconomicAuthority :=
    routeGateRemainingEconomicAuthorityAt
  everyDepthRowLedgerConsumerNext := fun depth =>
    (canonicalRouteGateCountermodelAt depth
      ).rowLedgerConsumerAndNextRemain
  everyDepthSiblingActive := routeGateSiblingActiveOutcomesAt
  everyDepthSiblingFactorizes := routeGateSiblingFactorizationsAt
  routeProjectionIndependent :=
    routeProjectionIndependentFromCurrentSiblings
  everyDepthDeletedAndTargetGenerated :=
    routeGateSourceDeleted_targetGeneratedOnlyAfterNext
  everyDepthNoRemainingReconstruction :=
    remainingAuthorityCannotReconstructDeletedRoute

theorem routeGateNecessity_negativeControls (depth : Nat) : True := by
  let countermodel := canonicalRouteGateCountermodelAt depth
  fail_if_success exact
    (countermodel.ubi : CanonicalRouteGateCountermodelAt depth)
  fail_if_success exact
    (countermodel.restoration.sourcePaymentReceipt :
      CanonicalRouteGateCountermodelAt depth)
  fail_if_success exact
    (countermodel.restoration.targetRouteReceipt :
      DeletedRouteAuthorityAt depth)
  fail_if_success exact
    ((0 : Nat) : CanonicalRouteGateCountermodelAt depth)
  fail_if_success exact countermodel.gateKind
  fail_if_success exact countermodel.coverage
  fail_if_success exact countermodel.history
  fail_if_success exact countermodel.future
  trivial

end
end M14ProofCarryingRouteGateIndependentNecessityRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingRouteGateIndependentNecessityRegression.routeGateSourceDeleted_targetGeneratedOnlyAfterNext
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingRouteGateIndependentNecessityRegression.proofCarryingRouteGateIndependentNecessityDirectConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingRouteGateIndependentNecessityRegression.routeGateNecessity_negativeControls
