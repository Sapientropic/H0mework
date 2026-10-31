import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Route.Producer.SourceGeneratedRouteGateIndependentNecessity
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.ProofCarryingExitRepairRenewalRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Capture.CaptureResponsibilityDispositionRegression

/-!
# Independent necessity of the noncapture gate

The existing UBI tenure-capture transition is already an actual ordinary
root reform.  At its exact source visit, Payment, route, debited service,
standing, tenure, residual bearer/consumer, row, whole ledger, root consumer,
generated next, and every other installed renewal projection remain live.
The one missing authority is a source noncapture verdict: full capture makes
that fibre empty and collapses actionable-exit capacity to zero.

The source-installed remove-capture disposition carries the differently typed
target noncapture proof, while only the compiler-generated next realizes the
target program and capacity one.  No root, occurrence, ledger, gate enum,
registry, history, or completed future is added.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedNoncaptureGateIndependentNecessity

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

/-! ## Exact source and target authority fibres -/

/-- A noncapture verdict for the actual captured source policy, indexed by
the exact temporal Payment occurrence.  The fibre is empty because the source
is genuinely captured; the subtype prevents a bare policy proposition from
being mistaken for occurrence authority. -/
abbrev DeletedSourceNoncaptureAuthorityAt (depth : Nat) :=
  { _sourceUncaptured : ¬ fullCapture.Captures ExitFutureCode.leave //
    (periodicSourceBackedPaymentAt depth).rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt depth) }

theorem deletedSourceNoncaptureAuthority_isEmpty (depth : Nat) :
    IsEmpty (DeletedSourceNoncaptureAuthorityAt depth) :=
  ⟨fun sourceUncaptured =>
    sourceUncaptured.1 (priceCaptureSignatureAt depth).captured⟩

theorem capturedSourceActionableExit_isEmpty (depth : Nat) :
    IsEmpty
      ((capturedGeometryCompilerAt depth
        ).SourceGeneratedActionableExitRenewalAt) := by
  constructor
  intro renewal
  have positive :
      0 < (capturedGeometryCompilerAt depth).actionableExitCapacity :=
    (capturedGeometryCompilerAt depth)
      |>.capacity_positive_iff_actionableExitRenewal.mpr ⟨renewal⟩
  rw [captured_nominal_capacity_eq_zero_at] at positive
  exact Nat.not_lt_zero _ positive

/-! ## Same-visit remaining renewal projections -/

def noncaptureNecessityProofCarryingAt (depth : Nat) :
    SourceInstalledRenewalAt jointRecognition (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def noncaptureNecessityRecognitionWitnessAt (depth : Nat) :
    SourceInstalledRenewalAt recognitionWitnessRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def noncaptureNecessityMandateAt (depth : Nat) :
    SourceInstalledRenewalAt mandateRecognition (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def noncaptureNecessityEssentialServiceAt (depth : Nat) :
    SourceInstalledRenewalAt essentialServiceRestorationRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def noncaptureNecessityRouteAt (depth : Nat) :
    SourceInstalledRenewalAt routeOutageRestorationRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def noncaptureNecessityCommonClearingAt (depth : Nat) :
    SourceInstalledRenewalAt commonClearingRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def noncaptureNecessityClearingBackstopAt (depth : Nat) :
    SourceInstalledRenewalAt clearingBackstopRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

/-! ## Full Type-valued countermodel -/

structure SourceGeneratedNoncaptureGateIndependentNecessityAt
    (depth : Nat) : Type 22 where
  private mk ::
  renewal : SourceInstalledProofCarryingExitRepairRenewalAt
    depth .removeCapture
  sourceSignature : PriceCaptureSignatureAt depth
  captureResponsibility : PeriodicCaptureResponsibilityAt depth
    (periodicSourceBackedPaymentAt depth)
  proofCarrying : SourceInstalledRenewalAt jointRecognition
    (temporalVisitAt depth)
  recognitionWitness : SourceInstalledRenewalAt recognitionWitnessRecognition
    (temporalVisitAt depth)
  mandate : SourceInstalledRenewalAt mandateRecognition
    (temporalVisitAt depth)
  essentialService : SourceInstalledRenewalAt
    essentialServiceRestorationRecognition (temporalVisitAt depth)
  route : SourceInstalledRenewalAt routeOutageRestorationRecognition
    (temporalVisitAt depth)
  commonClearing : SourceInstalledRenewalAt commonClearingRecognition
    (temporalVisitAt depth)
  clearingBackstop : SourceInstalledRenewalAt clearingBackstopRecognition
    (temporalVisitAt depth)
  sourceNoncaptureDeleted :
    IsEmpty (DeletedSourceNoncaptureAuthorityAt depth)

/-- Sole producer.  `depth` selects the existing exact visit and the
source-installed remove-capture transition; no verdict, repair, row, next,
projection family, or future is supplied by the caller. -/
def sourceGeneratedNoncaptureGateIndependentNecessityAt
    (depth : Nat) :
    SourceGeneratedNoncaptureGateIndependentNecessityAt depth :=
  { renewal := SourceInstalledProofCarryingExitRepairRenewalAt.generate depth
    sourceSignature := priceCaptureSignatureAt depth
    captureResponsibility := periodicCaptureResponsibilityAt depth
    proofCarrying := noncaptureNecessityProofCarryingAt depth
    recognitionWitness := noncaptureNecessityRecognitionWitnessAt depth
    mandate := noncaptureNecessityMandateAt depth
    essentialService := noncaptureNecessityEssentialServiceAt depth
    route := noncaptureNecessityRouteAt depth
    commonClearing := noncaptureNecessityCommonClearingAt depth
    clearingBackstop := noncaptureNecessityClearingBackstopAt depth
    sourceNoncaptureDeleted :=
      deletedSourceNoncaptureAuthority_isEmpty depth }

namespace SourceGeneratedNoncaptureGateIndependentNecessityAt

variable {depth : Nat}
  (countermodel : SourceGeneratedNoncaptureGateIndependentNecessityAt depth)

include countermodel

theorem exactRootAndPaymentRemain :
    countermodel.renewal.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      (periodicSourceBackedPaymentAt depth).rootOccurrence =
        countermodel.renewal.rootOccurrence :=
  ⟨countermodel.renewal.rootOccurrence_eq,
    (periodicSourceBackedPaymentAt depth).rootOccurrence_eq.trans
      countermodel.renewal.rootOccurrence_eq.symm⟩

theorem paymentStandingRouteServiceAndTenureRemain :
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
      Nonempty (ActualServiceAt depth) := by
  let failure :=
    countermodel.renewal.source.installed.payload.disposition.sourceFailure
  exact
    ⟨failure.tenureInterest,
      failure.tenureActorIsCounterparty,
      failure.tenurePhase,
      failure.tenureRole,
      countermodel.renewal.source.installed.payload.disposition
        |>.standing_preserved,
      countermodel.sourceSignature.paymentPresent,
      countermodel.sourceSignature.routePresent,
      countermodel.sourceSignature.servicePresent⟩

theorem residualBearerAndConsumerRemain :
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
        capturedProgram.payment.nextGenerated :=
  ⟨captured_leave_returns_exact_payment_settlement,
    countermodel.captureResponsibility.captureDisposition.bearerRetained,
    countermodel.captureResponsibility.captureDisposition
      |>.activatedResidualConsumer,
    countermodel.captureResponsibility.captureDisposition.sourceOwnedResidual,
    countermodel.captureResponsibility.captureDisposition
      |>.consumerNextIsPaymentNext⟩

theorem rowLedgerConsumerAndNextRemain :
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
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) :=
  ⟨countermodel.renewal.source.sourceEntryExact,
    countermodel.renewal.ordinarySelectedWrite_eq_installedSelectedRow,
    countermodel.renewal.ordinarySelectedWrite_commutes,
    rfl,
    ⟨countermodel.renewal.appliedReform.rootConsumer⟩,
    countermodel.renewal.appliedReform.rootFactorization,
    countermodel.renewal.generatedNext_eq_rootCompiler⟩

theorem everyRemainingProjectionActiveAtExactOccurrence :
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
          countermodel.clearingBackstop.payload⟩ :=
  ⟨countermodel.renewal.componentOutcome_eq_activePayload,
    countermodel.proofCarrying.componentOutcome_eq_activePayload,
    countermodel.recognitionWitness.componentOutcome_eq_activePayload,
    countermodel.mandate.componentOutcome_eq_activePayload,
    countermodel.essentialService.componentOutcome_eq_activePayload,
    countermodel.route.componentOutcome_eq_activePayload,
    countermodel.commonClearing.componentOutcome_eq_activePayload,
    countermodel.clearingBackstop.componentOutcome_eq_activePayload⟩

theorem everyRemainingProjectionFactorizes :
    countermodel.renewal.source.installed.RootAnswerAndNextFactorizes ∧
      countermodel.proofCarrying.RootAnswerAndNextFactorizes ∧
      countermodel.recognitionWitness.RootAnswerAndNextFactorizes ∧
      countermodel.mandate.RootAnswerAndNextFactorizes ∧
      countermodel.essentialService.RootAnswerAndNextFactorizes ∧
      countermodel.route.RootAnswerAndNextFactorizes ∧
      countermodel.commonClearing.RootAnswerAndNextFactorizes ∧
      countermodel.clearingBackstop.RootAnswerAndNextFactorizes :=
  ⟨countermodel.renewal.appliedReform.rootFactorization,
    countermodel.proofCarrying.rootAnswerAndNext_factorizes,
    countermodel.recognitionWitness.rootAnswerAndNext_factorizes,
    countermodel.mandate.rootAnswerAndNext_factorizes,
    countermodel.essentialService.rootAnswerAndNext_factorizes,
    countermodel.route.rootAnswerAndNext_factorizes,
    countermodel.commonClearing.rootAnswerAndNext_factorizes,
    countermodel.clearingBackstop.rootAnswerAndNext_factorizes⟩

theorem targetDispositionAndGeneratedNext :
    (¬ noCapture.Captures ExitFutureCode.leave) ∧
      countermodel.renewal.generatedNext.visit =
        temporalVisitAt (depth + 1) ∧
      (installedUBIAt (depth + 1)).payload.consumer.programAt =
        countermodel.renewal.source.installed.payload.disposition.targetProgramAt ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 :=
  ⟨countermodel.renewal.source.installed.payload.disposition.target_uncaptured,
    countermodel.renewal.generatedNext_repairedFace_capacity_eq_one.1,
    countermodel.renewal.generatedNext_repairedFace_capacity_eq_one.2.1,
    countermodel.renewal.generatedNext_repairedFace_capacity_eq_one.2.2⟩

omit countermodel in
theorem sourceAndTargetVisitsDistinct :
    temporalVisitAt depth ≠ temporalVisitAt (depth + 1) :=
  adjacent_periods_are_distinct depth

end SourceGeneratedNoncaptureGateIndependentNecessityAt

theorem remainingAuthorityCannotReconstructSourceNoncapture (depth : Nat) :
    IsEmpty
      (SourceGeneratedNoncaptureGateIndependentNecessityAt depth →
        DeletedSourceNoncaptureAuthorityAt depth) :=
  ⟨fun reconstruct =>
    (deletedSourceNoncaptureAuthority_isEmpty depth).false
      (reconstruct
        (sourceGeneratedNoncaptureGateIndependentNecessityAt depth))⟩

theorem targetNoncaptureCannotRetypeAsSourceNoncapture
    (depth : Nat) : True := by
  let countermodel :=
    sourceGeneratedNoncaptureGateIndependentNecessityAt depth
  fail_if_success exact
    (countermodel.renewal.source.installed.payload.disposition
      |>.target_uncaptured : DeletedSourceNoncaptureAuthorityAt depth)
  fail_if_success exact countermodel.gateKind
  fail_if_success exact countermodel.coverage
  fail_if_success exact countermodel.history
  fail_if_success exact countermodel.future
  fail_if_success exact countermodel.completedFuture
  trivial

end
end M14SourceGeneratedNoncaptureGateIndependentNecessity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedNoncaptureGateIndependentNecessity.sourceGeneratedNoncaptureGateIndependentNecessityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedNoncaptureGateIndependentNecessity.SourceGeneratedNoncaptureGateIndependentNecessityAt.everyRemainingProjectionActiveAtExactOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedNoncaptureGateIndependentNecessity.capturedSourceActionableExit_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedNoncaptureGateIndependentNecessity.remainingAuthorityCannotReconstructSourceNoncapture
