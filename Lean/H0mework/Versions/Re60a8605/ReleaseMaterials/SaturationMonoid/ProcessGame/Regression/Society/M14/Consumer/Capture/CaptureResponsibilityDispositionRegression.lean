import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capture.ResidualDisposition
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIPeriodicActualServiceCapacity

/-!
# M14 capture responsibility disposition

The fixed full-capture counterfactual is followed all the way to its existing
settlement responsibility.  The captured leave code returns the exact M3/M8
open settlement, retains its residual bearer, identifies its protected
interest with the source-generated accepting counterparty, carries an actual
residual consumer and source-owned incidence, and preserves the exact payment
next.

At every generated finite depth this disposition is indexed by the exact
periodic payment/root occurrence and accompanied by the same actual debited
service.  Nothing is stored as a future capture table.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14CaptureResponsibilityDispositionRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open Settlement.SourceOwnedSettlementCompiler
open UBI.Capture
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M8PurchasingPowerStandingRegression
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity

theorem leave_is_captured : fullCapture.Captures ExitFutureCode.leave :=
  rfl

theorem fixedCaptureDisposition :
    SourceAccountedCaptureDispositionAt capturedProgram ExitFutureCode.leave
      leave_is_captured :=
  SourceAccountedCaptureDispositionAt.generate capturedProgram
    ExitFutureCode.leave leave_is_captured

theorem captured_leave_returns_exact_payment_settlement :
    fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured =
      exactOpenSettlement exactResidualActivation :=
  fixedCaptureDisposition.exactSettlement

theorem captured_leave_retains_visible_residual_bearer :
    OpenSettlementAt.residualBearer
        (fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured) =
      OpenSettlementAt.residualBearer
        (exactOpenSettlement exactResidualActivation) :=
  fixedCaptureDisposition.bearerRetained

theorem captured_leave_beneficiary_is_generated_counterparty_interest :
    OpenSettlementAt.protectedInterest
        (fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured) =
      exchangeLaw.protectedInterestOfActor
        (exactCounterpartyActor exactResidualActivation) :=
  fixedCaptureDisposition.beneficiaryGenerated

theorem accepting_counterparty_bearer_is_generated :
    (exactCounterpartyObligation exactResidualActivation).bearer =
      exchangeLaw.bearerOfActor
        (exactCounterpartyActor exactResidualActivation) :=
  fixedCaptureDisposition.acceptingCounterpartyBearerGenerated

theorem captured_leave_has_activated_source_owned_residual :
    Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
        (exactOpenSettlement exactResidualActivation)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation) :=
  ⟨fixedCaptureDisposition.activatedResidualConsumer,
    fixedCaptureDisposition.sourceOwnedResidual⟩

theorem captured_leave_consumer_generates_payment_next :
    capturedProgram.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
      capturedProgram.payment.nextGenerated :=
  fixedCaptureDisposition.consumerNextIsPaymentNext

/-- One exact temporal capture disposition.  The payment occurrence is a
type index and all stored fields are propositions/`Nonempty`; the root does
not acquire a capture schedule or completed future. -/
structure PeriodicCaptureResponsibilityAt
    (depth : Nat)
    (payment : PeriodicSourceBackedPaymentAt depth) : Prop where
  exactTemporalOccurrence : payment.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  exactPaymentReceipt : Nonempty (SourceBackedUBIPaymentReceiptAt
    exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave)
  captureDisposition : SourceAccountedCaptureDispositionAt capturedProgram
    ExitFutureCode.leave leave_is_captured
  actualServiceRetained : Nonempty (ExactServedCrossingDebitedRunAt
    (anomiePhaseAt depth) M10OccurrenceCapacityDebitedRunFixture.debited
      (serviceCompilerAt depth))
  capacityCollapse :
    (geometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0
  rootFactorization : payment.installed.RootAnswerAndNextFactorizes

theorem periodicCaptureResponsibilityAt (depth : Nat) :
    PeriodicCaptureResponsibilityAt depth
      (periodicSourceBackedPaymentAt depth) where
  exactTemporalOccurrence :=
    (periodicSourceBackedPaymentAt depth).rootOccurrence_eq
  exactPaymentReceipt :=
    ⟨(periodicSourceBackedPaymentAt depth).paymentReceipt⟩
  captureDisposition := fixedCaptureDisposition
  actualServiceRetained := ⟨actualSettlementAt depth⟩
  capacityCollapse :=
    ⟨actionableExitCapacity_eq_one_at depth,
      captured_nominal_capacity_eq_zero_at depth⟩
  rootFactorization :=
    (periodicSourceBackedPaymentAt depth).rootFactorization

theorem every_periodic_payment_has_accounted_capture_disposition
    (depth : Nat) :
    PeriodicCaptureResponsibilityAt depth
      (periodicSourceBackedPaymentAt depth) :=
  periodicCaptureResponsibilityAt depth

theorem uncaptured_leave_has_no_capture_verdict :
    ¬ noCapture.Captures ExitFutureCode.leave := by
  simp [noCapture]

/-- Regression guard: a numeric capacity collapse is not a capture verdict
and cannot be passed to the generic disposition producer. -/
theorem bare_zero_capacity_cannot_generate_capture_disposition : True := by
  fail_if_success
    exact SourceAccountedCaptureDispositionAt.generate capturedProgram
      ExitFutureCode.leave (captured_nominal_capacity_eq_zero_at 0)
  trivial

structure CaptureResponsibilityDispositionCertificate : Prop where
  everyPeriod : ∀ depth : Nat,
    PeriodicCaptureResponsibilityAt depth
      (periodicSourceBackedPaymentAt depth)
  paymentOccurrencesRemainDistinct :
    Function.Injective periodicPaymentOccurrenceAt
  exactSettlement :
    fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured =
      exactOpenSettlement exactResidualActivation
  visibleResidualBearer :
    OpenSettlementAt.residualBearer
        (fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured) =
      OpenSettlementAt.residualBearer
        (exactOpenSettlement exactResidualActivation)
  generatedBeneficiary :
    OpenSettlementAt.protectedInterest
        (fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured) =
      exchangeLaw.protectedInterestOfActor
        (exactCounterpartyActor exactResidualActivation)
  generatedCounterpartyBearer :
    (exactCounterpartyObligation exactResidualActivation).bearer =
      exchangeLaw.bearerOfActor
        (exactCounterpartyActor exactResidualActivation)
  activatedSourceOwnedResidual :
    Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
        (exactOpenSettlement exactResidualActivation)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation)
  consumerGeneratesPaymentNext :
    capturedProgram.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
      capturedProgram.payment.nextGenerated
  uncapturedNegativeControl :
    ¬ noCapture.Captures ExitFutureCode.leave
  bareCapacityNoAuthority : True

theorem captureResponsibilityDispositionDirectConsumer :
    CaptureResponsibilityDispositionCertificate where
  everyPeriod := every_periodic_payment_has_accounted_capture_disposition
  paymentOccurrencesRemainDistinct := periodicPaymentOccurrenceAt_injective
  exactSettlement := captured_leave_returns_exact_payment_settlement
  visibleResidualBearer := captured_leave_retains_visible_residual_bearer
  generatedBeneficiary :=
    captured_leave_beneficiary_is_generated_counterparty_interest
  generatedCounterpartyBearer := accepting_counterparty_bearer_is_generated
  activatedSourceOwnedResidual :=
    captured_leave_has_activated_source_owned_residual
  consumerGeneratesPaymentNext :=
    captured_leave_consumer_generates_payment_next
  uncapturedNegativeControl := uncaptured_leave_has_no_capture_verdict
  bareCapacityNoAuthority :=
    bare_zero_capacity_cannot_generate_capture_disposition

end
end M14CaptureResponsibilityDispositionRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14CaptureResponsibilityDispositionRegression.every_periodic_payment_has_accounted_capture_disposition
#print axioms SaturationMonoid.ProcessGame.Society.M14CaptureResponsibilityDispositionRegression.captureResponsibilityDispositionDirectConsumer
