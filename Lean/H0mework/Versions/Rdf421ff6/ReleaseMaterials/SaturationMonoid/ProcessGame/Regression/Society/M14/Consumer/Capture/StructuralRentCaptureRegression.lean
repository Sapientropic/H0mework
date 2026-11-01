import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capture.PurposeCapture
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccessPaymentPurposeFixture
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Sector.EssentialAccessSectorRegression

/-!
# M14 source-generated structural rent capture

The fixed captured UBI payment is structural rent precisely at the strongest
legitimate fixed-instance mouth: its source-owned payment-purpose compiler
selects the exact tenure relation seed; that lineage generates the tenure
phase and provider role; the captured code consumes an exact open price
domain; and the beneficiary, bearer, residual consumer, and payment next all
commute.

No property, landlord, asset-holder, sector, price, receipt, or ledger
registry is introduced.  Health and platform have real generated relations
and the same coarse beneficiary readout, but cannot replace the source-chosen
payment purpose.  Full fulfillment separately removes the price domain.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14StructuralRentCaptureRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open Settlement.SourceOwnedSettlementCompiler
open UBI.Capture
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M8MoneyRootInstallationRegression
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14CaptureResponsibilityDispositionRegression
open M14CounterpartyCaptureRenewalRegression
open M14EssentialAccessRelationFixture
open M14EssentialAccessPaymentPurposeLaw
open M14EssentialAccessPaymentPurposeFixture
open M14EssentialAccessSectorRegression

/-- The tenure source facts are read from the action-bearing disposition
installed before this temporal visit is emitted. -/
theorem installedTenureFailureAt (depth : Nat) : SourceTenureCaptureFailure :=
  (periodicUBISourceAt depth).installed.payload.disposition.sourceFailure

theorem rooted_payment_purpose_has_exact_trace_provenance (depth : Nat) :
    (installedTenureFailureAt depth).paymentPurpose =
        exactTenurePaymentPurpose ∧
      ∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = Lifecycle.Universal.FixedAdapter.core.targetFace.state
          Lifecycle.actualEventGame.source ∧
        essentialAccessRelationCompiler.relationSeedAt
          Lifecycle.actualEventGame.source state seed.1 ∧
        Lifecycle.Universal.FixedAdapter.core.targetFace.SeedAt
          Lifecycle.actualEventGame.source state
          (essentialAccessRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor essentialAccessRelationCompiler =
        exactCounterpartyActor exactResidualActivation ∧
      essentialAccessRelationCompiler.relationOf seed = tenureRelation := by
  rcases (installedTenureFailureAt depth).paymentPurpose
      |>.exact_relation_actor_provenance
    with ⟨seed, provenance, actorEq, relationEq⟩
  exact ⟨Subsingleton.elim _ _, seed, provenance, actorEq,
    relationEq.trans payment_purpose_relation_is_tenure⟩

abbrev RootInstalledTenurePurposeCaptureAt (depth : Nat) :=
  SourceGeneratedPurposeCaptureAt
    (purposeCompiler := essentialAccessPaymentPurposeCompiler)
    capturedProgram ExitFutureCode.leave
      (installedTenureFailureAt depth).captured

theorem rootInstalledTenurePurposeCaptureAt (depth : Nat) :
    RootInstalledTenurePurposeCaptureAt depth :=
  SourceGeneratedPurposeCaptureAt.generateFromPurpose
    essentialAccessPaymentPurposeCompiler
    (installedTenureFailureAt depth).paymentPurpose capturedProgram
    ExitFutureCode.leave (installedTenureFailureAt depth).captured

/-- Strong fixed-instance carrier.  `rent` is earned only after all generic
capture authority has been joined to the source-generated tenure purpose,
phase, and role.  None of these are caller premises of the producer. -/
structure SourceGeneratedStructuralRentCaptureAt (depth : Nat) : Prop where
  private mk ::
  purposeCapture : RootInstalledTenurePurposeCaptureAt depth
  installedPurpose :
    (installedTenureFailureAt depth).paymentPurpose =
      exactTenurePaymentPurpose
  purposeRelationExact :
    essentialAccessPaymentPurposeCompiler.purposeRelation
      exactResidualActivation = tenureRelation
  paymentCounterpartyIsTenureActor :
    exactCounterpartyActor exactResidualActivation = tenureActor
  tenurePhaseGenerated :
    essentialAccessPaymentPurposeCompiler.purposePhase
      exactResidualActivation = .tenure
  tenureRoleGenerated :
    essentialAccessRelationCompiler.RelationRoleAt tenureActor tenureRelation
      .target .tenureProvider

/-- Sole rent producer.  It accepts no relation, sector, purpose, phase,
role, price, beneficiary, bearer, residual, consumer, or next. -/
theorem structuralRentCaptureAt (depth : Nat) :
    SourceGeneratedStructuralRentCaptureAt depth where
  purposeCapture := rootInstalledTenurePurposeCaptureAt depth
  installedPurpose := Subsingleton.elim _ _
  purposeRelationExact := payment_purpose_relation_is_tenure
  paymentCounterpartyIsTenureActor :=
    (installedTenureFailureAt depth).tenureActorIsCounterparty.symm
  tenurePhaseGenerated := payment_purpose_phase_is_tenure
  tenureRoleGenerated := (installedTenureFailureAt depth).tenureRole

/-- Exact commuting theorem: payment purpose, open price, capture destination,
tenure role, residual bearer, source-owned consumer, and generated next are
one dependent chain. -/
theorem structural_rent_payment_price_residual_next_commute (depth : Nat) :
    SourceGeneratedStructuralRentCaptureAt depth ∧
      ExactTenurePaymentPurposeAt ∧
      essentialAccessPaymentPurposeCompiler.purposeRelation
          exactResidualActivation = tenureRelation ∧
      essentialAccessPaymentPurposeCompiler.purposePhase
          exactResidualActivation = .tenure ∧
      essentialAccessRelationCompiler.RelationRoleAt tenureActor tenureRelation
        .target .tenureProvider ∧
      Nonempty (ExchangePriceObservationAt
        (rootPriceObserver exactResidualActivation)) ∧
      Nonempty (OpenSettlementAt settlementCompiler openOccurrence) ∧
      fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured =
        exactOpenSettlement exactResidualActivation ∧
      OpenSettlementAt.protectedInterest
          (fullCapture.captureSettlement ExitFutureCode.leave
            leave_is_captured) =
        exchangeLaw.protectedInterestOfActor tenureActor ∧
      OpenSettlementAt.residualBearer
          (fullCapture.captureSettlement ExitFutureCode.leave
            leave_is_captured) =
        OpenSettlementAt.residualBearer
          (exactOpenSettlement exactResidualActivation) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation) ∧
      capturedProgram.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
        capturedProgram.payment.nextGenerated := by
  refine ⟨structuralRentCaptureAt depth,
    (installedTenureFailureAt depth).paymentPurpose,
    payment_purpose_relation_is_tenure,
    payment_purpose_phase_is_tenure,
    (structuralRentCaptureAt depth).tenureRoleGenerated,
    (rootInstalledTenurePurposeCaptureAt depth).openPriceDomain,
    (rootInstalledTenurePurposeCaptureAt depth).unsettledObligation,
    (rootInstalledTenurePurposeCaptureAt depth).captureSettlementExact, ?_,
    (rootInstalledTenurePurposeCaptureAt depth).residualBearerRetained,
    (rootInstalledTenurePurposeCaptureAt depth).sourceOwnedResidual,
    (rootInstalledTenurePurposeCaptureAt depth).consumerNextIsPaymentNext⟩
  rw [(installedTenureFailureAt depth).tenureActorIsCounterparty]
  exact (rootInstalledTenurePurposeCaptureAt depth).captureBeneficiaryGenerated

/-! ## Strict missing-premise controls -/

/-- A tenure purpose without an open settlement is not rent capture.  Exact
full fulfillment makes the required price observation impossible. -/
structure FulfilledStructuralRentForgery (depth : Nat) : Prop where
  tenurePurpose : ExactTenurePaymentPurposeAt
  openPriceDomain : Nonempty
    (ExchangePriceObservationAt fulfilledZeroObserver)

theorem fulfilledStructuralRentForgery_isEmpty (depth : Nat) :
    IsEmpty (FulfilledStructuralRentForgery depth) :=
  ⟨fun forged => fully_fulfilled_has_no_price_domain.2
    forged.openPriceDomain⟩

/-- Direct consumer of the production no-open theorem: if this same exact
payment occurrence were fully fulfilled, its root-installed purpose capture
would be empty. -/
theorem fullyFulfilledSamePaymentOccurrence_noStructuralRent
    (depth : Nat)
    (fully : FullyFulfilledExchangeAt settlementCompiler openOccurrence) :
    IsEmpty (RootInstalledTenurePurposeCaptureAt depth) :=
  SourceGeneratedPurposeCaptureAt.fullyFulfilled_noPurposeCapture fully

/-- An open tenure payment without a capture verdict is not rent capture. -/
theorem uncaptured_leave_has_no_structural_rent_verdict :
    ¬ noCapture.Captures ExitFutureCode.leave :=
  uncaptured_leave_has_no_capture_verdict

/-- Temporal join: the local purpose law may recur, while payment, root, and
actual service authority stay indexed by the exact generated visit. -/
structure PeriodicStructuralRentCaptureAt
    (depth : Nat)
    (payment : PeriodicSourceBackedPaymentAt depth) : Prop where
  structuralRent : SourceGeneratedStructuralRentCaptureAt depth
  periodicTenure : PeriodicTenureCaptureRenewalAt depth payment
  exactTemporalOccurrence : payment.rootOccurrence =
    ((M9ProofCarryingRenewalInquiryRoot.jointRoot).toAuthoritativeRoot.toLedgerRoot).exactTemporalCausalEventAt
      (temporalVisitAt depth)
  actualServiceRetained : Nonempty (ExactServedCrossingDebitedRunAt
    (anomiePhaseAt depth) M10OccurrenceCapacityDebitedRunFixture.debited
      (serviceCompilerAt depth))
  rootFactorization : payment.installed.RootAnswerAndNextFactorizes

theorem periodicStructuralRentCaptureAt (depth : Nat) :
    PeriodicStructuralRentCaptureAt depth
      (periodicSourceBackedPaymentAt depth) := by
  let periodicTenure := periodicTenureCaptureRenewalAt depth
  let periodicCapture := periodicTenure.periodicCounterparty.periodicCapture
  exact
    { structuralRent := structuralRentCaptureAt depth
      periodicTenure := periodicTenure
      exactTemporalOccurrence := periodicCapture.exactTemporalOccurrence
      actualServiceRetained := periodicCapture.actualServiceRetained
      rootFactorization := periodicCapture.rootFactorization }

/-- Capacity transfer is a downstream readout of the same periodic capture,
not a premise or stored field of structural rent. -/
theorem structural_rent_transfers_exit_capacity_at (depth : Nat) :
    PeriodicStructuralRentCaptureAt depth
        (periodicSourceBackedPaymentAt depth) ∧
      (geometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 :=
  ⟨periodicStructuralRentCaptureAt depth,
    (periodicTenureCaptureRenewalAt depth).periodicCounterparty
      |>.periodicCapture.capacityCollapse⟩

structure StructuralRentCaptureCertificate : Prop where
  everyDepth : ∀ depth : Nat,
    PeriodicStructuralRentCaptureAt depth
      (periodicSourceBackedPaymentAt depth)
  exactTraceProvenance : ∀ depth : Nat,
    (installedTenureFailureAt depth).paymentPurpose =
        exactTenurePaymentPurpose ∧
      ∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = Lifecycle.Universal.FixedAdapter.core.targetFace.state
          Lifecycle.actualEventGame.source ∧
        essentialAccessRelationCompiler.relationSeedAt
          Lifecycle.actualEventGame.source state seed.1 ∧
        Lifecycle.Universal.FixedAdapter.core.targetFace.SeedAt
          Lifecycle.actualEventGame.source state
          (essentialAccessRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor essentialAccessRelationCompiler =
        exactCounterpartyActor exactResidualActivation ∧
      essentialAccessRelationCompiler.relationOf seed = tenureRelation
  paymentPriceResidualNextCommute : ∀ depth : Nat,
    SourceGeneratedStructuralRentCaptureAt depth ∧
      ExactTenurePaymentPurposeAt ∧
      essentialAccessPaymentPurposeCompiler.purposeRelation
          exactResidualActivation = tenureRelation ∧
      essentialAccessPaymentPurposeCompiler.purposePhase
          exactResidualActivation = .tenure ∧
      essentialAccessRelationCompiler.RelationRoleAt tenureActor tenureRelation
        .target .tenureProvider ∧
      Nonempty (ExchangePriceObservationAt
        (rootPriceObserver exactResidualActivation)) ∧
      Nonempty (OpenSettlementAt settlementCompiler openOccurrence) ∧
      fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured =
        exactOpenSettlement exactResidualActivation ∧
      OpenSettlementAt.protectedInterest
          (fullCapture.captureSettlement ExitFutureCode.leave
            leave_is_captured) =
        exchangeLaw.protectedInterestOfActor tenureActor ∧
      OpenSettlementAt.residualBearer
          (fullCapture.captureSettlement ExitFutureCode.leave
            leave_is_captured) =
        OpenSettlementAt.residualBearer
          (exactOpenSettlement exactResidualActivation) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation) ∧
      capturedProgram.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
        capturedProgram.payment.nextGenerated
  noHealthPurposeCompiler :
    ¬ ∃ compiler : AnyEssentialAccessPaymentPurposeCompiler,
      compiler.purposeRelation exactResidualActivation = healthRelation
  noPlatformPurposeCompiler :
    ¬ ∃ compiler : AnyEssentialAccessPaymentPurposeCompiler,
      compiler.purposeRelation exactResidualActivation = platformRelation
  fulfilledHasNoRentPriceDomain : ∀ depth : Nat,
    IsEmpty (FulfilledStructuralRentForgery depth)
  fullFulfillmentEliminatesSameOccurrenceRent : ∀ depth : Nat,
    FullyFulfilledExchangeAt settlementCompiler openOccurrence →
      IsEmpty (RootInstalledTenurePurposeCaptureAt depth)
  uncapturedHasNoRentVerdict :
    ¬ noCapture.Captures ExitFutureCode.leave
  sameCoarseReadoutDifferentSources :
    exchangeLaw.protectedInterestOfActor tenureActor =
        exchangeLaw.protectedInterestOfActor healthActor ∧
      exchangeLaw.protectedInterestOfActor tenureActor =
        exchangeLaw.protectedInterestOfActor platformActor

theorem structuralRentCaptureDirectConsumer :
    StructuralRentCaptureCertificate where
  everyDepth := periodicStructuralRentCaptureAt
  exactTraceProvenance := rooted_payment_purpose_has_exact_trace_provenance
  paymentPriceResidualNextCommute :=
    structural_rent_payment_price_residual_next_commute
  noHealthPurposeCompiler :=
    no_payment_purpose_compiler_maps_exact_payment_to_health
  noPlatformPurposeCompiler :=
    no_payment_purpose_compiler_maps_exact_payment_to_platform
  fulfilledHasNoRentPriceDomain := fulfilledStructuralRentForgery_isEmpty
  fullFulfillmentEliminatesSameOccurrenceRent :=
    fullyFulfilledSamePaymentOccurrence_noStructuralRent
  uncapturedHasNoRentVerdict :=
    uncaptured_leave_has_no_structural_rent_verdict
  sameCoarseReadoutDifferentSources :=
    ⟨tenure_health_protectedInterest_readouts_eq,
      tenure_platform_protectedInterest_readouts_eq⟩

end
end M14StructuralRentCaptureRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14StructuralRentCaptureRegression.structuralRentCaptureAt
#print axioms SaturationMonoid.ProcessGame.Society.M14StructuralRentCaptureRegression.periodicStructuralRentCaptureAt
#print axioms SaturationMonoid.ProcessGame.Society.M14StructuralRentCaptureRegression.structuralRentCaptureDirectConsumer
