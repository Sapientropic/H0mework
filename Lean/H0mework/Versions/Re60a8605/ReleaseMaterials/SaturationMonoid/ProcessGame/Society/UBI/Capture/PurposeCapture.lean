import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capture.CounterpartyRenewal
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capture.PaymentPurpose

/-!
# Purpose-generated capture

This module joins three already generated authorities:

* the payment's source-owned purpose relation;
* the exact open price domain and responsibility residual;
* the captured-code counterparty renewal.

It deliberately remains domain-neutral.  A downstream source restriction may
call an instance structural rent only when the purpose relation's own lineage
generates a tenure phase and role.  No property, asset-holder, creditor,
sector, price, receipt, or future registry is introduced here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UBI
namespace Capture

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money Power
open Settlement.SourceOwnedSettlementCompiler

universe u v wa wc x y z q s r e c p

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {core : SourceOwnedLifecycleCore.{u, v, wa} occurrenceOf game}
variable {V : Vocabulary.{x}}
variable {P : NativeResponsibilityProcess V}
variable {incidence : ActorResponsibilityIncidence core V}
variable
  {exchangeRelationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, y}
    occurrenceOf game core.targetFace}
variable
  {exchangeLaw : SourceOwnedExchangeLaw.{u, v, wa, x, y, z}
    core V P incidence exchangeRelationCompiler}
variable
  {settlementCompiler : SourceOwnedSettlementCompiler.{u, v, wa, x, y, z, q}
    exchangeLaw}
variable
  {activationCompiler :
    SourceOwnedResidualConsumerCompiler.{u, v, wa, x, y, z, q, s}
      settlementCompiler}

variable {controllerFace : M0BoundaryFace.{u, v, wc} occurrenceOf}
variable
  {exitRelationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, e}
    occurrenceOf game core.targetFace}
variable
  {employmentController : SourceOwnedActionControllerCompiler.{u, v, wc, c}
    game controllerFace}
variable [Zero (exitRelationCompiler.Phase game.source)]

variable
  {purposeRelationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, p}
    occurrenceOf game core.targetFace}
variable
  {purposeCompiler : SourceOwnedPaymentPurposeCompiler
    (activationCompiler := activationCompiler)
    (purposeRelationCompiler := purposeRelationCompiler)}

variable {paymentSeed : activationCompiler.ExactActivationSeed}
variable {PriceValue : Type r}
variable {observer : ExchangePriceObserverAt
  (settlementCompiler := settlementCompiler)
  (paymentSeed.occurrence activationCompiler) PriceValue}
variable {employer : employmentController.Actor}
variable {worker : exitRelationCompiler.Actor}
variable {employment exitRelation : exitRelationCompiler.GeneratedRelation}
variable {capture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
  (OpenSettlementAt settlementCompiler
    (paymentSeed.occurrence activationCompiler))
  (exactOpenSettlement paymentSeed)}

/-- A captured payment whose purpose, price domain, beneficiary, residual,
and consumer next all remain source-accounted.  The public producer accepts
neither a purpose relation nor any of these conclusions. -/
structure SourceGeneratedPurposeCaptureAt
    (program : ExitCapacityProgramAt paymentSeed observer employer worker
      employment exitRelation capture)
    (code : exitRelationCompiler.FutureCode)
    (captured : capture.Captures code) : Prop where
  private mk ::
  paymentPurpose :
    purposeCompiler.SourceGeneratedPaymentPurposeAt paymentSeed
  counterpartyRenewal :
    SourceGeneratedCounterpartyCaptureRenewalAt program code captured
  openPriceDomain : Nonempty (ExchangePriceObservationAt observer)
  unsettledObligation : Nonempty
    (OpenSettlementAt settlementCompiler
      (paymentSeed.occurrence activationCompiler))
  captureSettlementExact :
    capture.captureSettlement code captured = exactOpenSettlement paymentSeed
  captureBeneficiaryGenerated :
    OpenSettlementAt.protectedInterest
        (capture.captureSettlement code captured) =
      exchangeLaw.protectedInterestOfActor (exactCounterpartyActor paymentSeed)
  residualBearerRetained :
    OpenSettlementAt.residualBearer
        (capture.captureSettlement code captured) =
      OpenSettlementAt.residualBearer (exactOpenSettlement paymentSeed)
  residualRetained :
    OpenSettlementAt.residual (capture.captureSettlement code captured) =
      OpenSettlementAt.residual (exactOpenSettlement paymentSeed)
  activatedResidualConsumer : Nonempty
    (OpenSettlementAt.ActivatedResidualConsumerAt
      (exactOpenSettlement paymentSeed))
  sourceOwnedResidual : Nonempty (SourceOwnsResponsibilityIncidence V
    (P.boundarySource
      program.purchasingPowerStanding.activatedConsumer.activation)
    (exactOpenSettlement paymentSeed).obligation)
  consumerNextIsPaymentNext :
    program.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
      program.payment.nextGenerated

namespace SourceGeneratedPurposeCaptureAt

/-- Assemble capture from an already source-generated payment-purpose
authority.  This is the root-consumer mouth: the caller cannot submit a raw
relation, phase, or sector label, only the sealed purpose image. -/
theorem generateFromPurpose
    (purposeCompiler : SourceOwnedPaymentPurposeCompiler
      (activationCompiler := activationCompiler)
      (purposeRelationCompiler := purposeRelationCompiler))
    (paymentPurpose :
      purposeCompiler.SourceGeneratedPaymentPurposeAt paymentSeed)
    (program : ExitCapacityProgramAt paymentSeed observer employer worker
      employment exitRelation capture)
    (code : exitRelationCompiler.FutureCode)
    (captured : capture.Captures code) :
    SourceGeneratedPurposeCaptureAt
      (purposeCompiler := purposeCompiler) program code captured := by
  let renewal := SourceGeneratedCounterpartyCaptureRenewalAt.generate
    program code captured
  let disposition := renewal.captureDisposition
  exact
    { paymentPurpose := paymentPurpose
      counterpartyRenewal := renewal
      openPriceDomain := ⟨program.purchasingPowerStanding.priceObservation⟩
      unsettledObligation := ⟨exactOpenSettlement paymentSeed⟩
      captureSettlementExact := disposition.exactSettlement
      captureBeneficiaryGenerated := disposition.beneficiaryGenerated
      residualBearerRetained := disposition.bearerRetained
      residualRetained := disposition.residualRetained
      activatedResidualConsumer := disposition.activatedResidualConsumer
      sourceOwnedResidual := disposition.sourceOwnedResidual
      consumerNextIsPaymentNext := disposition.consumerNextIsPaymentNext }

/-- Sole producer.  Purpose is selected by the source compiler; price and
residual facts are read from the indexed program and captured code. -/
theorem generate
    (purposeCompiler : SourceOwnedPaymentPurposeCompiler
      (activationCompiler := activationCompiler)
      (purposeRelationCompiler := purposeRelationCompiler))
    (program : ExitCapacityProgramAt paymentSeed observer employer worker
      employment exitRelation capture)
    (code : exitRelationCompiler.FutureCode)
    (captured : capture.Captures code) :
    SourceGeneratedPurposeCaptureAt
      (purposeCompiler := purposeCompiler) program code captured :=
  generateFromPurpose purposeCompiler
    (SourceOwnedPaymentPurposeCompiler.SourceGeneratedPaymentPurposeAt.generate
      purposeCompiler paymentSeed)
    program code captured

/-- The selected purpose relation and exact payment counterparty retain their
common generated actor, independently of any observer readout. -/
theorem purpose_relation_actor_provenance
    {program : ExitCapacityProgramAt paymentSeed observer employer worker
      employment exitRelation capture}
    {code : exitRelationCompiler.FutureCode}
    {captured : capture.Captures code}
    (purposeCapture : SourceGeneratedPurposeCaptureAt
      (purposeCompiler := purposeCompiler) program code captured) :
    ∃ seed : purposeRelationCompiler.ExactRelationSeed,
      (∃ state ∈ game.occurrence.trace,
        state = core.targetFace.state game.source ∧
          purposeRelationCompiler.relationSeedAt game.source state seed.1 ∧
          core.targetFace.SeedAt game.source state
            (purposeRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor purposeRelationCompiler = exactCounterpartyActor paymentSeed ∧
      purposeRelationCompiler.relationOf seed =
        purposeCompiler.purposeRelation paymentSeed :=
  purposeCapture.paymentPurpose.exact_relation_actor_provenance

/-- If the indexed settlement occurrence has no open obligation, no
purpose-capture carrier can be generated. -/
theorem noOpenSettlement_noPurposeCapture
    {program : ExitCapacityProgramAt paymentSeed observer employer worker
      employment exitRelation capture}
    {code : exitRelationCompiler.FutureCode}
    {captured : capture.Captures code}
    (noOpen : IsEmpty (OpenSettlementAt settlementCompiler
      (paymentSeed.occurrence activationCompiler))) :
    IsEmpty (SourceGeneratedPurposeCaptureAt
      (purposeCompiler := purposeCompiler) program code captured) := by
  refine ⟨fun purposeCapture => ?_⟩
  rcases purposeCapture.unsettledObligation with ⟨openSettlement⟩
  exact noOpen.false openSettlement

/-- Exact full fulfillment is therefore incompatible with every
purpose-capture carrier on that same settlement occurrence. -/
theorem fullyFulfilled_noPurposeCapture
    {program : ExitCapacityProgramAt paymentSeed observer employer worker
      employment exitRelation capture}
    {code : exitRelationCompiler.FutureCode}
    {captured : capture.Captures code}
    (fully : FullyFulfilledExchangeAt settlementCompiler
      (paymentSeed.occurrence activationCompiler)) :
    IsEmpty (SourceGeneratedPurposeCaptureAt
      (purposeCompiler := purposeCompiler) program code captured) :=
  noOpenSettlement_noPurposeCapture fully.openSettlement_isEmpty

end SourceGeneratedPurposeCaptureAt

end Capture
end UBI
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.UBI.Capture.SourceGeneratedPurposeCaptureAt.generate
#print axioms SaturationMonoid.ProcessGame.Society.UBI.Capture.SourceGeneratedPurposeCaptureAt.generateFromPurpose
#print axioms SaturationMonoid.ProcessGame.Society.UBI.Capture.SourceGeneratedPurposeCaptureAt.fullyFulfilled_noPurposeCapture
