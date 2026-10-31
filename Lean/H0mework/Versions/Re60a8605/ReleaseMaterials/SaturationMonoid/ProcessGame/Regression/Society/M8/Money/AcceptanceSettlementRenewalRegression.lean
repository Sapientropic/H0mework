import H0mework.Society.Renewal.RenewalFaceSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Money.ExactSettlementRenewalFixture

/-!
# M8 money as acceptance and settlement renewal

Purchasing standing is projected from the exact open obligation selected by a
later source-owned residual-consumer activation.  The same seed generates its
source-ownership consumer and activated lifecycle disposition.  Price remains
a readout precisely on the open-settlement carrier; full fulfillment removes
that carrier instead of assigning a zero price.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8AcceptanceSettlementRenewalRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Renewal
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M8ExactSettlementRenewalFixture

def moneyStandingOf
    (seed : residualConsumerCompiler.ExactActivationSeed) :
    AdmittedObligation V :=
  (seed.openSettlement residualConsumerCompiler).obligation

def MoneyRenewalConsumerAt
    (seed : residualConsumerCompiler.ExactActivationSeed) : Type :=
  SourceOwnsResponsibilityIncidence V
    (P.boundarySource (seed.activation residualConsumerCompiler))
    (seed.openSettlement residualConsumerCompiler).obligation

def MoneyRenewalDispositionAt
    (seed : residualConsumerCompiler.ExactActivationSeed) : Type :=
  OpenSettlementAt.ActivatedResidualConsumerAt
    (seed.openSettlement residualConsumerCompiler)

abbrev MoneyRenewalFace :=
  SourceGeneratedRenewalFace
    Lifecycle.actualEventGame
    residualConsumerCompiler.ActivationSeed
    residualConsumerCompiler.activationSeedAt
    (fun _source => V.Lineage)
    (fun _source seed =>
      (residualConsumerCompiler.openSettlement seed.1).obligation.lineage)
    (AdmittedObligation V) moneyStandingOf
    MoneyRenewalConsumerAt MoneyRenewalDispositionAt

/-- Exact later acceptance/settlement activation generates the local money
renewal face. -/
def acceptanceSettlementRenewal : MoneyRenewalFace :=
  SourceGeneratedRenewalFace.generate exactResidualActivation
    (exactResidualActivation.sourceOwnership residualConsumerCompiler)
    (exactResidualActivation.activatedConsumer residualConsumerCompiler)

theorem money_renewal_event_in_actual_trace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      residualConsumerCompiler.activationSeedAt
        Lifecycle.actualEventGame.source state
        acceptanceSettlementRenewal.event :=
  acceptanceSettlementRenewal.event_mem_source_trace

theorem money_renewal_event_is_exact_activation :
    acceptanceSettlementRenewal.event = .maintainA :=
  rfl

theorem purchasing_standing_is_exact_open_obligation :
    acceptanceSettlementRenewal.standing = (openAt .a).obligation :=
  rfl

theorem purchasing_standing_lineage_is_exact_debt_lineage :
    acceptanceSettlementRenewal.actor.1 = (openAt .a).obligation.lineage :=
  rfl

theorem money_consumer_is_exact_source_ownership :
    acceptanceSettlementRenewal.responsibilityConsumer =
      exactResidualActivation.sourceOwnership residualConsumerCompiler :=
  rfl

theorem money_disposition_is_exact_activated_consumer :
    acceptanceSettlementRenewal.exactDisposition = activatedA :=
  rfl

theorem money_disposition_generates_exact_next :
    acceptanceSettlementRenewal.exactDisposition.edge.target.history =
      (openOccurrence.current settlementCompiler).history ++
        [acceptanceSettlementRenewal.exactDisposition.edge.lifecycleEvent] ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          acceptanceSettlementRenewal.exactDisposition.activation)
        (openAt .a).obligation) :=
  activated_consumer_generates_exact_next

structure AcceptanceSettlementRenewalCertificate : Prop where
  renewalFace : Nonempty MoneyRenewalFace
  exactEventTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      residualConsumerCompiler.activationSeedAt
        Lifecycle.actualEventGame.source state
        acceptanceSettlementRenewal.event
  exactAcceptanceEvent : acceptanceSettlementRenewal.event = .maintainA
  exactStandingObligation :
    acceptanceSettlementRenewal.standing = (openAt .a).obligation
  exactDebtLineage :
    acceptanceSettlementRenewal.actor.1 = (openAt .a).obligation.lineage
  exactSourceConsumer :
    acceptanceSettlementRenewal.responsibilityConsumer =
      exactResidualActivation.sourceOwnership residualConsumerCompiler
  exactActivatedDisposition :
    acceptanceSettlementRenewal.exactDisposition = activatedA
  sourceAdmissionAccepted :
    (admissionPayload (legToken .a)).assumption =
      BearerAssumption.accepted ()
  wholeLedgerNext :
    generatedResidualConsumer.nextGeneratedState.generated =
      .step (openOccurrence.generatedState settlementCompiler).generated
        generatedResidualConsumer.edge ∧
      generatedResidualConsumer.nextGeneratedState.current =
        generatedResidualConsumer.edge.target
  openPriceIffOpenSettlement :
    Nonempty (ExchangePriceObservationAt openZeroObserver) ↔
      Nonempty (OpenSettlementAt settlementCompiler openOccurrence)
  openZeroQuoteStillDefined :
    Nonempty (OpenSettlementAt settlementCompiler openOccurrence) ∧
      Nonempty (ExchangePriceObservationAt openZeroObserver) ∧
      openAZeroPrice.value = 0
  fullySettledPriceDomainEmpty :
    IsEmpty (OpenSettlementAt settlementCompiler fulfilledOccurrence) ∧
      ¬ Nonempty (ExchangePriceObservationAt fulfilledZeroObserver)

theorem acceptanceSettlementRenewalDirectConsumer :
    AcceptanceSettlementRenewalCertificate where
  renewalFace := ⟨acceptanceSettlementRenewal⟩
  exactEventTrace := money_renewal_event_in_actual_trace
  exactAcceptanceEvent := money_renewal_event_is_exact_activation
  exactStandingObligation := purchasing_standing_is_exact_open_obligation
  exactDebtLineage := purchasing_standing_lineage_is_exact_debt_lineage
  exactSourceConsumer := money_consumer_is_exact_source_ownership
  exactActivatedDisposition :=
    money_disposition_is_exact_activated_consumer
  sourceAdmissionAccepted := open_leg_source_has_exact_accepted_assumption
  wholeLedgerNext := later_acceptance_generates_whole_ledger_next
  openPriceIffOpenSettlement := open_price_domain_exact
  openZeroQuoteStillDefined := open_zero_quote_remains_price_defined
  fullySettledPriceDomainEmpty := fully_settled_price_domain_empty

end
end M8AcceptanceSettlementRenewalRegression
end Society
end ProcessGame
end SaturationMonoid
