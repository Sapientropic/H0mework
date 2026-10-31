import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Money.PurchasingPowerStanding
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Money.AcceptanceSettlementRenewalRegression

/-!
# M8 source-backed purchasing-power consumer

The existing four-leg exchange supplies one exact reciprocal tender:
the open `a` obligation tenders its source content, the source-generated `b`
counterparty carries an accepted reciprocal admission, the open price domain
is witnessed, and the exact residual activation generates the next state.

This fixed fixture is only a consumer of the unrestricted production theorem.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8PurchasingPowerStandingRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M8ExactSettlementRenewalFixture
open M8AcceptanceSettlementRenewalRegression

def exactTender : SourceBackedTenderAt exactResidualActivation :=
  sourceBackedTender exactResidualActivation

def exactCounterpartyAcceptance :
    CounterpartyAcceptedTenderAt exactResidualActivation exactTender :=
  counterpartyAcceptedTender exactResidualActivation () rfl rfl rfl

/-- Exact source-backed standing; unlike the old calibration, its carrier is
not `AdmittedObligation`. -/
def purchasingPowerStanding :
    PurchasingPowerStandingAt exactResidualActivation openZeroObserver :=
  PurchasingPowerStandingAt.generate exactCounterpartyAcceptance

def purchasingPowerRenewal :
    PurchasingPowerRenewalStepAt exactResidualActivation openZeroObserver :=
  purchasingPowerRenewalStep exactResidualActivation openZeroObserver
    exactCounterpartyAcceptance

@[simp] theorem exact_tender_medium : exactTender.medium = () :=
  rfl

@[simp] theorem exact_tender_source_event : exactTender.sourceEvent = .after :=
  rfl

theorem exact_acceptance_is_reciprocal_source_assumption :
    exactCounterpartyAcceptance.reciprocalAssumption =
      BearerAssumption.accepted () :=
  exactCounterpartyAcceptance.reciprocalAssumption_eq

theorem exact_acceptance_bearer_is_counterparty :
    (exactCounterpartyObligation exactResidualActivation).bearer =
      exchangeLaw.bearerOfActor
        (exactCounterpartyActor exactResidualActivation) :=
  exactCounterpartyAcceptance.reciprocalBearer_eq

theorem exact_tender_protects_counterparty_interest :
    (exactOpenSettlement exactResidualActivation).obligation.beneficiary =
      exchangeLaw.protectedInterestOfActor
        (exactCounterpartyActor exactResidualActivation) :=
  exactCounterpartyAcceptance.tenderBeneficiary_eq

theorem standing_price_domain_is_same_open_settlement :
    purchasingPowerStanding.priceObservation.openSettlement = openAt .a :=
  purchasingPowerStanding.price_open_eq

def standing_has_source_owned_next :
    SourceOwnsResponsibilityIncidence V
      (P.boundarySource
        purchasingPowerStanding.activatedConsumer.activation)
      (openAt .a).obligation :=
  purchasingPowerStanding.sourceOwnership

theorem standing_event_has_exact_trace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      residualConsumerCompiler.activationSeedAt
        Lifecycle.actualEventGame.source state
        (PurchasingPowerStandingAt.renewalEvent purchasingPowerStanding) :=
  PurchasingPowerStandingAt.event_mem_source_trace purchasingPowerStanding

theorem standing_next_is_exact_generated_step :
    (PurchasingPowerStandingAt.nextGeneratedState
      purchasingPowerStanding).generated =
      NativeResponsibilityProcess.Run.step
        (openOccurrence.generatedState settlementCompiler).generated
        generatedResidualConsumer.edge :=
  rfl

theorem every_exact_accepted_activation_generates_a_renewal_step
    (seed : residualConsumerCompiler.ExactActivationSeed)
    (reciprocalContent_eq :
      (exactCounterpartyObligation seed).content =
        (exactOpenSettlement seed).obligation.content)
    (beneficiary_eq : (exactOpenSettlement seed).obligation.beneficiary =
      exchangeLaw.protectedInterestOfActor (exactCounterpartyActor seed)) :
    Nonempty (PurchasingPowerRenewalStepAt seed
      (PriceObserverAt.zero
        (OpenSettlement := OpenSettlementAt settlementCompiler
          (seed.occurrence residualConsumerCompiler))
        (Value := Int))) :=
  ⟨purchasingPowerRenewalStep seed _
    (counterpartyAcceptedTender seed () rfl reciprocalContent_eq
      beneficiary_eq)⟩

/-- Actual full fulfillment excludes every source-backed standing whose
activation claims this exact occurrence, regardless of the activation seed
carrier or price observer. -/
theorem fulfilled_occurrence_eliminates_any_purchasing_standing
    {otherActivationCompiler :
      SourceOwnedResidualConsumerCompiler settlementCompiler}
    (seed : otherActivationCompiler.ExactActivationSeed)
    (occurrence_eq : seed.occurrence otherActivationCompiler =
      fulfilledOccurrence)
    {PriceValue : Type*}
    (observer : ExchangePriceObserverAt
      (settlementCompiler := settlementCompiler)
      (seed.occurrence otherActivationCompiler) PriceValue) :
    IsEmpty (PurchasingPowerStandingAt seed observer) :=
  fullyFulfilledOccurrence_eliminatesStanding fullyFulfilled seed
    occurrence_eq observer

theorem fulfilled_occurrence_price_domain_empty :
    IsEmpty (OpenSettlementAt settlementCompiler fulfilledOccurrence) ∧
      ¬ Nonempty (ExchangePriceObservationAt fulfilledZeroObserver) :=
  fully_fulfilled_has_no_price_domain

/-- Direct consumer combines the old exact settlement calibration with the
new non-alias standing and one arbitrary exact renewal step. -/
structure PurchasingPowerStandingCertificate where
  priorCalibration : AcceptanceSettlementRenewalCertificate
  standing : PurchasingPowerStandingAt exactResidualActivation openZeroObserver
  tenderMediumExact : standing.tender.medium = ()
  reciprocalAcceptanceExact :
    standing.counterpartyAcceptance.reciprocalAssumption =
      BearerAssumption.accepted ()
  priceOpenExact : standing.priceObservation.openSettlement = openAt .a
  sourceOwnedNext : SourceOwnsResponsibilityIncidence V
    (P.boundarySource standing.activatedConsumer.activation)
    (openAt .a).obligation
  renewalStep : PurchasingPowerRenewalStepAt
    exactResidualActivation openZeroObserver
  priceDefinedIffOpen :
    Nonempty (ExchangePriceObservationAt openZeroObserver) ↔
      Nonempty (OpenSettlementAt settlementCompiler openOccurrence)
  fulfilledPriceDomainEmpty :
    IsEmpty (OpenSettlementAt settlementCompiler fulfilledOccurrence) ∧
      ¬ Nonempty (ExchangePriceObservationAt fulfilledZeroObserver)

def purchasingPowerStandingDirectConsumer :
    PurchasingPowerStandingCertificate where
  priorCalibration := acceptanceSettlementRenewalDirectConsumer
  standing := purchasingPowerStanding
  tenderMediumExact := exact_tender_medium
  reciprocalAcceptanceExact :=
    exact_acceptance_is_reciprocal_source_assumption
  priceOpenExact := standing_price_domain_is_same_open_settlement
  sourceOwnedNext := standing_has_source_owned_next
  renewalStep := purchasingPowerRenewal
  priceDefinedIffOpen := open_price_domain_exact
  fulfilledPriceDomainEmpty := fulfilled_occurrence_price_domain_empty

end
end M8PurchasingPowerStandingRegression
end Society
end ProcessGame
end SaturationMonoid
