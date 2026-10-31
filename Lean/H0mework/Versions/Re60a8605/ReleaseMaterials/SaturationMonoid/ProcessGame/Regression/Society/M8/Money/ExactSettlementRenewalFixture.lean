import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M3.ExchangeSettlementPriceRegression

/-!
# M8 exact money-renewal authority fixture

This fixture only exposes the already generated M3 acceptance, open
settlement, later residual-consumer activation, whole-ledger next, and full
fulfillment facts.  It creates no money registry, credit lineage, or price
oracle.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8ExactSettlementRenewalFixture

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression

theorem open_leg_has_exact_admission_event :
    exactExchangeSeed.admissionEvent exchangeCompiler .a = legToken .a :=
  rfl

theorem open_leg_source_has_exact_accepted_assumption :
    (admissionPayload (legToken .a)).assumption =
      BearerAssumption.accepted () :=
  rfl

theorem open_leg_has_exact_source_ownership :
    Nonempty (SourceOwnsResponsibilityIncidence V
      (exactExchangeSeed.sourceEvent exchangeCompiler .a)
      (openAt .a).obligation) :=
  four_leg_native_reciprocity .a |>.2.2.1

theorem later_acceptance_consumer_has_exact_source :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = core.targetFace.state Lifecycle.actualEventGame.source ∧
        residualConsumerCompiler.activationAdmittedAt
          exactResidualActivation.1 :=
  residual_activation_has_exact_source

theorem later_acceptance_generates_whole_ledger_next :
    generatedResidualConsumer.nextGeneratedState.generated =
      .step (openOccurrence.generatedState settlementCompiler).generated
        generatedResidualConsumer.edge ∧
      generatedResidualConsumer.nextGeneratedState.current =
        generatedResidualConsumer.edge.target :=
  ⟨generated_consumer_generates_whole_ledger_next,
    generated_consumer_next_current_is_exact_target⟩

theorem open_price_domain_exact :
    Nonempty (ExchangePriceObservationAt openZeroObserver) ↔
      Nonempty (OpenSettlementAt settlementCompiler openOccurrence) :=
  exchangePriceDefined_iff_openSettlement openZeroObserver

theorem open_zero_quote_remains_price_defined :
    Nonempty (OpenSettlementAt settlementCompiler openOccurrence) ∧
      Nonempty (ExchangePriceObservationAt openZeroObserver) ∧
      openAZeroPrice.value = 0 :=
  open_settlement_has_defined_zero_price

/-- Full settlement removes the carrier of price observations.  The mouth is
an empty-domain statement, never an equation assigning price zero. -/
theorem fully_settled_price_domain_empty :
    IsEmpty (OpenSettlementAt settlementCompiler fulfilledOccurrence) ∧
      ¬ Nonempty (ExchangePriceObservationAt fulfilledZeroObserver) :=
  fully_fulfilled_has_no_price_domain

end M8ExactSettlementRenewalFixture
end Society
end ProcessGame
end SaturationMonoid
