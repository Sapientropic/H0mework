import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M3.ExchangeAuthorityRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M3.ExchangeSettlementPriceRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M3.GoOpenKeyPriceRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M3.SettlementDispositionRegression

/-!
# M3 whole-program sink

One theorem consumes the universal finite-leg exchange, exact settlement
continuation, all native disposition branches, independent residual
activation, the strong price/open equivalence, target-smuggling controls, and
the honest G6 key-level consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M3WholeProgramRegression

open ResponsibilityLifecycle
open Settlement Exchange Price
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression

structure M3WholeProgramCertificate : Prop where
  finiteScopeNotBinary :
    (exactExchangeSeed.legList exchangeCompiler).length = 4
  nativeReciprocity : ∀ leg : exactExchangeSeed.Leg,
    relationCompiler.GeneratedInterestAt
        (exactExchangeSeed.actor exchangeCompiler leg)
        (exactExchangeSeed.relation exchangeCompiler leg) ∧
      Nonempty (incidence.TargetResponsibilityAt
        (exactExchangeSeed.actor exchangeCompiler leg)
        (exactExchangeSeed.obligation exchangeCompiler leg)
        (exactExchangeSeed.sourceEvent exchangeCompiler leg)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (exactExchangeSeed.sourceEvent exchangeCompiler leg)
        (exactExchangeSeed.obligation exchangeCompiler leg)) ∧
      (exactExchangeSeed.obligation exchangeCompiler leg).bearer =
        exchangeLaw.bearerOfActor
          (exactExchangeSeed.actor exchangeCompiler leg) ∧
      (exactExchangeSeed.obligation exchangeCompiler leg).beneficiary =
        exchangeLaw.protectedInterestOfActor
          (exactExchangeSeed.actor exchangeCompiler
            (exactExchangeSeed.counterparty exchangeCompiler leg))
  counterpartyExactProvenance : ∀ leg : exactExchangeSeed.Leg,
    ExactCounterpartyProvenanceAt leg
  exactDispositionExhaustion : ∀ leg : Leg,
    ∀ event : ReviewEvent
      (exactExchangeSeed.obligation exchangeCompiler leg),
      Nonempty (ExactSettlementEdge.LiveResidualAt
        (M3SettlementDispositionRegression.settlementOf leg event)) ∨
        Nonempty (ExactSettlementEdge.ClosedSettlementAt
          (M3SettlementDispositionRegression.settlementOf leg event))
  supersessionOpen : ∀ leg : Leg,
    Nonempty (ExactSettlementEdge.LiveResidualAt
      (M3SettlementDispositionRegression.settlementOf leg .supersede))
  bearerReleaseOpen : ∀ leg : Leg,
    Nonempty (ExactSettlementEdge.LiveResidualAt
      (M3SettlementDispositionRegression.settlementOf leg .bearerRelease))
  reopenSameDebt :
    SameDebtLineage
      M3SettlementDispositionRegression.fulfilledAArchive.obligation
      (M3SettlementDispositionRegression.reopenAAuthority.targetObligation P)
  residualConsumerExactSource :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = Lifecycle.EventState.after ∧
        residualConsumerCompiler.activationAdmittedAt
          exactResidualActivation.1
  residualConsumerActivated :
    generatedResidualConsumer.edge.target.history =
      (openOccurrence.current settlementCompiler).history ++
        [generatedResidualConsumer.edge.lifecycleEvent]
  residualConsumerWholeLedgerNext :
    generatedResidualConsumer.nextGeneratedState.generated =
      .step (openOccurrence.generatedState settlementCompiler).generated
        generatedResidualConsumer.edge
  residualConsumerExactTarget :
    generatedResidualConsumer.nextGeneratedState.current =
      generatedResidualConsumer.edge.target
  partialSettlementKeepsPrice :
    Nonempty (OpenSettlementAt settlementCompiler partialOccurrence) ∧
      Nonempty (ExchangePriceObservationAt partialZeroObserver)
  strongPriceCarrier :
    Nonempty (ExchangePriceObservationAt openZeroObserver ≃
      OpenSettlementAt settlementCompiler openOccurrence)
  fullyFulfilledNoPrice :
    IsEmpty (OpenSettlementAt settlementCompiler fulfilledOccurrence) ∧
      ¬ Nonempty (ExchangePriceObservationAt fulfilledZeroObserver)
  sameLineageForgeryRejected :
    SameDebtLineage
        (exactExchangeSeed.obligation exchangeCompiler .a)
        forgedObligation ∧
      IsEmpty ForgedSameLineageOpenA
  noAdmissionNoExchange :
    IsEmpty M3ExchangeAuthorityRegression.rejectedLaw.GeneratedExchange
  goClosureDoesNotMintPrice :
    Go.closureGain
        Go.G6ClosureGainRegression.gainUpdate = 2 ∧
      ¬ Nonempty (PriceObservationAt
        M3GoOpenKeyPriceRegression.gainZeroObserver)
  goOpenDebtCanHaveZeroQuote :
    Nonempty (Go.Obligation.GeneratedOpenKeyAt
        Go.G6ClosureGainRegression.debtUpdate) ∧
      Nonempty (PriceObservationAt
        M3GoOpenKeyPriceRegression.debtZeroObserver) ∧
      M3GoOpenKeyPriceRegression.debtZeroObservation.value = 0

theorem m3WholeProgram : M3WholeProgramCertificate where
  finiteScopeNotBinary := fixture_has_more_than_binary_scope
  nativeReciprocity := four_leg_native_reciprocity
  counterpartyExactProvenance := four_leg_counterparty_exact_provenance
  exactDispositionExhaustion :=
    M3SettlementDispositionRegression.every_review_is_live_or_closed
  supersessionOpen := fun leg =>
    ⟨M3SettlementDispositionRegression.supersessionOpen leg⟩
  bearerReleaseOpen := fun leg =>
    ⟨M3SettlementDispositionRegression.bearerReleaseOpen leg⟩
  reopenSameDebt :=
    M3SettlementDispositionRegression.exact_reopen_restores_live_same_lineage.2
  residualConsumerExactSource := by
    simpa [Lifecycle.Universal.FixedAdapter.core,
      Lifecycle.Universal.FixedAdapter.targetFace] using
      residual_activation_has_exact_source
  residualConsumerActivated := generated_consumer_appends_whole_ledger_next
  residualConsumerWholeLedgerNext :=
    generated_consumer_generates_whole_ledger_next
  residualConsumerExactTarget :=
    generated_consumer_next_current_is_exact_target
  partialSettlementKeepsPrice :=
    ⟨one_fulfilled_leg_does_not_remove_price_domain.2.1,
      one_fulfilled_leg_does_not_remove_price_domain.2.2⟩
  strongPriceCarrier := ⟨openPriceEquiv⟩
  fullyFulfilledNoPrice := fully_fulfilled_has_no_price_domain
  sameLineageForgeryRejected :=
    ⟨forgedObligation_sameDebtLineage, forgedSameLineageOpenA_isEmpty⟩
  noAdmissionNoExchange :=
    M3ExchangeAuthorityRegression.rejectedGeneratedExchange_isEmpty
  goClosureDoesNotMintPrice :=
    M3GoOpenKeyPriceRegression.positive_closureGain_does_not_create_price_domain
  goOpenDebtCanHaveZeroQuote :=
    M3GoOpenKeyPriceRegression.generated_debt_has_defined_zero_price

end M3WholeProgramRegression
end Society
end ProcessGame
end SaturationMonoid
