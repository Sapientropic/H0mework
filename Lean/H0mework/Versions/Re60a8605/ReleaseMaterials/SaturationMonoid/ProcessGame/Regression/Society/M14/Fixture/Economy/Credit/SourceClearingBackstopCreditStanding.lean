import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Money.PurchasingPowerStanding
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Clearing.Backstop.SourceGeneratedClearingBackstopActivation

/-!
# M14 source-generated standing at the clearing backstop

The existing C5 exact `b` activation is fed directly into the production
money interface.  Its exchange-generated counterparty admission supplies the
accepted tender, and `PurchasingPowerStandingAt.generate` supplies the sole
standing.  Borrower, creditor, relation, obligation, open settlement, source
event, and next state are all read from the existing exchange and backstop
compilers.

This fixture introduces no credit/default/risk-pool kind, actor or money
registry, money source, occurrence, run, ledger, claim table, future code, or
completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceClearingBackstopCreditStanding

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money Clearing
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M4AutomaticFullFulfillmentRegression
open M14ClearingConsumerDeath
open M14SourceGeneratedClearingBackstopActivation

/-! ## Existing exchange relation and counterparties -/

/-- Obligation-side actor of the exact open `b` leg. -/
def borrowerActor : core.TargetActor :=
  exactExchangeSeed.actor exchangeCompiler (.b : Leg)

/-- Beneficiary-side actor forced by the existing counterparty involution. -/
def creditorActor : core.TargetActor :=
  exactExchangeSeed.actor exchangeCompiler
    (exactExchangeSeed.counterparty exchangeCompiler (.b : Leg))

def creditRelation : relationCompiler.GeneratedRelation :=
  exactExchangeSeed.relation exchangeCompiler (.b : Leg)

def creditObligation : AdmittedObligation M3FiniteExchangeFixture.V :=
  exactExchangeSeed.obligation exchangeCompiler (.b : Leg)

theorem creditInterest :
    relationCompiler.GeneratedInterestAt borrowerActor creditRelation :=
  exactExchangeSeed.interest exchangeCompiler (.b : Leg)

@[simp] theorem borrowerActor_value_exact :
    borrowerActor.1 = Lifecycle.TargetToken.t1 :=
  rfl

@[simp] theorem creditorActor_is_counterparty_A :
    creditorActor = exactExchangeSeed.actor exchangeCompiler (.a : Leg) :=
  rfl

@[simp] theorem creditorActor_value_exact :
    creditorActor.1 = Lifecycle.TargetToken.t0 :=
  rfl

theorem borrower_ne_creditor : borrowerActor ≠ creditorActor :=
  SourceOwnedExchangeLaw.counterparty_actors_distinct exchangeLaw
    exactExchangeSeed (.b : Leg)

@[simp] theorem creditObligation_is_existing_open_B :
    creditObligation = partialOpenB.obligation :=
  rfl

/-! ## Exact accepted tender and standing -/

def backstopTender :
    SourceBackedTenderAt sourceGeneratedClearingBackstopExactSeed :=
  sourceBackedTender sourceGeneratedClearingBackstopExactSeed

/-- The acceptance receipt is the existing counterparty leg's admitted
`accepted` assumption.  No receipt is accepted at this producer mouth. -/
def backstopCounterpartyAcceptedTender :
    CounterpartyAcceptedTenderAt sourceGeneratedClearingBackstopExactSeed
      backstopTender :=
  counterpartyAcceptedTender sourceGeneratedClearingBackstopExactSeed
    () rfl rfl rfl

/-- Sole zero-argument standing producer. -/
def sourceGeneratedClearingBackstopCreditStanding :
    PurchasingPowerStandingAt sourceGeneratedClearingBackstopExactSeed
      partialZeroObserver :=
  PurchasingPowerStandingAt.generate backstopCounterpartyAcceptedTender

/-! ## Exact source and receipt provenance -/

@[simp] theorem standing_occurrence_exact :
    sourceGeneratedClearingBackstopExactSeed.occurrence
        partialBResidualConsumerCompiler = partialOccurrence :=
  backstop_occurrence_exact

@[simp] theorem standing_openSettlement_exact :
    PurchasingPowerStandingAt.openSettlement
        sourceGeneratedClearingBackstopCreditStanding = partialOpenB :=
  rfl

@[simp] theorem standing_open_leg_exact :
    (PurchasingPowerStandingAt.openSettlement
      sourceGeneratedClearingBackstopCreditStanding).leg = (.b : Leg) :=
  rfl

@[simp] theorem standing_borrower_relation_exact :
    creditRelation =
      exactExchangeSeed.relation exchangeCompiler (.b : Leg) :=
  rfl

@[simp] theorem standing_creditor_exact :
    PurchasingPowerStandingAt.counterparty
        sourceGeneratedClearingBackstopCreditStanding = creditorActor :=
  rfl

@[simp] theorem standing_medium_exact :
    PurchasingPowerStandingAt.medium
        sourceGeneratedClearingBackstopCreditStanding =
      partialOpenB.obligation.content :=
  rfl

@[simp] theorem counterparty_obligation_is_existing_A :
    exactCounterpartyObligation sourceGeneratedClearingBackstopExactSeed =
      exactExchangeSeed.obligation exchangeCompiler (.a : Leg) :=
  rfl

theorem acceptedTender_receipt_provenance :
    backstopTender.sourceEvent =
        M3FiniteExchangeFixture.P.boundarySource
          canonicalAClearingFace.counterpartyConsumer.event ∧
      backstopCounterpartyAcceptedTender.reciprocalAssumption =
        BearerAssumption.accepted
          backstopCounterpartyAcceptedTender.acceptanceReceipt ∧
      (exactCounterpartyObligation
          sourceGeneratedClearingBackstopExactSeed).content =
        backstopTender.medium ∧
      (exactCounterpartyObligation
          sourceGeneratedClearingBackstopExactSeed).bearer =
        exchangeLaw.bearerOfActor creditorActor ∧
      partialOpenB.obligation.beneficiary =
        exchangeLaw.protectedInterestOfActor creditorActor :=
  ⟨rfl,
    backstopCounterpartyAcceptedTender.reciprocalAssumption_eq,
    backstopCounterpartyAcceptedTender.reciprocalContent_eq,
    backstopCounterpartyAcceptedTender.reciprocalBearer_eq,
    backstopCounterpartyAcceptedTender.tenderBeneficiary_eq⟩

theorem standing_source_trace_provenance :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      partialBResidualConsumerCompiler.activationSeedAt
        Lifecycle.actualEventGame.source state
        (PurchasingPowerStandingAt.renewalEvent
          sourceGeneratedClearingBackstopCreditStanding) :=
  PurchasingPowerStandingAt.event_mem_source_trace
    sourceGeneratedClearingBackstopCreditStanding

theorem standing_source_ownership :
    Nonempty (SourceOwnsResponsibilityIncidence M3FiniteExchangeFixture.V
      (M3FiniteExchangeFixture.P.boundarySource
        canonicalAClearingFace.counterpartyConsumer.event)
      partialOpenB.obligation) :=
  ⟨sourceGeneratedClearingBackstopCreditStanding.sourceOwnership⟩

/-! ## Existing generated next -/

@[simp] theorem standing_activatedConsumer_is_C4_adapter :
    sourceGeneratedClearingBackstopCreditStanding.activatedConsumer =
      rawBackstopAdapter :=
  rfl

@[simp] theorem standing_next_is_existing_backstop_next :
    PurchasingPowerStandingAt.nextGeneratedState
        sourceGeneratedClearingBackstopCreditStanding =
      sourceGeneratedClearingBackstopActivation.nextGeneratedState :=
  rfl

@[simp] theorem standing_next_current_is_fulfillB_target :
    (PurchasingPowerStandingAt.nextGeneratedState
      sourceGeneratedClearingBackstopCreditStanding).current =
        fulfillB.target :=
  rfl

theorem standing_next_whole_run_and_history_exact :
    (PurchasingPowerStandingAt.nextGeneratedState
        sourceGeneratedClearingBackstopCreditStanding).generated =
      .step (partialOccurrence.generatedState settlementCompiler).generated
        fulfillB ∧
      fulfillB.target.history =
        (partialOccurrence.current settlementCompiler).history ++
          [fulfillB.lifecycleEvent] ∧
      Nonempty (AutomaticFullFulfillment.FulfilledSlotAt
        (exchangeLaw := exchangeLaw) exactExchangeSeed
        (PurchasingPowerStandingAt.nextGeneratedState
          sourceGeneratedClearingBackstopCreditStanding).current
        (.b : Leg)) :=
  ⟨backstop_whole_generated_next_exact,
    backstop_history_exact,
    ⟨backstopFulfilledB⟩⟩

/-! ## Old-source and one-sided controls -/

theorem rawAdapter_does_not_retype_old_source_compiler :
    Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt partialOpenB) ∧
      (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        (activation.openSettlement residualConsumerCompiler).leg = .b) ∧
      (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        activation.occurrence residualConsumerCompiler = partialOccurrence) :=
  ⟨⟨rawBackstopAdapter⟩,
    residualCompiler_cannot_select_B,
    residualCompiler_cannot_point_to_partialOccurrence⟩

/-- The C1 one-sided `a` action leaves `b` unfulfilled, whereas the standing
next is the later source-generated `fulfillB` state. -/
theorem oneSidedA_cannot_supply_backstop_credit_next :
    canonicalAClearingFace.oneSidedEdge = fulfillA ∧
      IsEmpty (AutomaticFullFulfillment.FulfilledSlotAt
        (exchangeLaw := exchangeLaw) exactExchangeSeed
        canonicalAClearingFace.oneSidedEdge.target (.b : Leg)) ∧
      Nonempty (AutomaticFullFulfillment.FulfilledSlotAt
        (exchangeLaw := exchangeLaw) exactExchangeSeed
        (PurchasingPowerStandingAt.nextGeneratedState
          sourceGeneratedClearingBackstopCreditStanding).current
        (.b : Leg)) :=
  ⟨canonicalA_oneSidedEdge_eq_fulfillA,
    canonicalAClearingFace.oneSided_counterpartyFulfilled_isEmpty,
    ⟨backstopFulfilledB⟩⟩

theorem standing_producer_has_no_new_ontology_or_future_fields : True := by
  let standing := sourceGeneratedClearingBackstopCreditStanding
  fail_if_success exact standing.creditKind
  fail_if_success exact standing.defaultKind
  fail_if_success exact standing.riskPool
  fail_if_success exact standing.actorRegistry
  fail_if_success exact standing.moneySource
  fail_if_success exact standing.claimRegistry
  fail_if_success exact standing.ledger
  fail_if_success exact standing.futureSchedule
  fail_if_success exact standing.completedFuture
  trivial

end
end M14SourceClearingBackstopCreditStanding
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopCreditStanding.creditInterest
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopCreditStanding.backstopCounterpartyAcceptedTender
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopCreditStanding.sourceGeneratedClearingBackstopCreditStanding
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopCreditStanding.acceptedTender_receipt_provenance
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopCreditStanding.standing_next_whole_run_and_history_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopCreditStanding.rawAdapter_does_not_retype_old_source_compiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopCreditStanding.oneSidedA_cannot_supply_backstop_credit_next
