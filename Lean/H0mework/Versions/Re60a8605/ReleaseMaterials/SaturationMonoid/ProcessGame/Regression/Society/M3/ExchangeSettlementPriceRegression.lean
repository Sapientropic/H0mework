import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M3.FiniteExchangeFixture
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Price.ExchangeSettlementPrice

/-!
# Exact settlement and strong price-domain regression

The four-leg native exchange has two source-generated settlement currents:
the immediate exchange target, where every obligation is open, and the
dependent four-edge current, where every stable slot carries an exact
fulfilled archive.  A later activation consumes one open residual through
the installed process; it is not stored in the open occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M3ExchangeSettlementPriceRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture

abbrev exchangeState : P.GeneratedState :=
  exactExchangeSeed.generatedState exchangeCompiler

def fulfillA : P.Edge exchangeState.current :=
  .cross (exactExchangeSeed.obligationSlot exchangeCompiler .a)
    (exactExchangeSeed.obligation exchangeCompiler .a)
    (exactExchangeSeed.generatedState_obligationSlot_get exchangeCompiler .a)
    .fulfill

def slotBAfterA : Fin fulfillA.target.slots.length :=
  ⟨exactExchangeSeed.obligationSlotIndex exchangeCompiler .b, by decide⟩

theorem b_present_after_a :
    fulfillA.target.slots.get slotBAfterA =
      .live (exactExchangeSeed.obligation exchangeCompiler .b) :=
  rfl

def fulfillB : P.Edge fulfillA.target :=
  .cross slotBAfterA
    (exactExchangeSeed.obligation exchangeCompiler .b)
    b_present_after_a .fulfill

def slotCAfterB : Fin fulfillB.target.slots.length :=
  ⟨exactExchangeSeed.obligationSlotIndex exchangeCompiler .c, by decide⟩

theorem c_present_after_b :
    fulfillB.target.slots.get slotCAfterB =
      .live (exactExchangeSeed.obligation exchangeCompiler .c) :=
  rfl

def fulfillC : P.Edge fulfillB.target :=
  .cross slotCAfterB
    (exactExchangeSeed.obligation exchangeCompiler .c)
    c_present_after_b .fulfill

def slotDAfterC : Fin fulfillC.target.slots.length :=
  ⟨exactExchangeSeed.obligationSlotIndex exchangeCompiler .d, by decide⟩

theorem d_present_after_c :
    fulfillC.target.slots.get slotDAfterC =
      .live (exactExchangeSeed.obligation exchangeCompiler .d) :=
  rfl

def fulfillD : P.Edge fulfillC.target :=
  .cross slotDAfterC
    (exactExchangeSeed.obligation exchangeCompiler .d)
    d_present_after_c .fulfill

def fulfillmentRun : P.Run exchangeState.current fulfillD.target :=
  .step (.step (.step (.step .nil fulfillA) fulfillB) fulfillC) fulfillD

inductive SettlementSeed where
  | open
  | partlySettled
  | fulfilled
  deriving DecidableEq, Repr

def settlementCompiler : SourceOwnedSettlementCompiler exchangeLaw where
  SettlementSeed := SettlementSeed
  settlementAdmittedAt := fun _ => True
  exchangeSeed := fun _ => exactExchangeSeed
  continuation := fun seed =>
    match seed with
    | .open => ⟨exchangeState.current, .nil⟩
    | .partlySettled => ⟨fulfillA.target, .step .nil fulfillA⟩
    | .fulfilled => ⟨fulfillD.target, fulfillmentRun⟩

def exactOpenSeed : settlementCompiler.ExactSettlementSeed :=
  ⟨.open, .after, by simp [Lifecycle.actualEventOccurrenceOf], rfl, trivial⟩

def exactFulfilledSeed : settlementCompiler.ExactSettlementSeed :=
  ⟨.fulfilled, .after,
    by simp [Lifecycle.actualEventOccurrenceOf], rfl, trivial⟩

def exactPartialSeed : settlementCompiler.ExactSettlementSeed :=
  ⟨.partlySettled, .after,
    by simp [Lifecycle.actualEventOccurrenceOf], rfl, trivial⟩

def openOccurrence : settlementCompiler.GeneratedSettlementOccurrence :=
  settlementCompiler.occurrenceOfSeed exactOpenSeed

def fulfilledOccurrence : settlementCompiler.GeneratedSettlementOccurrence :=
  settlementCompiler.occurrenceOfSeed exactFulfilledSeed

def partialOccurrence : settlementCompiler.GeneratedSettlementOccurrence :=
  settlementCompiler.occurrenceOfSeed exactPartialSeed

def openAt (leg : Leg) :
    OpenSettlementAt settlementCompiler openOccurrence where
  leg := leg
  obligation := exactExchangeSeed.obligation exchangeCompiler leg
  present := by
    exact exactExchangeSeed.generatedState_obligationSlot_get
      exchangeCompiler leg

theorem all_four_legs_are_open :
    ∀ leg : Leg,
      ∃ openSettlement :
          OpenSettlementAt settlementCompiler openOccurrence,
        openSettlement.leg = leg :=
  fun leg => ⟨openAt leg, rfl⟩

def partialFulfilledA :
    FulfilledExchangeLegAt settlementCompiler partialOccurrence .a :=
  ⟨_, .after, (), rfl⟩

def partialOpenB :
    OpenSettlementAt settlementCompiler partialOccurrence :=
  ⟨.b, exactExchangeSeed.obligation exchangeCompiler .b, rfl⟩

def partialZeroObserver :
    ExchangePriceObserverAt (settlementCompiler := settlementCompiler)
      partialOccurrence Int :=
  PriceObserverAt.zero

/-- Closing one generated obligation cannot be misreported as full
settlement: another stable exchange leg remains open and price-defined. -/
theorem one_fulfilled_leg_does_not_remove_price_domain :
    Nonempty
        (FulfilledExchangeLegAt settlementCompiler partialOccurrence .a) ∧
      Nonempty (OpenSettlementAt settlementCompiler partialOccurrence) ∧
      Nonempty (ExchangePriceObservationAt partialZeroObserver) :=
  ⟨⟨partialFulfilledA⟩, ⟨partialOpenB⟩,
    ⟨openSettlementZeroPrice partialOpenB⟩⟩

/-- The later activation is a separate source seed family. -/
inductive ResidualActivationSeed where
  | maintainA
  deriving DecidableEq, Repr

def residualConsumerCompiler :
    SourceOwnedResidualConsumerCompiler settlementCompiler where
  ActivationSeed := ResidualActivationSeed
  activationAdmittedAt := fun _ => True
  settlementSeed := fun _ => exactOpenSeed
  openSettlement := fun _ => openAt .a
  boundaryEvent := fun _ => .maintain

def exactResidualActivation :
    residualConsumerCompiler.ExactActivationSeed :=
  ⟨.maintainA, .after,
    by simp [Lifecycle.actualEventOccurrenceOf], rfl, trivial⟩

def generatedResidualConsumer :
    residualConsumerCompiler.GeneratedResidualConsumerOccurrence :=
  residualConsumerCompiler.consumerOfSeed exactResidualActivation

/-- Actual downstream activation of one open residual.  This adapter is now
projected from an exact activation seed rather than constructed directly. -/
def activatedA :
    OpenSettlementAt.ActivatedResidualConsumerAt (openAt .a) :=
  exactResidualActivation.activatedConsumer residualConsumerCompiler

theorem residual_activation_has_exact_source :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = core.targetFace.state Lifecycle.actualEventGame.source ∧
        residualConsumerCompiler.activationAdmittedAt
          exactResidualActivation.1 :=
  exactResidualActivation.exact_state_provenance residualConsumerCompiler

theorem activated_consumer_generates_exact_next :
    activatedA.edge.target.history =
      (openOccurrence.current settlementCompiler).history ++
        [activatedA.edge.lifecycleEvent] ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource activatedA.activation)
        (openAt .a).obligation) :=
  ⟨activatedA.history_append, ⟨activatedA.sourceOwnership⟩⟩

theorem generated_consumer_appends_whole_ledger_next :
    generatedResidualConsumer.edge.target.history =
      (openOccurrence.current settlementCompiler).history ++
        [generatedResidualConsumer.edge.lifecycleEvent] :=
  generatedResidualConsumer.history_append

theorem generated_consumer_generates_whole_ledger_next :
    generatedResidualConsumer.nextGeneratedState.generated =
      .step (openOccurrence.generatedState settlementCompiler).generated
        generatedResidualConsumer.edge :=
  generatedResidualConsumer.nextGeneratedState_generated

theorem generated_consumer_next_current_is_exact_target :
    generatedResidualConsumer.nextGeneratedState.current =
      generatedResidualConsumer.edge.target :=
  generatedResidualConsumer.nextGeneratedState_current

def fulfilledAt (leg : Leg) :
    FulfilledExchangeLegAt settlementCompiler fulfilledOccurrence leg := by
  cases leg <;>
    exact ⟨_, .after, (), rfl⟩

def fullyFulfilled :
    FullyFulfilledExchangeAt settlementCompiler fulfilledOccurrence :=
  ⟨fulfilledAt⟩

def openZeroObserver :
    ExchangePriceObserverAt (settlementCompiler := settlementCompiler)
      openOccurrence Int :=
  PriceObserverAt.zero

def openAZeroPrice : ExchangePriceObservationAt openZeroObserver :=
  openSettlementZeroPrice (openAt .a)

theorem open_settlement_has_defined_zero_price :
    Nonempty (OpenSettlementAt settlementCompiler openOccurrence) ∧
      Nonempty (ExchangePriceObservationAt openZeroObserver) ∧
      openAZeroPrice.value = 0 :=
  ⟨⟨openAt .a⟩, ⟨openAZeroPrice⟩, rfl⟩

def fulfilledZeroObserver :
    ExchangePriceObserverAt (settlementCompiler := settlementCompiler)
      fulfilledOccurrence Int :=
  PriceObserverAt.zero

theorem fully_fulfilled_has_no_price_domain :
    IsEmpty (OpenSettlementAt settlementCompiler fulfilledOccurrence) ∧
      ¬ Nonempty (ExchangePriceObservationAt fulfilledZeroObserver) :=
  ⟨fullyFulfilled.openSettlement_isEmpty,
    fullyFulfilled_noPrice fullyFulfilled fulfilledZeroObserver⟩

/-- Strong form, consumed directly at the concrete occurrence. -/
def openPriceEquiv :
    ExchangePriceObservationAt openZeroObserver ≃
      OpenSettlementAt settlementCompiler openOccurrence :=
  exchangePriceObservationEquivOpenSettlement openZeroObserver

/-! ## Bare lineage cannot forge exchange-fibre membership -/

def forgedObligation : AdmittedObligation V :=
  admittedObligation .t5

theorem forgedObligation_sameDebtLineage :
    SameDebtLineage
      (exactExchangeSeed.obligation exchangeCompiler .a)
      forgedObligation :=
  rfl

structure ForgedSameLineageOpenA : Type where
  openSettlement : OpenSettlementAt settlementCompiler openOccurrence
  leg_eq : openSettlement.leg = .a
  obligation_eq : openSettlement.obligation = forgedObligation

theorem forgedSameLineageOpenA_isEmpty :
    IsEmpty ForgedSameLineageOpenA := by
  refine ⟨fun forged => ?_⟩
  have forgedPresent := forged.openSettlement.present
  rw [forged.leg_eq, forged.obligation_eq] at forgedPresent
  have canonicalPresent := (openAt .a).present
  have slotsEq :
      ObligationSlot.live forgedObligation =
        .live (exactExchangeSeed.obligation exchangeCompiler .a) :=
    forgedPresent.symm.trans canonicalPresent
  have obligationsEq := ObligationSlot.live.inj slotsEq
  have bearersEq := congrArg AdmittedObligation.bearer obligationsEq
  cases bearersEq

end M3ExchangeSettlementPriceRegression
end Society
end ProcessGame
end SaturationMonoid
