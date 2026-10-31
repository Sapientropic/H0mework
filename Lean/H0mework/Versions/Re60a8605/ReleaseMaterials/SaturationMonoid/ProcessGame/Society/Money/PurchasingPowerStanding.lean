import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Price.ExchangeSettlementPrice

/-!
# Source-backed purchasing-power standing

Purchasing power is not an alias for an obligation.  One exact residual-
consumer activation generates a tender from the open obligation's content,
the reciprocal counterparty's accepted admission, the exact open settlement,
a price observation on precisely that open fibre, and the source-owned next
responsibility state.

The construction adds no money registry, credit lineage, ledger, price
oracle, or completed future.  Price remains a readout on open settlement.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Money

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price
open Settlement.SourceOwnedSettlementCompiler

universe u v w x y z q s r

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game}
variable {V : Vocabulary.{x}}
variable {P : NativeResponsibilityProcess V}
variable {incidence : ActorResponsibilityIncidence core V}
variable
  {relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, w, y}
    occurrenceOf game core.targetFace}
variable
  {exchangeLaw : SourceOwnedExchangeLaw.{u, v, w, x, y, z}
    core V P incidence relationCompiler}
variable
  {settlementCompiler : SourceOwnedSettlementCompiler.{u, v, w, x, y, z, q}
    exchangeLaw}
variable
  {activationCompiler :
    SourceOwnedResidualConsumerCompiler.{u, v, w, x, y, z, q, s}
      settlementCompiler}

abbrev ExactActivationSeed := activationCompiler.ExactActivationSeed

abbrev exactSettlementOccurrence
    (seed : ExactActivationSeed (activationCompiler := activationCompiler)) :=
  seed.occurrence activationCompiler

abbrev exactOpenSettlement
    (seed : ExactActivationSeed (activationCompiler := activationCompiler)) :=
  seed.openSettlement activationCompiler

abbrev exactExchangeSeed
    (seed : ExactActivationSeed (activationCompiler := activationCompiler)) :=
  (seed.occurrence activationCompiler).exchangeSeed settlementCompiler

def exactCounterpartyLeg
    (seed : ExactActivationSeed (activationCompiler := activationCompiler)) :
    (seed.occurrence activationCompiler).Leg settlementCompiler :=
  (exactExchangeSeed seed).counterparty exchangeLaw.compiler
    (exactOpenSettlement seed).leg

def exactCounterpartyActor
    (seed : ExactActivationSeed (activationCompiler := activationCompiler)) :
    core.TargetActor :=
  (exactExchangeSeed seed).actor exchangeLaw.compiler
    (exactCounterpartyLeg seed)

def exactCounterpartyObligation
    (seed : ExactActivationSeed (activationCompiler := activationCompiler)) :
    AdmittedObligation V :=
  (exactExchangeSeed seed).obligation exchangeLaw.compiler
    (exactCounterpartyLeg seed)

/-- Tender generated from the exact open obligation and current activation
source.  The constructor is private, so no caller can substitute a medium. -/
structure SourceBackedTenderAt
    (seed : ExactActivationSeed (activationCompiler := activationCompiler)) where
  private mk ::
  medium : V.Content
  medium_eq : medium = (exactOpenSettlement seed).obligation.content
  sourceEvent : V.SourceEvent
  sourceEvent_eq : sourceEvent =
    P.boundarySource (seed.activation activationCompiler)

def sourceBackedTender
    (seed : ExactActivationSeed (activationCompiler := activationCompiler)) :
    SourceBackedTenderAt seed :=
  ⟨(exactOpenSettlement seed).obligation.content, rfl,
    P.boundarySource (seed.activation activationCompiler), rfl⟩

/-- The source-generated reciprocal leg accepts the same tender content.
Acceptance is its exact admission assumption, and both bearer and protected
interest remain tied to the exchange-law counterparty actor. -/
structure CounterpartyAcceptedTenderAt
    (seed : ExactActivationSeed (activationCompiler := activationCompiler))
    (tender : SourceBackedTenderAt seed) where
  private mk ::
  reciprocalAssumption : BearerAssumption V
    (exactCounterpartyObligation seed).admission.sourceEvent
    (exactCounterpartyObligation seed).bearer
    (exactCounterpartyObligation seed).scope
  acceptanceReceipt : V.AcceptedAt
    (exactCounterpartyObligation seed).bearer
    (exactCounterpartyObligation seed).admission.sourceEvent
    (exactCounterpartyObligation seed).scope
  reciprocalAssumption_eq : reciprocalAssumption =
    BearerAssumption.accepted acceptanceReceipt
  reciprocalContent_eq :
    (exactCounterpartyObligation seed).content = tender.medium
  reciprocalBearer_eq : (exactCounterpartyObligation seed).bearer =
    exchangeLaw.bearerOfActor (exactCounterpartyActor seed)
  tenderBeneficiary_eq : (exactOpenSettlement seed).obligation.beneficiary =
    exchangeLaw.protectedInterestOfActor (exactCounterpartyActor seed)

/-- Generate exact counterparty acceptance once the two reciprocal source
obligations identify the tender content. -/
def counterpartyAcceptedTender
    (seed : ExactActivationSeed (activationCompiler := activationCompiler))
    (acceptanceReceipt : V.AcceptedAt
      (exactCounterpartyObligation seed).bearer
      (exactCounterpartyObligation seed).admission.sourceEvent
      (exactCounterpartyObligation seed).scope)
    (reciprocalAssumption_eq :
      (exactCounterpartyObligation seed).admission.assumption =
        BearerAssumption.accepted acceptanceReceipt)
    (reciprocalContent_eq : (exactCounterpartyObligation seed).content =
      (exactOpenSettlement seed).obligation.content)
    (tenderBeneficiary_eq : (exactOpenSettlement seed).obligation.beneficiary =
      exchangeLaw.protectedInterestOfActor (exactCounterpartyActor seed)) :
    CounterpartyAcceptedTenderAt seed (sourceBackedTender seed) where
  reciprocalAssumption :=
    (exactCounterpartyObligation seed).admission.assumption
  acceptanceReceipt := acceptanceReceipt
  reciprocalAssumption_eq := reciprocalAssumption_eq
  reciprocalContent_eq := reciprocalContent_eq
  reciprocalBearer_eq := exchangeLaw.bearer_eq (exactExchangeSeed seed)
    (exactCounterpartyLeg seed)
  tenderBeneficiary_eq := tenderBeneficiary_eq

/-- Source-backed purchasing power at one exact continuation activation.
The type is indexed by the exact seed and fixed price observer; its private
constructor prevents a free standing value or mismatched price domain. -/
structure PurchasingPowerStandingAt
    (seed : ExactActivationSeed (activationCompiler := activationCompiler))
    {PriceValue : Type r}
    (observer : ExchangePriceObserverAt
      (settlementCompiler := settlementCompiler)
      (seed.occurrence activationCompiler) PriceValue) where
  private mk ::
  tender : SourceBackedTenderAt seed
  counterpartyAcceptance : CounterpartyAcceptedTenderAt seed tender
  activatedConsumer : OpenSettlementAt.ActivatedResidualConsumerAt
    (exactOpenSettlement seed)
  activatedConsumer_eq :
    activatedConsumer = seed.activatedConsumer activationCompiler
  sourceOwnership : SourceOwnsResponsibilityIncidence V
    (P.boundarySource activatedConsumer.activation)
    (exactOpenSettlement seed).obligation
  priceObservation : ExchangePriceObservationAt observer
  price_open_eq : priceObservation.openSettlement = exactOpenSettlement seed

namespace PurchasingPowerStandingAt

variable {seed : ExactActivationSeed (activationCompiler := activationCompiler)}
variable {PriceValue : Type r}
variable {observer : ExchangePriceObserverAt
  (settlementCompiler := settlementCompiler)
  (seed.occurrence activationCompiler) PriceValue}

/-- Canonical producer from the exact activation and source-generated
counterparty acceptance. -/
def generate
    (accepted : CounterpartyAcceptedTenderAt seed (sourceBackedTender seed)) :
    PurchasingPowerStandingAt seed observer where
  tender := sourceBackedTender seed
  counterpartyAcceptance := accepted
  activatedConsumer := seed.activatedConsumer activationCompiler
  activatedConsumer_eq := rfl
  sourceOwnership := seed.sourceOwnership activationCompiler
  priceObservation := ⟨exactOpenSettlement seed⟩
  price_open_eq := rfl

def medium (standing : PurchasingPowerStandingAt seed observer) : V.Content :=
  standing.tender.medium

def openSettlement (_standing : PurchasingPowerStandingAt seed observer) :
    OpenSettlementAt settlementCompiler
    (seed.occurrence activationCompiler) :=
  exactOpenSettlement seed

def counterparty (_standing : PurchasingPowerStandingAt seed observer) :
    core.TargetActor :=
  exactCounterpartyActor seed

def renewalEvent (_standing : PurchasingPowerStandingAt seed observer) :
    activationCompiler.ActivationSeed :=
  seed.1

def nextGeneratedState (_standing : PurchasingPowerStandingAt seed observer) :
    P.GeneratedState :=
  seed.nextGeneratedState activationCompiler

theorem activatedConsumer_nextGenerated_exact
    (standing : PurchasingPowerStandingAt seed observer) :
    standing.activatedConsumer.nextGeneratedState =
      nextGeneratedState standing := by
  rw [standing.activatedConsumer_eq]
  rfl

theorem event_mem_source_trace :
    ∀ standing : PurchasingPowerStandingAt seed observer,
    ∃ state ∈ game.occurrence.trace,
      activationCompiler.activationSeedAt game.source state
        (renewalEvent standing) :=
  fun _ => seed.2

theorem next_generated_exact :
    ∀ standing : PurchasingPowerStandingAt seed observer,
    (nextGeneratedState standing).generated =
      NativeResponsibilityProcess.Run.step
        ((seed.occurrence activationCompiler).generatedState
          settlementCompiler).generated
        (seed.edge activationCompiler) :=
  fun _ => rfl

theorem next_current_exact :
    ∀ standing : PurchasingPowerStandingAt seed observer,
    (nextGeneratedState standing).current =
      (seed.edge activationCompiler).target :=
  fun _ => rfl

theorem history_append :
    (seed.edge activationCompiler).target.history =
      ((seed.occurrence activationCompiler).current settlementCompiler).history ++
        [(seed.edge activationCompiler).lifecycleEvent] :=
  seed.history_append activationCompiler

end PurchasingPowerStandingAt

/-- One arbitrary exact continuation step.  Every inhabitant carries its own
acceptance, settlement event, price-domain witness, source ownership, and
generated next; no horizon or future table is stored. -/
structure PurchasingPowerRenewalStepAt
    (seed : ExactActivationSeed (activationCompiler := activationCompiler))
    {PriceValue : Type r}
    (observer : ExchangePriceObserverAt
      (settlementCompiler := settlementCompiler)
      (seed.occurrence activationCompiler) PriceValue) where
  standing : PurchasingPowerStandingAt seed observer
  eventTrace : ∃ state ∈ game.occurrence.trace,
    activationCompiler.activationSeedAt game.source state
      (PurchasingPowerStandingAt.renewalEvent standing)
  nextGenerated : P.GeneratedState
  next_eq : nextGenerated =
    PurchasingPowerStandingAt.nextGeneratedState standing

def purchasingPowerRenewalStep
    (seed : ExactActivationSeed (activationCompiler := activationCompiler))
    {PriceValue : Type r}
    (observer : ExchangePriceObserverAt
      (settlementCompiler := settlementCompiler)
      (seed.occurrence activationCompiler) PriceValue)
    (accepted : CounterpartyAcceptedTenderAt seed (sourceBackedTender seed)) :
    PurchasingPowerRenewalStepAt seed observer :=
  let standing : PurchasingPowerStandingAt seed observer :=
    PurchasingPowerStandingAt.generate accepted
  ⟨standing, PurchasingPowerStandingAt.event_mem_source_trace standing,
    PurchasingPowerStandingAt.nextGeneratedState standing, rfl⟩

/-- Full fulfillment exactly eliminates both source-backed purchasing-power
standing and the price domain at the same settlement occurrence. -/
theorem fullyFulfilled_eliminatesStandingAndPrice
    (seed : ExactActivationSeed (activationCompiler := activationCompiler))
    {PriceValue : Type r}
    (observer : ExchangePriceObserverAt
      (settlementCompiler := settlementCompiler)
      (seed.occurrence activationCompiler) PriceValue)
    (fully : FullyFulfilledExchangeAt settlementCompiler
      (seed.occurrence activationCompiler)) :
    IsEmpty (PurchasingPowerStandingAt seed observer) ∧
      ¬ Nonempty (ExchangePriceObservationAt observer) := by
  constructor
  · exact ⟨fun _standing =>
      fully.openSettlement_isEmpty.false (exactOpenSettlement seed)⟩
  · exact fullyFulfilled_noPrice fully observer

/-- Occurrence-level form: if an exact activation is claimed to land in a
fully fulfilled occurrence, every source-backed purchasing-power standing
over that activation is empty.  The equality is used only to transport the
existing full-fulfillment emptiness theorem; no activation is manufactured. -/
theorem fullyFulfilledOccurrence_eliminatesStanding
    {occurrence : settlementCompiler.GeneratedSettlementOccurrence}
    (fully : FullyFulfilledExchangeAt settlementCompiler occurrence)
    (seed : ExactActivationSeed (activationCompiler := activationCompiler))
    (occurrence_eq : seed.occurrence activationCompiler = occurrence)
    {PriceValue : Type r}
    (observer : ExchangePriceObserverAt
      (settlementCompiler := settlementCompiler)
      (seed.occurrence activationCompiler) PriceValue) :
    IsEmpty (PurchasingPowerStandingAt seed observer) := by
  cases occurrence_eq
  exact (fullyFulfilled_eliminatesStandingAndPrice seed observer fully).1

end Money
end Society
end ProcessGame
end SaturationMonoid
