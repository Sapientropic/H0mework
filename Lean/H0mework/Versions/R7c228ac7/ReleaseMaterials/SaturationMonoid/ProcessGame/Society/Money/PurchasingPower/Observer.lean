import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Money.PurchasingPowerStanding

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Money

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price
open Settlement.SourceOwnedSettlementCompiler

universe u v w x y z q s r t

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

variable {seed : ExactActivationSeed (activationCompiler := activationCompiler)}
variable {Value : Type r} {NewValue : Type t}
variable {observer : ExchangePriceObserverAt
  (settlementCompiler := settlementCompiler) (seed.occurrence activationCompiler) Value}
variable (replacement : ExchangePriceObserverAt
  (settlementCompiler := settlementCompiler) (seed.occurrence activationCompiler) NewValue)

private theorem tender_is_from_the_exact_open_settlement (tender : SourceBackedTenderAt seed) :
    tender = sourceBackedTender seed := by
  rcases tender with ⟨medium, exactMedium, event, exactEvent⟩
  subst medium
  subst event
  rfl

namespace PurchasingPowerStandingAt

/-- Reuse the original accepted tender and activation with a different readout. -/
def reobserve (standing : PurchasingPowerStandingAt seed observer) :
    PurchasingPowerStandingAt seed replacement :=
  generate (tender_is_from_the_exact_open_settlement standing.tender ▸ standing.counterpartyAcceptance)

theorem reobserve_keeps_the_original_tender_acceptance_and_activation
    (standing : PurchasingPowerStandingAt seed observer) :
    (standing.reobserve replacement).tender = standing.tender ∧
      (standing.reobserve replacement).counterpartyAcceptance.acceptanceReceipt =
        standing.counterpartyAcceptance.acceptanceReceipt ∧
      (standing.reobserve replacement).activatedConsumer = standing.activatedConsumer ∧
      (standing.reobserve replacement).priceObservation.openSettlement = standing.priceObservation.openSettlement ∧
      (standing.reobserve replacement).nextGeneratedState = standing.nextGeneratedState := by
  have receipt (tender : SourceBackedTenderAt seed) (accepted : CounterpartyAcceptedTenderAt seed tender)
      (eq : tender = sourceBackedTender seed) :
      (eq ▸ accepted : CounterpartyAcceptedTenderAt seed (sourceBackedTender seed)).acceptanceReceipt =
        accepted.acceptanceReceipt := by
    cases eq
    rfl
  exact ⟨(tender_is_from_the_exact_open_settlement _).symm,
    receipt _ _ _, standing.activatedConsumer_eq.symm, standing.price_open_eq.symm, rfl⟩

/-- Every observer value can be read at the same paid occurrence, with
the same tender, acceptance, settlement and next responsibility state. -/
theorem every_quote_is_possible_on_the_same_actual_payment
    (standing : PurchasingPowerStandingAt seed observer) (value : NewValue) :
    ∃ replacement : ExchangePriceObserverAt (seed.occurrence activationCompiler) NewValue,
      (standing.reobserve replacement).priceObservation.value = value ∧
      (type_of% (standing.reobserve_keeps_the_original_tender_acceptance_and_activation replacement)) := by
  let constant : ExchangePriceObserverAt (seed.occurrence activationCompiler) NewValue := ⟨fun _ => value⟩
  exact ⟨constant, rfl, standing.reobserve_keeps_the_original_tender_acceptance_and_activation constant⟩

end PurchasingPowerStandingAt

namespace PurchasingPowerRenewalStepAt

def reobserve (payment : PurchasingPowerRenewalStepAt seed observer) :
    PurchasingPowerRenewalStepAt seed replacement :=
  ⟨payment.standing.reobserve replacement, payment.eventTrace, payment.nextGenerated, payment.next_eq⟩

end PurchasingPowerRenewalStepAt

end Money
end Society
end ProcessGame
end SaturationMonoid
