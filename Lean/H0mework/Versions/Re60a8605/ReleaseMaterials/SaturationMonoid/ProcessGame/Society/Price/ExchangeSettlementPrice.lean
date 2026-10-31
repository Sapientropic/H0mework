import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Price.SettlementPriceObserver
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Settlement.ExchangeSettlement

/-!
# Strong price domain for exchange settlement

The generic price observer is specialized to the exact exchange-indexed open
settlement fibre.  The resulting equivalence is stronger than mere
inhabitation: every price observation is exactly one open responsibility
occurrence, and every such occurrence has exactly one observation record for
the fixed observer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Price

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement
open Settlement.SourceOwnedSettlementCompiler

universe u v w x y z q r

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

abbrev ExchangePriceObserverAt
    (occurrence : settlementCompiler.GeneratedSettlementOccurrence)
    (Value : Type r) :=
  PriceObserverAt
    (OpenSettlementAt settlementCompiler occurrence) Value

abbrev ExchangePriceObservationAt
    {occurrence : settlementCompiler.GeneratedSettlementOccurrence}
    {Value : Type r}
    (observer : ExchangePriceObserverAt occurrence Value) :=
  PriceObservationAt observer

/-- Strong carrier theorem: price observations and exact open exchange
settlements are constructively equivalent. -/
def exchangePriceObservationEquivOpenSettlement
    {occurrence : settlementCompiler.GeneratedSettlementOccurrence}
    {Value : Type r}
    (observer : ExchangePriceObserverAt occurrence Value) :
    ExchangePriceObservationAt observer ≃
      OpenSettlementAt settlementCompiler occurrence :=
  priceObservationEquivOpenSettlement observer

theorem exchangePriceDefined_iff_openSettlement
    {occurrence : settlementCompiler.GeneratedSettlementOccurrence}
    {Value : Type r}
    (observer : ExchangePriceObserverAt occurrence Value) :
    Nonempty (ExchangePriceObservationAt observer) ↔
      Nonempty (OpenSettlementAt settlementCompiler occurrence) :=
  priceObservation_nonempty_iff_openSettlement_nonempty observer

/-- Fully fulfilled exchange settlement removes the price domain for every
observer and every value carrier. -/
theorem fullyFulfilled_noPrice
    {occurrence : settlementCompiler.GeneratedSettlementOccurrence}
    {Value : Type r}
    (fully : FullyFulfilledExchangeAt settlementCompiler occurrence)
    (observer : ExchangePriceObserverAt occurrence Value) :
    ¬ Nonempty (ExchangePriceObservationAt observer) :=
  noPriceObservation_of_noOpenSettlement
    fully.openSettlement_isEmpty observer

/-- An open exchange settlement supports a defined zero quote. -/
def openSettlementZeroPrice
    {occurrence : settlementCompiler.GeneratedSettlementOccurrence}
    {Value : Type r} [Zero Value]
    (openSettlement : OpenSettlementAt settlementCompiler occurrence) :
    ExchangePriceObservationAt
      (PriceObserverAt.zero
        (OpenSettlement :=
          OpenSettlementAt settlementCompiler occurrence)
        (Value := Value)) :=
  zeroPriceObservation openSettlement

@[simp] theorem openSettlementZeroPrice_value
    {occurrence : settlementCompiler.GeneratedSettlementOccurrence}
    {Value : Type r} [Zero Value]
    (openSettlement : OpenSettlementAt settlementCompiler occurrence) :
    (openSettlementZeroPrice (Value := Value) openSettlement).value = 0 :=
  rfl

end Price
end Society
end ProcessGame
end SaturationMonoid
