import Mathlib.Data.Set.Basic

/-!
# Price observations exist exactly on open settlement fibres

The observer receives an already generated open-settlement carrier.  Its
quote is a readout on that carrier: no price value enters the source,
exchange, responsibility process, or settlement compiler.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Price

universe u v

/-- A price observer is only a readout on an existing open-settlement fibre. -/
structure PriceObserverAt (OpenSettlement : Type u) (Value : Type v) where
  quote : OpenSettlement → Value

/-- A price observation stores its exact domain occurrence, never a
caller-selected value.  The value is recomputed by the fixed observer. -/
structure PriceObservationAt
    {OpenSettlement : Type u} {Value : Type v}
    (observer : PriceObserverAt OpenSettlement Value) where
  openSettlement : OpenSettlement

namespace PriceObservationAt

variable {OpenSettlement : Type u} {Value : Type v}
variable {observer : PriceObserverAt OpenSettlement Value}

/-- Price value is an observer readout and has no authority over its domain. -/
def value (observation : PriceObservationAt observer) : Value :=
  observer.quote observation.openSettlement

end PriceObservationAt

/-- Strong carrier form of the price-domain theorem. -/
def priceObservationEquivOpenSettlement
    {OpenSettlement : Type u} {Value : Type v}
    (observer : PriceObserverAt OpenSettlement Value) :
    PriceObservationAt observer ≃ OpenSettlement where
  toFun := PriceObservationAt.openSettlement
  invFun := fun openSettlement => ⟨openSettlement⟩
  left_inv := by rintro ⟨openSettlement⟩; rfl
  right_inv := by intro openSettlement; rfl

/-- A price observation exists exactly when an open settlement exists. -/
theorem priceObservation_nonempty_iff_openSettlement_nonempty
    {OpenSettlement : Type u} {Value : Type v}
    (observer : PriceObserverAt OpenSettlement Value) :
    Nonempty (PriceObservationAt observer) ↔ Nonempty OpenSettlement := by
  constructor
  · rintro ⟨observation⟩
    exact ⟨observation.openSettlement⟩
  · rintro ⟨openSettlement⟩
    exact ⟨⟨openSettlement⟩⟩

/-- The zero observer still has the full open-settlement domain. -/
def PriceObserverAt.zero
    {OpenSettlement : Type u} {Value : Type v} [Zero Value] :
    PriceObserverAt OpenSettlement Value where
  quote := fun _ => 0

/-- Zero quote is a genuine price observation whenever settlement is open. -/
def zeroPriceObservation
    {OpenSettlement : Type u} {Value : Type v} [Zero Value]
    (openSettlement : OpenSettlement) :
    PriceObservationAt
      (PriceObserverAt.zero (OpenSettlement := OpenSettlement)
        (Value := Value)) :=
  ⟨openSettlement⟩

@[simp] theorem zeroPriceObservation_value
    {OpenSettlement : Type u} {Value : Type v} [Zero Value]
    (openSettlement : OpenSettlement) :
    (zeroPriceObservation (Value := Value) openSettlement).value = 0 :=
  rfl

/-- An empty settlement fibre removes the price observer's domain; this is
not represented by a distinguished price value. -/
theorem priceObservationIsEmpty
    {OpenSettlement : Type u} {Value : Type v}
    (empty : IsEmpty OpenSettlement)
    (observer : PriceObserverAt OpenSettlement Value) :
    IsEmpty (PriceObservationAt observer) :=
  ⟨fun observation => empty.false observation.openSettlement⟩

theorem noPriceObservation_of_noOpenSettlement
    {OpenSettlement : Type u} {Value : Type v}
    (empty : IsEmpty OpenSettlement)
    (observer : PriceObserverAt OpenSettlement Value) :
    ¬ Nonempty (PriceObservationAt observer) := by
  rintro ⟨observation⟩
  exact (priceObservationIsEmpty empty observer).false observation

end Price
end Society
end ProcessGame
end SaturationMonoid
