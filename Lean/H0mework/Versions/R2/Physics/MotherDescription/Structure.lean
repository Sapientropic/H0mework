import H0mework.Versions.R2.Physics.MotherDescription.Carrier

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.WholeDescription

open Stage9C.Revision
open NoIslandNoMagic.Consciousness.Representation

noncomputable section

universe u v

def pointRead {Output : Sort u} (read : Current → Output) (description : Pointwise) : Output :=
  read (decodePoint description)

def weakRead {Output : Sort u} (read : Current → Output) (description : Compact) : Output :=
  read (decodeWeak description)

theorem every_readout {Output : Sort u} (read : Current → Output) (description : Pointwise) :
    weakRead read (equivalence description) = pointRead read description :=
  congrArg read (equivalence_decodes description)

def pointRelation {Index : Type u} (relation : (Index → Current) → Prop)
    (objects : Index → Pointwise) : Prop := relation (decodePoint ∘ objects)

def weakRelation {Index : Type u} (relation : (Index → Current) → Prop)
    (objects : Index → Compact) : Prop := relation (decodeWeak ∘ objects)

/-- Relations of arbitrary arity are preserved and reflected. -/
theorem every_relation {Index : Type u} (relation : (Index → Current) → Prop)
    (objects : Index → Pointwise) :
    weakRelation relation (equivalence ∘ objects) ↔ pointRelation relation objects := by
  have decoded : decodeWeak ∘ (equivalence ∘ objects) = decodePoint ∘ objects :=
    funext (fun index => equivalence_decodes (objects index))
  unfold weakRelation pointRelation
  rw [decoded]

def pointOperation {Index : Type u} (operation : (Index → Current) → Current)
    (objects : Index → Pointwise) : Pointwise := point (operation (decodePoint ∘ objects))

def weakOperation {Index : Type u} (operation : (Index → Current) → Current)
    (objects : Index → Compact) : Compact := weak (operation (decodeWeak ∘ objects))

/-- Every source operation induces the same operation in both descriptions. -/
theorem every_operation {Index : Type u} (operation : (Index → Current) → Current)
    (objects : Index → Pointwise) :
    equivalence (pointOperation operation objects) =
      weakOperation operation (equivalence ∘ objects) := by
  have decoded : decodeWeak ∘ (equivalence ∘ objects) = decodePoint ∘ objects :=
    funext (fun index => equivalence_decodes (objects index))
  unfold pointOperation weakOperation
  rw [equivalence_point, decoded]

def pointAction (action : Current → Current) : Pointwise → Pointwise := point ∘ action ∘ decodePoint
def weakAction (action : Current → Current) : Compact → Compact := weak ∘ action ∘ decodeWeak

theorem weakAction_weak (action : Current → Current) (current : Current) :
    weakAction action (weak current) = weak (action current) := by
  change weak (action (decodeWeak (weak current))) = _
  rw [decodeWeak_weak]

theorem equivalence_action (action : Current → Current) (description : Pointwise) :
    equivalence (pointAction action description) = weakAction action (equivalence description) := by
  change equivalence (point (action (decodePoint description))) = weak (action (decodeWeak (equivalence description)))
  rw [equivalence_point, equivalence_decodes]

theorem weakAction_unique (action : Current → Current) (candidate : Compact → Compact)
    (commutes : ∀ current, candidate (weak current) = weak (action current)) :
    candidate = weakAction action :=
  FaceKernelExactAt.injectiveRangeFactor_unique compact_injective (weak ∘ action) candidate commutes

def pointNext : Pointwise → Pointwise := pointAction SpinPair.next
def weakNext : Compact → Compact := weakAction SpinPair.next

theorem next_commutes (description : Pointwise) :
    equivalence (pointNext description) = weakNext (equivalence description) :=
  equivalence_action SpinPair.next description

theorem next_unique : ∃! next : Compact → Compact,
    ∀ current, next (weak current) = weak (SpinPair.next current) :=
  ⟨weakNext, weakAction_weak SpinPair.next,
    fun candidate same => weakAction_unique SpinPair.next candidate same⟩

/-- Completeness of another description is checked against the original
physical consumers; no inverse or action law is requested from it. -/
theorem complete_injective {Description : Type u} {describe : Current → Description}
    (complete : FaceKernelExactAt consumers describe) : Function.Injective describe :=
  fun {left right} same => consumers_complete ((complete left right).1 same)

theorem every_complete_readout {Description : Type u} {Output : Type v}
    (describe : Current → Description) (complete : FaceKernelExactAt consumers describe)
    (read : Current → Output) :
    ∃! factor : Set.range describe → Output,
      ∀ current, factor ⟨describe current, current, rfl⟩ = read current :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization (complete_injective complete) read

/-- The action, including the native next, is generated on every complete
description. The comparison candidate never supplies its dynamics. -/
theorem every_complete_action {Description : Type u}
    (describe : Current → Description) (complete : FaceKernelExactAt consumers describe)
    (action : Current → Current) :
    ∃! lifted : Set.range describe → Set.range describe,
      ∀ current, lifted ⟨describe current, current, rfl⟩ =
        ⟨describe (action current), action current, rfl⟩ :=
  every_complete_readout describe complete
    (fun current => (⟨describe (action current), action current, rfl⟩ : Set.range describe))

end
end SaturationMonoid.PhysicsCore.Stage10.WholeDescription
