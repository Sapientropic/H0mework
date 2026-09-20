/-!
# Constructive presentations for living-law core

`Equiv.trans`, `Equiv.sigmaCongrRight`, and the generic inverse-law accessors
currently pass through quotient/extensional infrastructure.  The living-law
core only needs explicit forward/backward programs and their two inverse laws.
This module provides that data directly; conversion to Mathlib `Equiv` is a
downstream adapter, not the core composition law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution

universe u v w

/-- A bidirectional presentation carried by explicit programs and inverse
laws.  No quotient, choice, or propositional extensionality is used. -/
structure ConstructivePresentation (A : Type u) (B : Type v) where
  forward : A → B
  backward : B → A
  backward_forward : ∀ value, backward (forward value) = value
  forward_backward : ∀ value, forward (backward value) = value

namespace ConstructivePresentation

def refl (A : Type u) : ConstructivePresentation A A where
  forward := fun value => value
  backward := fun value => value
  backward_forward := fun _ => rfl
  forward_backward := fun _ => rfl

def symm
    {A : Type u} {B : Type v}
    (presentation : ConstructivePresentation A B) :
    ConstructivePresentation B A where
  forward := presentation.backward
  backward := presentation.forward
  backward_forward := presentation.forward_backward
  forward_backward := presentation.backward_forward

def trans
    {A : Type u} {B : Type v} {C : Type w}
    (left : ConstructivePresentation A B)
    (right : ConstructivePresentation B C) :
    ConstructivePresentation A C where
  forward := fun value => right.forward (left.forward value)
  backward := fun value => left.backward (right.backward value)
  backward_forward := by
    intro value
    calc
      left.backward (right.backward (right.forward (left.forward value))) =
          left.backward (left.forward value) :=
        congrArg left.backward (right.backward_forward (left.forward value))
      _ = value := left.backward_forward value
  forward_backward := by
    intro value
    calc
      right.forward (left.forward (left.backward (right.backward value))) =
          right.forward (right.backward value) :=
        congrArg right.forward (left.forward_backward (right.backward value))
      _ = value := right.forward_backward value

def cast
    {I : Type u} {F : I → Type v} {left right : I}
    (index_eq : left = right) : ConstructivePresentation (F left) (F right) := by
  cases index_eq
  exact refl (F left)

def sigmaCongrRight
    {I : Type u} {A : I → Type v} {B : I → Type w}
    (presentation : (index : I) → ConstructivePresentation (A index) (B index)) :
    ConstructivePresentation (Σ index, A index) (Σ index, B index) where
  forward := fun value =>
    ⟨value.1, (presentation value.1).forward value.2⟩
  backward := fun value =>
    ⟨value.1, (presentation value.1).backward value.2⟩
  backward_forward := by
    rintro ⟨index, value⟩
    exact Sigma.ext rfl <|
      heq_of_eq ((presentation index).backward_forward value)
  forward_backward := by
    rintro ⟨index, value⟩
    exact Sigma.ext rfl <|
      heq_of_eq ((presentation index).forward_backward value)

/-- A zero-information source presentation can only target a genuinely
zero-information carrier.  Thus `PUnit` may seal an already indexed fact but
cannot hide a second value. -/
theorem subsingleton_target
    {A : Type u} {B : Type v}
    (presentation : ConstructivePresentation A B)
    [Subsingleton A] : Subsingleton B := by
  constructor
  intro left right
  calc
    left = presentation.forward (presentation.backward left) :=
      (presentation.forward_backward left).symm
    _ = presentation.forward (presentation.backward right) :=
      congrArg presentation.forward (Subsingleton.elim _ _)
    _ = right := presentation.forward_backward right

/-- Subsingleton-ness is invariant under a constructive presentation. -/
theorem subsingleton_source
    {A : Type u} {B : Type v}
    (presentation : ConstructivePresentation A B)
    [Subsingleton B] : Subsingleton A :=
  presentation.symm.subsingleton_target

end ConstructivePresentation

end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
