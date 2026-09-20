import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Integral indistinguishable-particle pair

The ordered tensor square is kinematical.  Its physical two-particle carrier
is the coinvariant quotient by the image of `swap - id`, so exchanging two
unlabelled particles changes only the presentation.  A swap-invariant linear
read descends canonically through this quotient.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedIntegralIndistinguishableParticlePair

noncomputable section

universe u v

variable (H : Type u) [AddCommGroup H]

abbrev OrderedPair := TensorProduct ℤ H H

/-- Exchange of the two kinematical tensor factors. -/
def swap : OrderedPair H →ₗ[ℤ] OrderedPair H :=
  (TensorProduct.comm ℤ H H).toLinearMap

@[simp] theorem swap_tmul (left right : H) :
    swap H (left ⊗ₜ[ℤ] right) = right ⊗ₜ[ℤ] left :=
  rfl

/-- The redundant-label direction removed by physical symmetrization. -/
def exchangeDifference : OrderedPair H →ₗ[ℤ] OrderedPair H :=
  swap H - LinearMap.id

/-- All integral linear combinations of exchange-presentation differences. -/
abbrev ExchangeRelation : Submodule ℤ (OrderedPair H) :=
  LinearMap.range (exchangeDifference H)

/-- The physical two-particle sector: ordered labels modulo exchange. -/
abbrev PhysicalPair := OrderedPair H ⧸ ExchangeRelation H

/-- Canonical kinematical-to-physical projection. -/
def projection : OrderedPair H →ₗ[ℤ] PhysicalPair H :=
  (ExchangeRelation H).mkQ

theorem projection_kernel :
    LinearMap.ker (projection H) = ExchangeRelation H :=
  by
    change LinearMap.ker (ExchangeRelation H).mkQ = ExchangeRelation H
    exact Submodule.ker_mkQ _

theorem projection_surjective : Function.Surjective (projection H) :=
  Submodule.mkQ_surjective _

/-- Every tensor and its exchanged presentation are one physical state. -/
@[simp] theorem projection_swap (value : OrderedPair H) :
    projection H (swap H value) = projection H value := by
  apply (Submodule.Quotient.eq _).2
  change swap H value - value ∈ LinearMap.range (exchangeDifference H)
  exact ⟨value, by simp [exchangeDifference]⟩

/-- Pure tensors are insensitive to the order of their two factors. -/
@[simp] theorem projection_tmul_swap (left right : H) :
    projection H (left ⊗ₜ[ℤ] right) =
      projection H (right ⊗ₜ[ℤ] left) := by
  simpa using (projection_swap H (left ⊗ₜ[ℤ] right)).symm

variable {H}
variable {X : Type v} [AddCommGroup X]

theorem exchangeRelation_le_ker
    (read : OrderedPair H →ₗ[ℤ] X)
    (swapInvariant : ∀ value, read (swap H value) = read value) :
    ExchangeRelation H ≤ LinearMap.ker read := by
  rintro _ ⟨value, rfl⟩
  change read (exchangeDifference H value) = 0
  simp [exchangeDifference, swapInvariant value]

/-- Canonical descent of a swap-invariant detector. -/
def descend
    (read : OrderedPair H →ₗ[ℤ] X)
    (swapInvariant : ∀ value, read (swap H value) = read value) :
    PhysicalPair H →ₗ[ℤ] X :=
  (ExchangeRelation H).liftQ read
    (exchangeRelation_le_ker read swapInvariant)

@[simp] theorem descend_projection
    (read : OrderedPair H →ₗ[ℤ] X)
    (swapInvariant : ∀ value, read (swap H value) = read value)
    (value : OrderedPair H) :
    descend read swapInvariant (projection H value) = read value :=
  rfl

end

end SourceGeneratedIntegralIndistinguishableParticlePair
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedIntegralIndistinguishableParticlePair.projection_tmul_swap
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedIntegralIndistinguishableParticlePair.descend_projection
