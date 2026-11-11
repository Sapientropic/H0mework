import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# No uniform ordinary algebraic perfect ambient

The countable free rational vector space cannot inject into a reflexive
rational vector space.  Consequently it cannot inject into either carrier of
an ordinary algebraically perfect pairing.

This is a category-exact no-go for ordinary algebraic reflexive or
`LinearMap.IsPerfPair` ambients.  It does not reject the source-generated
exact dual-image envelope, nor a later Ind--Pro, topological, or derived
perfectification whose duality lives in a larger category.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace UniversalAlgebraicPerfectAmbientNoGo

noncomputable section

abbrev InfiniteCarrier := ℕ →₀ ℚ

theorem infiniteCarrier_not_finite :
    ¬ Module.Finite ℚ InfiniteCarrier := by
  intro finite
  letI : Module.Finite ℚ InfiniteCarrier := finite
  letI : Finite ℕ :=
    Module.Finite.finite_basis (Finsupp.basisSingleOne (R := ℚ))
  exact not_finite ℕ

/-- A reflexive vector space over a field is finite-dimensional, so it cannot
contain the countable free vector space faithfully. -/
theorem no_injective_map_to_reflexive
    (P : Type*) [AddCommGroup P] [Module ℚ P]
    [Module.IsReflexive ℚ P]
    (inclusion : InfiniteCarrier →ₗ[ℚ] P) :
    ¬ Function.Injective inclusion := by
  intro inclusionInjective
  letI : FiniteDimensional ℚ P := inferInstance
  have sourceFinite : FiniteDimensional ℚ InfiniteCarrier :=
    FiniteDimensional.of_injective inclusion inclusionInjective
  exact infiniteCarrier_not_finite sourceFinite

/-- Bundled form of the forbidden ordinary algebraic ambient. -/
structure ReflexiveAmbient where
  Carrier : Type
  [carrierAddCommGroup : AddCommGroup Carrier]
  [carrierModule : Module ℚ Carrier]
  reflexive : Module.IsReflexive ℚ Carrier
  inclusion : InfiniteCarrier →ₗ[ℚ] Carrier
  inclusion_injective : Function.Injective inclusion

theorem reflexiveAmbient_isEmpty : IsEmpty ReflexiveAmbient := by
  constructor
  intro ambient
  letI : AddCommGroup ambient.Carrier := ambient.carrierAddCommGroup
  letI : Module ℚ ambient.Carrier := ambient.carrierModule
  letI : Module.IsReflexive ℚ ambient.Carrier := ambient.reflexive
  exact (no_injective_map_to_reflexive ambient.Carrier ambient.inclusion)
    ambient.inclusion_injective

/-- Mathlib perfect pairings force reflexivity on both sides, hence the same
infinite source cannot inject into either algebraic pairing carrier. -/
theorem no_injective_map_to_perfectPair
    (P Q : Type*)
    [AddCommGroup P] [Module ℚ P]
    [AddCommGroup Q] [Module ℚ Q]
    (pairing : P →ₗ[ℚ] Q →ₗ[ℚ] ℚ)
    [pairing.IsPerfPair]
    (inclusion : InfiniteCarrier →ₗ[ℚ] P) :
    ¬ Function.Injective inclusion := by
  letI : Module.IsReflexive ℚ P :=
    Module.IsReflexive.of_isPerfPair (p := pairing)
  exact no_injective_map_to_reflexive P inclusion

end
end UniversalAlgebraicPerfectAmbientNoGo
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
