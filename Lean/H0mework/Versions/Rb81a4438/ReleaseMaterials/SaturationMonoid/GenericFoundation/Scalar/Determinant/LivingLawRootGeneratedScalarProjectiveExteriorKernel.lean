import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Scalar projective exterior powers

Finite projectivity generates a finite free presentation with a source-owned
splitting.  Exterior functoriality transports that splitting, so every
exterior power is again finite projective without choosing a basis of the
original carrier.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarProjectiveExterior

open Module

noncomputable section

universe r m

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]

/-- A finite projective module generates a finite projective exterior power
in every degree. -/
theorem finiteProjective_exteriorPower_projective
    (finite : Module.Finite R M) (projective : Module.Projective R M)
    (degree : ℕ) : Module.Projective R (⋀[R]^degree M) := by
  letI : Module.Finite R M := finite
  letI : Module.Projective R M := projective
  obtain ⟨generators, generatorsSpan⟩ := finite
  let freeCarrier := generators →₀ R
  let projection : freeCarrier →ₗ[R] M :=
    Finsupp.linearCombination R (Subtype.val : generators → M)
  have projectionSurjective : Function.Surjective projection := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination,
      Subtype.range_val]
    exact generatorsSpan
  obtain ⟨sectionMap, split⟩ := Module.projective_lifting_property
    projection (LinearMap.id : M →ₗ[R] M) projectionSurjective
  letI : Module.Projective R (⋀[R]^degree freeCarrier) := inferInstance
  apply Module.Projective.of_split
    (exteriorPower.map degree sectionMap)
    (exteriorPower.map degree projection)
  rw [← exteriorPower.map_comp, split, exteriorPower.map_id]

/-- Exterior powers of finite modules remain finite. -/
theorem finiteProjective_exteriorPower_finite
    (finite : Module.Finite R M) (degree : ℕ) :
    Module.Finite R (⋀[R]^degree M) := by
  letI : Module.Finite R M := finite
  infer_instance

end
end SourceGeneratedScalarProjectiveExterior
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
