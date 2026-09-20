import Mathlib.Algebra.Module.Presentation.Finite

/-!
# Representation residual for finite-free compression

A finite-free carrier surjecting onto an additive module forces that module
to be finitely generated.  Since the countable free integral module is not
finitely generated, no generic consumer may claim finite determinant
eligibility for every complete source carrier using only a presentation or a
cofinal-limit marker.  A lawful finite-compression mouth must first consume a
source-generated finite generator envelope (or an equivalent compactness
receipt); when that envelope is unavailable, the exact outcome is a
representation/compression residual rather than a claim about the source's
intrinsic completeness.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalPerfectCompressionNoGo

noncomputable section

/-- The weakest faithful finite-free compression already forces a finite
target module, so it is a finite-determinant eligibility test rather than a
universal source theorem. -/
structure FiniteFreeSurjectiveCompressionAt
    (module : Type*) [AddCommGroup module] where
  Carrier : Type
  [carrierAddCommGroup : AddCommGroup Carrier]
  [carrierFree : Module.Free ℤ Carrier]
  [carrierFinite : Module.Finite ℤ Carrier]
  readout : Carrier →ₗ[ℤ] module
  readout_surjective : Function.Surjective readout

theorem moduleFinite_of_finiteFreeSurjectiveCompression
    {module : Type*} [AddCommGroup module]
    (compression : FiniteFreeSurjectiveCompressionAt module) :
    Module.Finite ℤ module := by
  letI : AddCommGroup compression.Carrier := compression.carrierAddCommGroup
  letI : Module.Free ℤ compression.Carrier := compression.carrierFree
  letI : Module.Finite ℤ compression.Carrier := compression.carrierFinite
  exact Module.Finite.of_surjective compression.readout
    compression.readout_surjective

theorem natFinsupp_not_moduleFinite :
    ¬ Module.Finite ℤ (ℕ →₀ ℤ) := by
  intro finite
  letI : Module.Finite ℤ (ℕ →₀ ℤ) := finite
  letI : Finite ℕ :=
    Module.Finite.finite_basis (Finsupp.basisSingleOne (R := ℤ))
  exact not_finite ℕ

theorem natFinsupp_no_finiteFreeSurjectiveCompression :
    ¬ Nonempty (FiniteFreeSurjectiveCompressionAt (ℕ →₀ ℤ)) := by
  rintro ⟨compression⟩
  exact natFinsupp_not_moduleFinite
    (moduleFinite_of_finiteFreeSurjectiveCompression compression)

/-- No uniform finite-free surjective compression exists for arbitrary
additive carriers.  This is the generic negative branch: it records an exact
representation residual, not a claim about arbitrary source carriers'
intrinsic completeness. -/
theorem no_uniform_finiteFreeSurjectiveCompression :
    ¬ (∀ (module : Type) [AddCommGroup module],
      Nonempty (FiniteFreeSurjectiveCompressionAt module)) := by
  intro uniform
  let compression := (uniform (ℕ →₀ ℤ)).some
  exact natFinsupp_no_finiteFreeSurjectiveCompression ⟨compression⟩

end

end CofinalPerfectCompressionNoGo
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
