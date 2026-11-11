import H0mework.Realization.Integral.PrimeResidual

/-!
# Naturality of faithful integral prime residuals

Every integral-linear dependent-face morphism commutes with prime
multiplication and therefore descends canonically to `L / pL`.  Identity and
composition hold on the nose; no inverse or finite chart is required.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFaithfulIntegralFace

noncomputable section

universe l m n

variable {L : Type l} {M : Type m} {N : Type n}
variable [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]

theorem primeRange_maps
    (prime : Nat.Primes) (map : L →ₗ[ℤ] M) :
    LinearMap.range (primeMultiplication (L := L) prime) ≤
      (LinearMap.range (primeMultiplication (L := M) prime)).comap map := by
  rintro _ ⟨value, rfl⟩
  refine ⟨map value, ?_⟩
  simp

def residualMap (prime : Nat.Primes) (map : L →ₗ[ℤ] M) :
    PrimeResidual (L := L) prime →ₗ[ℤ] PrimeResidual (L := M) prime :=
  Submodule.mapQ
    (LinearMap.range (primeMultiplication (L := L) prime))
    (LinearMap.range (primeMultiplication (L := M) prime))
    map (primeRange_maps prime map)

@[simp] theorem residualMap_class
    (prime : Nat.Primes) (map : L →ₗ[ℤ] M) (value : L) :
    residualMap prime map (residualClass (L := L) prime value) =
      residualClass (L := M) prime (map value) :=
  rfl

theorem residualMap_id (prime : Nat.Primes) :
    residualMap prime (LinearMap.id : L →ₗ[ℤ] L) = LinearMap.id := by
  apply LinearMap.ext
  intro residual
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective
      (LinearMap.range (primeMultiplication (L := L) prime)) residual
  rfl

theorem residualMap_comp
    (prime : Nat.Primes) (second : M →ₗ[ℤ] N) (first : L →ₗ[ℤ] M) :
    residualMap prime (second.comp first) =
      (residualMap prime second).comp (residualMap prime first) := by
  apply LinearMap.ext
  intro residual
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective
      (LinearMap.range (primeMultiplication (L := L) prime)) residual
  rfl

end
end SourceGeneratedFaithfulIntegralFace
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
