import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Integral.Localization.LivingLawRootGeneratedCharacterOrbitIntegralFaceKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Integral.Localization.LivingLawRootGeneratedFaithfulIntegralPrimeResidualNaturalityKernel

/-!
# Naturality of source-generated character orbits

A complex-linear source morphism sends every two-sided orbit point to the
corresponding orbit point of the mapped vector.  It therefore induces the
integral-face map and, functorially, every prime residual map.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedCharacterOrbitIntegralFace

open SourceGeneratedFaithfulIntegralFace

noncomputable section

universe h k m

variable {H : Type h} {K : Type k} {M : Type m}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]
variable [NormedAddCommGroup K] [NormedSpace ℂ K]
variable [NormedAddCommGroup M] [NormedSpace ℂ M]

@[simp] theorem map_orbitPoint
    (map : H →ₗ[ℂ] K) (scalar : ℂˣ) (vector : H) (exponent : ℤ) :
    map (orbitPoint scalar vector exponent) =
      orbitPoint scalar (map vector) exponent := by
  simp [orbitPoint]

theorem map_mem_characterOrbit
    (map : H →ₗ[ℂ] K) (scalar : ℂˣ) (vector : H)
    {value : H} (membership : value ∈ characterOrbit scalar vector) :
    map value ∈ characterOrbit scalar (map vector) := by
  refine AddSubgroup.closure_induction
    (p := fun current _ =>
      map current ∈ characterOrbit scalar (map vector))
    ?_ ?_ ?_ ?_ membership
  · intro current current_mem
    rcases current_mem with ⟨exponent, rfl⟩
    simpa using orbitPoint_mem scalar (map vector) exponent
  · simp
  · intro left right _ _ left_mem right_mem
    simpa only [map_add] using
      (characterOrbit scalar (map vector)).add_mem left_mem right_mem
  · intro current _ current_mem
    simpa only [map_neg] using
      (characterOrbit scalar (map vector)).neg_mem current_mem

def orbitMap (map : H →ₗ[ℂ] K) (scalar : ℂˣ) (vector : H) :
    characterOrbit scalar vector →ₗ[ℤ]
      characterOrbit scalar (map vector) where
  toFun value := ⟨map value.1, map_mem_characterOrbit map scalar vector value.2⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp] theorem orbitMap_realization
    (map : H →ₗ[ℂ] K) (scalar : ℂˣ) (vector : H) (value) :
    orbitRealization scalar (map vector) (orbitMap map scalar vector value) =
      map (orbitRealization scalar vector value) :=
  rfl

theorem orbitMap_id (scalar : ℂˣ) (vector : H) :
    orbitMap (LinearMap.id : H →ₗ[ℂ] H) scalar vector = LinearMap.id := by
  ext value
  rfl

theorem orbitMap_comp
    (second : K →ₗ[ℂ] M) (first : H →ₗ[ℂ] K)
    (scalar : ℂˣ) (vector : H) :
    orbitMap (second.comp first) scalar vector =
      (orbitMap second scalar (first vector)).comp
        (orbitMap first scalar vector) := by
  ext value
  rfl

theorem primeResidual_orbitMap_class
    (map : H →ₗ[ℂ] K) (scalar : ℂˣ) (vector : H)
    (prime : Nat.Primes) (value : characterOrbit scalar vector) :
    residualMap prime (orbitMap map scalar vector)
        (residualClass prime value) =
      residualClass prime (orbitMap map scalar vector value) :=
  residualMap_class _ _ _

end
end SourceGeneratedCharacterOrbitIntegralFace
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
