import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import H0mework.Realization.Integral.PrimeResidual

/-!
# Integral character group ring

Every group and complex multiplicative character generate the integral group
ring `ℤ[G]`.  Its canonical basis carries left and right translations, while
the character evaluates every basis vector without requiring finiteness,
projectivity, perfectness, nondegeneracy, or determinant data.  The basis
vector at the identity also gives an explicit residual for every rational
prime.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedIntegralCharacterGroupRing

open SourceGeneratedFaithfulIntegralFace

noncomputable section

universe u v w

variable {G : Type u} [Group G]
variable {H : Type v} [Group H]

abbrev Carrier (G : Type u) [Group G] := MonoidAlgebra ℤ G

/-- Canonical integral basis vector `δ_g`. -/
def delta (element : G) : Carrier G :=
  MonoidAlgebra.single element 1

/-- The canonical free basis of the integral group ring. -/
def canonicalBasis : Module.Basis G ℤ (Carrier G) :=
  Finsupp.basisSingleOne.map
    (MonoidAlgebra.coeffLinearEquiv ℤ).symm

@[simp] theorem canonicalBasis_apply (element : G) :
    canonicalBasis element = delta element := by
  simp [canonicalBasis, delta]

/-- The basis element as an actual unit of the group ring. -/
def deltaUnit (element : G) : (Carrier G)ˣ :=
  Units.map (MonoidAlgebra.of ℤ G) (toUnits element)

@[simp] theorem deltaUnit_coe (element : G) :
    (deltaUnit element : Carrier G) = delta element := by
  simp [deltaUnit, delta]

@[simp] theorem delta_mul_delta (left right : G) :
    delta left * delta right = delta (left * right) := by
  simp [delta]

/-- Integral-linear left translation by a group element. -/
def leftTranslation (element : G) : Carrier G ≃ₗ[ℤ] Carrier G :=
  (deltaUnit element).mulLeftLinearEquiv ℤ (Carrier G)

/-- Integral-linear right translation by a group element. -/
def rightTranslation (element : G) : Carrier G ≃ₗ[ℤ] Carrier G :=
  (deltaUnit element).mulRightLinearEquiv ℤ

@[simp] theorem leftTranslation_delta (left right : G) :
    leftTranslation left (delta right) = delta (left * right) := by
  simp [leftTranslation, deltaUnit_coe, delta_mul_delta]

@[simp] theorem rightTranslation_delta (left right : G) :
    rightTranslation right (delta left) = delta (left * right) := by
  simp [rightTranslation, deltaUnit_coe, delta_mul_delta]

@[simp] theorem leftTranslation_one :
    leftTranslation (1 : G) = LinearEquiv.refl ℤ (Carrier G) := by
  ext value
  simp [leftTranslation, deltaUnit_coe, delta]

@[simp] theorem rightTranslation_one :
    rightTranslation (1 : G) = LinearEquiv.refl ℤ (Carrier G) := by
  ext value
  simp [rightTranslation, deltaUnit_coe, delta]

theorem leftTranslation_comp (first second : G) :
    (leftTranslation first).trans (leftTranslation second) =
      leftTranslation (second * first) := by
  apply LinearEquiv.ext
  intro value
  change delta second * (delta first * value) =
    delta (second * first) * value
  rw [← mul_assoc, delta_mul_delta]

theorem rightTranslation_comp (first second : G) :
    (rightTranslation first).trans (rightTranslation second) =
      rightTranslation (first * second) := by
  apply LinearEquiv.ext
  intro value
  change (value * delta first) * delta second =
    value * delta (first * second)
  rw [mul_assoc, delta_mul_delta]

/-- Ring-valued extension of the source character. -/
def characterEvaluationRingHom (character : G →* ℂ) :
    Carrier G →+* ℂ :=
  MonoidAlgebra.liftNCRingHom (Int.castRingHom ℂ) character
    (fun _ _ ↦ Commute.all _ _)

/-- Integral-linear character evaluation. -/
def characterEvaluation (character : G →* ℂ) :
    Carrier G →ₗ[ℤ] ℂ :=
  (characterEvaluationRingHom character).toAddMonoidHom.toIntLinearMap

@[simp] theorem characterEvaluation_delta
    (character : G →* ℂ) (element : G) :
    characterEvaluation character (delta element) = character element := by
  simp [characterEvaluation, characterEvaluationRingHom, delta]

theorem characterEvaluation_left_covariance
    (character : G →* ℂ) (element : G) (value : Carrier G) :
    characterEvaluation character (leftTranslation element value) =
      character element * characterEvaluation character value := by
  change characterEvaluationRingHom character
      ((deltaUnit element : Carrier G) * value) = _
  rw [map_mul, deltaUnit_coe]
  change characterEvaluationRingHom character (delta element) *
      characterEvaluationRingHom character value =
    character element * characterEvaluationRingHom character value
  rw [show characterEvaluationRingHom character (delta element) =
      character element by
    exact characterEvaluation_delta character element]

theorem characterEvaluation_right_covariance
    (character : G →* ℂ) (element : G) (value : Carrier G) :
    characterEvaluation character (rightTranslation element value) =
      characterEvaluation character value * character element := by
  change characterEvaluationRingHom character
      (value * (deltaUnit element : Carrier G)) = _
  rw [map_mul, deltaUnit_coe]
  change characterEvaluationRingHom character value *
      characterEvaluationRingHom character (delta element) =
    characterEvaluationRingHom character value * character element
  rw [show characterEvaluationRingHom character (delta element) =
      character element by
    exact characterEvaluation_delta character element]

variable {V : Type w} [AddCommGroup V]

/-- A source representation and one source vector generate the unique
integral-linear orbit realization. -/
def orbitRealization
    (representation : G →* Module.End ℤ V) (vector : V) :
    Carrier G →ₗ[ℤ] V :=
  canonicalBasis.constr ℤ (fun element ↦ representation element vector)

@[simp] theorem orbitRealization_delta
    (representation : G →* Module.End ℤ V) (vector : V) (element : G) :
    orbitRealization representation vector (delta element) =
      representation element vector := by
  rw [← canonicalBasis_apply element]
  exact canonicalBasis.constr_basis ℤ _ element

/-- Left translation of the group ring is transported to the source
representation action. -/
theorem orbitRealization_left_covariance
    (representation : G →* Module.End ℤ V) (vector : V) (element : G) :
    (orbitRealization representation vector).comp
        (leftTranslation element).toLinearMap =
      (representation element).comp
        (orbitRealization representation vector) := by
  apply MonoidAlgebra.lhom_ext'
  intro basisElement
  apply LinearMap.ext
  intro coefficient
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
  rw [show MonoidAlgebra.single basisElement coefficient =
        coefficient • delta basisElement by simp [delta]]
  simp only [map_smul, orbitRealization_delta]
  congr 1
  change orbitRealization representation vector
      (leftTranslation element (delta basisElement)) = _
  rw [leftTranslation_delta, orbitRealization_delta, map_mul]
  rfl

/-- Functorial map of integral group rings induced by a source group
morphism. -/
def map (morphism : G →* H) : Carrier G →ₗ[ℤ] Carrier H :=
  (MonoidAlgebra.mapDomainAlgHom ℤ ℤ morphism).toLinearMap

@[simp] theorem map_delta (morphism : G →* H) (element : G) :
    map morphism (delta element) = delta (morphism element) := by
  simp [map, delta]

/-- Character evaluation is natural under source group morphisms. -/
theorem characterEvaluation_naturality
    (morphism : G →* H) (character : H →* ℂ) (value : Carrier G) :
    characterEvaluation character (map morphism value) =
      characterEvaluation (character.comp morphism) value := by
  let left : Carrier G →ₗ[ℤ] ℂ :=
    (characterEvaluation character).comp (map morphism)
  let right : Carrier G →ₗ[ℤ] ℂ :=
    characterEvaluation (character.comp morphism)
  have mapsEqual : left = right := by
    apply MonoidAlgebra.lhom_ext'
    intro element
    apply LinearMap.ext
    intro coefficient
    simp [left, right, map, characterEvaluation,
      characterEvaluationRingHom, MonoidAlgebra.lsingle_apply]
  exact LinearMap.congr_fun mapsEqual value

/-- The identity basis vector is not divisible by any rational prime. -/
theorem delta_one_not_prime_divisible (prime : Nat.Primes) :
    ¬ ∃ divided : Carrier G, prime.1 • divided = delta (1 : G) := by
  rintro ⟨divided, equality⟩
  have atIdentity := congrArg
    (fun value : Carrier G => value.coeff (1 : G)) equality
  simp only [MonoidAlgebra.coeff_smul_apply] at atIdentity
  simp [delta] at atIdentity
  change (prime.1 : ℤ) * divided.coeff 1 = 1 at atIdentity
  have dividesOne : (prime.1 : ℤ) ∣ 1 :=
    ⟨divided.coeff 1, atIdentity.symm⟩
  have unit : IsUnit (prime.1 : ℤ) :=
    (isUnit_iff_dvd_one).2 dividesOne
  rcases Int.isUnit_iff.mp unit with primeOne | primeNegOne
  · have primeNatOne : prime.1 = 1 := by exact_mod_cast primeOne
    exact prime.property.ne_one primeNatOne
  · have primePositive : (0 : ℤ) < prime.1 := by
      exact_mod_cast prime.property.pos
    omega

/-- Explicit generic prime residual generated by the identity basis. -/
def deltaOnePrimeResidualCoordinate (prime : Nat.Primes) :
    PrimeResidualCoordinate (L := Carrier G) prime where
  representative := delta (1 : G)
  not_divisible := delta_one_not_prime_divisible prime

theorem deltaOne_primeResidualClass_ne_zero (prime : Nat.Primes) :
    residualClass (L := Carrier G) prime (delta (1 : G)) ≠ 0 :=
  (deltaOnePrimeResidualCoordinate (G := G) prime).class_ne_zero

end
end SourceGeneratedIntegralCharacterGroupRing
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
