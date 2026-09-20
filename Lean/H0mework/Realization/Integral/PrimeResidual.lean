import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import H0mework.Realization.Integral.FaithfulAction

/-!
# Faithful integral prime residual

For a source-owned integral face `L → Ambient`, multiplication by a rational
prime is injective because the ambient complex carrier is torsion-free.  It is
then either an automorphism of `L`, or its cokernel `L / pL` contains an actual
nonzero coordinate.  This is the generic non-`p`-inverting disposition.

The final no-go is exact: if `L` itself retains a complex-module structure,
then multiplication by every prime is surjective.  Therefore restriction of
scalars on a complex/Hilbert carrier cannot be the required integral face.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFaithfulIntegralFace

noncomputable section

universe l a

variable {L : Type l} [AddCommGroup L]

def primeMultiplication (prime : Nat.Primes) : L →ₗ[ℤ] L :=
  (prime.1 : ℤ) • LinearMap.id

@[simp] theorem primeMultiplication_apply
    (prime : Nat.Primes) (value : L) :
    primeMultiplication (L := L) prime value = prime.1 • value := by
  simp [primeMultiplication, Nat.cast_smul_eq_nsmul]

/-- The exact coordinate lost by a finite prime-local observation. -/
abbrev PrimeResidual (prime : Nat.Primes) :=
  L ⧸ LinearMap.range (primeMultiplication (L := L) prime)

def residualClass (prime : Nat.Primes) :
    L →ₗ[ℤ] PrimeResidual (L := L) prime :=
  Submodule.mkQ _

theorem residualClass_eq_zero_iff
    (prime : Nat.Primes) (value : L) :
    residualClass (L := L) prime value = 0 ↔
      ∃ divided : L, prime.1 • divided = value := by
  rw [residualClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨divided, equality⟩
    refine ⟨divided, ?_⟩
    simpa only [primeMultiplication_apply] using equality
  · rintro ⟨divided, equality⟩
    refine ⟨divided, ?_⟩
    rw [primeMultiplication_apply, equality]

structure PrimeResidualCoordinate (prime : Nat.Primes) where
  representative : L
  not_divisible :
    ¬ ∃ divided : L, prime.1 • divided = representative

theorem PrimeResidualCoordinate.class_ne_zero
    {prime : Nat.Primes}
    (coordinate : PrimeResidualCoordinate (L := L) prime) :
    residualClass (L := L) prime coordinate.representative ≠ 0 := by
  rw [ne_eq, residualClass_eq_zero_iff]
  exact coordinate.not_divisible

variable {Ambient : Type a} [AddCommGroup Ambient] [Module ℂ Ambient]

/-- Complex scalar multiplication viewed only as an integral-linear ambient
action. -/
def complexScalarAction (scalar : ℂ) : Ambient →ₗ[ℤ] Ambient :=
  ((scalar • LinearMap.id) : Ambient →ₗ[ℂ] Ambient).restrictScalars ℤ

@[simp] theorem complexScalarAction_apply (scalar : ℂ) (value : Ambient) :
    complexScalarAction (Ambient := Ambient) scalar value = scalar • value := by
  simp [complexScalarAction]

theorem primeMultiplication_injective
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (prime : Nat.Primes) :
    Function.Injective (primeMultiplication (L := L) prime) := by
  intro left right equality
  apply face.injective
  have mapped := congrArg face.realization equality
  simp only [primeMultiplication_apply, map_nsmul] at mapped
  have multipliedDifference :
      prime.1 • (face.realization left - face.realization right) = 0 := by
    rw [nsmul_sub, mapped, sub_self]
  have scalarMultiplied :
      (prime.1 : ℂ) • (face.realization left - face.realization right) = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using multipliedDifference
  have coefficientNonzero : (prime.1 : ℂ) ≠ 0 := by
    exact_mod_cast prime.property.ne_zero
  have differenceZero : face.realization left - face.realization right = 0 :=
    (smul_eq_zero.mp scalarMultiplied).resolve_left coefficientNonzero
  exact sub_eq_zero.mp differenceZero

inductive PrimeDisposition
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (prime : Nat.Primes) : Type (max l a) where
  | localized
      (equivalence : L ≃ₗ[ℤ] L)
      (equivalence_eq_primeMultiplication :
        equivalence.toLinearMap = primeMultiplication (L := L) prime)
  | representationResidual
      (coordinate : PrimeResidualCoordinate (L := L) prime)

noncomputable def settlePrime
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (prime : Nat.Primes) : PrimeDisposition face prime := by
  classical
  by_cases surjective : Function.Surjective
      (primeMultiplication (L := L) prime)
  · exact .localized
      (LinearEquiv.ofBijective (primeMultiplication (L := L) prime)
        ⟨primeMultiplication_injective face prime, surjective⟩)
      rfl
  · have missing : ∃ target : L,
        ¬ ∃ source : L,
          primeMultiplication (L := L) prime source = target := by
      simpa [Function.Surjective] using surjective
    exact .representationResidual ⟨missing.choose, by
      simpa only [primeMultiplication_apply] using missing.choose_spec⟩

theorem primeDisposition_total
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (prime : Nat.Primes) : Nonempty (PrimeDisposition face prime) :=
  ⟨settlePrime face prime⟩

/-! ## Exact no-go for scalar restriction -/

theorem complexModule_primeMultiplication_surjective
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (prime : Nat.Primes) :
    Function.Surjective (primeMultiplication (L := V) prime) := by
  intro value
  let divided : V := ((prime.1 : ℂ)⁻¹) • value
  refine ⟨divided, ?_⟩
  rw [primeMultiplication_apply, ← Nat.cast_smul_eq_nsmul ℂ]
  change (prime.1 : ℂ) • (((prime.1 : ℂ)⁻¹) • value) = value
  rw [smul_smul, mul_inv_cancel₀]
  · exact one_smul ℂ value
  · exact_mod_cast prime.property.ne_zero

theorem complexModule_residualClass_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (prime : Nat.Primes) (value : V) :
    residualClass (L := V) prime value = 0 := by
  apply (residualClass_eq_zero_iff prime value).2
  simpa only [primeMultiplication_apply] using
    complexModule_primeMultiplication_surjective prime value

theorem complexModule_no_primeResidualCoordinate
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (prime : Nat.Primes) :
    ¬ Nonempty (PrimeResidualCoordinate (L := V) prime) := by
  rintro ⟨coordinate⟩
  exact coordinate.class_ne_zero
    (complexModule_residualClass_eq_zero prime coordinate.representative)

end
end SourceGeneratedFaithfulIntegralFace
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
