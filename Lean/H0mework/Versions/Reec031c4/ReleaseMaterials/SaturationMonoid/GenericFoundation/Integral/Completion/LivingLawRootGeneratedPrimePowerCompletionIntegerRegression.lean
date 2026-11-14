import H0mework.Realization.Perfectification.Integral.Completion.LivingLawRootGeneratedPrimePowerCompletionNaturalityKernel

/-!
# Integer prime-power completion regression

For every rational prime, the canonical map from `ℤ` into the generated
prime-power inverse limit is injective.  Its image of `1` is nonzero and is
not a `p`-multiple, already detected by the actual stage-zero quotient.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace PrimePowerCompletionIntegerRegression

open CategoryTheory
open SourceGeneratedPrimePowerCompletion

noncomputable section

theorem integer_eq_zero_of_primePowerDivisible
    (prime : Nat.Primes) (value : ℤ)
    (divided : ∀ stage, ∃ root : ℤ,
      (prime.1 : ℤ) ^ (stage + 1) • root = value) :
    value = 0 := by
  by_contra value_ne_zero
  let stage := value.natAbs
  obtain ⟨root, root_eq⟩ := divided stage
  have value_dvd : (prime.1 : ℤ) ^ (stage + 1) ∣ value := by
    refine ⟨root, ?_⟩
    simpa only [smul_eq_mul] using root_eq.symm
  have divisor_le := Int.natAbs_le_of_dvd_ne_zero value_dvd value_ne_zero
  have divisor_le' : prime.1 ^ (stage + 1) ≤ stage := by
    simpa only [Int.natAbs_pow, Int.natAbs_natCast, stage] using divisor_le
  have two_pow_le : 2 ^ (stage + 1) ≤ prime.1 ^ (stage + 1) :=
    Nat.pow_le_pow_left prime.property.two_le _
  have stage_lt_two_pow : stage < 2 ^ (stage + 1) := by
    apply lt_of_lt_of_le stage.lt_two_pow_self
    rw [pow_succ]
    omega
  exact (not_le_of_gt (stage_lt_two_pow.trans_le two_pow_le)) divisor_le'

theorem integer_canonicalLinearMap_injective (prime : Nat.Primes) :
    Function.Injective
      (canonicalLinearMap (L := ℤ) prime) := by
  intro left right equality
  apply sub_eq_zero.mp
  apply integer_eq_zero_of_primePowerDivisible prime (left - right)
  apply (canonicalMap_eq_zero_iff prime (left - right)).1
  change canonicalLinearMap (L := ℤ) prime (left - right) = 0
  rw [map_sub, equality, sub_self]

def completedOne (prime : Nat.Primes) :
    Completion (L := ℤ) prime :=
  canonicalLinearMap (L := ℤ) prime 1

theorem completedOne_ne_zero (prime : Nat.Primes) :
    completedOne prime ≠ 0 := by
  intro completedZero
  have sourceZero : (1 : ℤ) = 0 := by
    apply integer_canonicalLinearMap_injective prime
    simpa [completedOne] using completedZero
  exact one_ne_zero sourceZero

theorem stageZero_prime_nsmul_eq_zero
    (prime : Nat.Primes)
    (residual : StageResidual (L := ℤ) prime 0) :
    prime.1 • residual = 0 := by
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (powerRange (L := ℤ) prime 0) residual
  calc
    prime.1 • stageProjection (L := ℤ) prime 0 value =
        stageProjection (L := ℤ) prime 0 (prime.1 • value) :=
      ((stageProjection (L := ℤ) prime 0).toAddMonoidHom.map_nsmul
        prime.1 value).symm
    _ = 0 := by
      apply (stageProjection_eq_zero_iff prime 0 _).2
      refine ⟨value, ?_⟩
      simp

theorem stageZero_one_ne_zero (prime : Nat.Primes) :
    stageProjection (L := ℤ) prime 0 1 ≠ 0 := by
  intro quotientZero
  obtain ⟨divided, equality⟩ :=
    (stageProjection_eq_zero_iff prime 0 1).1 quotientZero
  have prime_dvd_one : (prime.1 : ℤ) ∣ (1 : ℤ) := by
    refine ⟨divided, ?_⟩
    simpa [smul_eq_mul] using equality.symm
  have prime_le_one :=
    Int.natAbs_le_of_dvd_ne_zero prime_dvd_one one_ne_zero
  have : prime.1 ≤ 1 := by
    simpa only [Int.natAbs_natCast, Int.natAbs_one] using prime_le_one
  exact (not_le_of_gt prime.property.two_le) this

theorem completedOne_not_primeMultiple (prime : Nat.Primes) :
    ¬ ∃ divided : Completion (L := ℤ) prime,
      prime.1 • divided = completedOne prime := by
  rintro ⟨divided, equality⟩
  have projected := congrArg
    (fun completed ↦ restriction (L := ℤ) prime 0 completed)
    equality
  have oneProjection := ConcreteCategory.congr_hom
    (canonicalMap_restriction (L := ℤ) prime 0) (1 : ℤ)
  change restriction (L := ℤ) prime 0 (completedOne prime) =
      stageProjection (L := ℤ) prime 0 1 at oneProjection
  change (restriction (L := ℤ) prime 0).hom
        (prime.1 • divided) =
      (restriction (L := ℤ) prime 0).hom (completedOne prime)
    at projected
  have projected' :
      prime.1 • restriction (L := ℤ) prime 0 divided =
        restriction (L := ℤ) prime 0 (completedOne prime) :=
    ((restriction (L := ℤ) prime 0).hom.toAddMonoidHom.map_nsmul
      prime.1 divided).symm.trans projected
  have zero_eq_oneProjection :
      0 = stageProjection (L := ℤ) prime 0 1 := by
    calc
      0 = prime.1 •
          restriction (L := ℤ) prime 0 divided :=
        (stageZero_prime_nsmul_eq_zero prime _).symm
      _ = restriction (L := ℤ) prime 0 (completedOne prime) := projected'
      _ = stageProjection (L := ℤ) prime 0 1 := oneProjection
  exact stageZero_one_ne_zero prime zero_eq_oneProjection.symm

def doubleMap : ℤ →ₗ[ℤ] ℤ :=
  (2 : ℤ) • LinearMap.id

theorem doubleMap_completion_naturality (prime : Nat.Primes) :
    canonicalMap (L := ℤ) prime ≫
        inducedCompletionMap prime doubleMap =
      ModuleCat.ofHom doubleMap ≫ canonicalMap (L := ℤ) prime :=
  canonicalMap_naturality prime doubleMap

theorem coimage_realization_is_faithful (prime : Nat.Primes) :
    Function.Injective
      (coimageFaithfulIntegralFace (L := ℤ) prime).realization :=
  (coimageFaithfulIntegralFace (L := ℤ) prime).injective

def coimageOne (prime : Nat.Primes) :
    FaithfulCoimage (L := ℤ) prime :=
  coimageProjection (L := ℤ) prime 1

theorem coimageOne_realizes_completedOne (prime : Nat.Primes) :
    (coimageFaithfulIntegralFace (L := ℤ) prime).realization
        (coimageOne prime) = completedOne prime := by
  exact LinearMap.congr_fun
    (coimageRealization_projection (L := ℤ) prime) 1

theorem coimageOne_not_primeDivisible (prime : Nat.Primes) :
    ¬ ∃ divided : FaithfulCoimage (L := ℤ) prime,
      prime.1 • divided = coimageOne prime := by
  rintro ⟨divided, equality⟩
  apply completedOne_not_primeMultiple prime
  refine ⟨(coimageFaithfulIntegralFace (L := ℤ) prime).realization divided, ?_⟩
  calc
    prime.1 •
          (coimageFaithfulIntegralFace (L := ℤ) prime).realization divided =
        (coimageFaithfulIntegralFace (L := ℤ) prime).realization
          (prime.1 • divided) :=
      ((coimageFaithfulIntegralFace (L := ℤ) prime).realization
        |>.toAddMonoidHom.map_nsmul prime.1 divided).symm
    _ = (coimageFaithfulIntegralFace (L := ℤ) prime).realization
          (coimageOne prime) := congrArg _ equality
    _ = completedOne prime := coimageOne_realizes_completedOne prime

def coimagePrimeResidualCoordinate (prime : Nat.Primes) :
    SourceGeneratedFaithfulIntegralFace.PrimeResidualCoordinate
      (L := FaithfulCoimage (L := ℤ) prime) prime where
  representative := coimageOne prime
  not_divisible := coimageOne_not_primeDivisible prime

theorem coimage_primeResidualClass_ne_zero (prime : Nat.Primes) :
    SourceGeneratedFaithfulIntegralFace.residualClass
        (L := FaithfulCoimage (L := ℤ) prime) prime (coimageOne prime) ≠ 0 :=
  (coimagePrimeResidualCoordinate prime).class_ne_zero

#print axioms integer_canonicalLinearMap_injective
#print axioms completedOne_ne_zero
#print axioms completedOne_not_primeMultiple
#print axioms canonicalMap_naturality
#print axioms settleSeparation
#print axioms coimage_universal
#print axioms inducedCompletionMap_comp
#print axioms coimageMap_comp
#print axioms coimage_realization_is_faithful
#print axioms coimage_primeResidualClass_ne_zero

end
end PrimePowerCompletionIntegerRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
