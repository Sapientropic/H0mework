import SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Readback

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits SourceGeneratedPrimePowerCompletion

variable {L : Type u} [AddCommGroup L]

theorem factorial_to_primes_from_primes (value : AllPrimeCompletion L) :
    factorialToPrimes (factorialFromPrimes value) = value := by
  funext prime
  apply Concrete.limit_ext (tower (L := L) prime)
  rintro ⟨j⟩
  let address := primePowerAddress prime j
  let modulus := factorialModulus address
  let nonzero := factorial_modulus_ne_zero address
  let written := prime_power_address_dvd prime j
  let primes := modulusPrimes modulus
  let depths := modulusDepth modulus
  let source := finitePrimeLift primes depths value
  have exponent : j+1 ≤ modulus.factorization prime.val :=
    (prime.property.pow_dvd_iff_le_factorization nonzero).1 written
  have positive : 0 < modulus.factorization prime.val := (Nat.succ_pos j).trans_le exponent
  let coordinate : primes := ⟨prime, modulus_prime_mem.2 (Finsupp.mem_support_iff.mpr (ne_of_gt positive))⟩
  have within : j ≤ depths coordinate := by
    have valuation := modulus_depth_succ modulus coordinate
    change j+1 ≤ modulus.factorization coordinate.val.val at exponent
    omega
  have sourceRead := (modulus_projection_eq_iff modulus nonzero source value).2
    (finite_prime_lift_projection primes depths value)
  let read := factorialStageToPrime (L := L) prime j address written
  change (restriction prime j).hom (factorialToPrimes (factorialFromPrimes value) prime) =
    (restriction prime j).hom (value prime)
  exact (factorial_to_primes_restriction prime j address written (factorialFromPrimes value)).trans
    ((congrArg read (factorial_from_primes_restriction address value)).trans
      ((congrArg read sourceRead.symm).trans
        ((factorial_stage_to_prime_projection prime j address written source).trans
          (finite_prime_lift_lower primes depths value coordinate j within))))

private theorem factorial_to_then_from_primes (value : FactorialCompletion (L := L)) :
    factorialFromPrimes (factorialToPrimes value) = value := by
  apply Concrete.limit_ext (factorialTower (L := L))
  rintro ⟨address⟩
  let modulus := factorialModulus address
  let nonzero := factorial_modulus_ne_zero address
  let residue := (factorialRestriction (L := L) address).hom value
  let family := factorialToPrimes value
  obtain ⟨source, represents⟩ := (modulusRange (L := L) modulus).mkQ_surjective residue
  have sourceRead : modulusProjection modulus source = modulusRead modulus nonzero family := by
    apply (modulus_projection_eq_iff modulus nonzero source family).2
    funext p
    let level := modulusDepth modulus p
    have written : p.val.val^(level+1) ∣ modulus :=
      (p.val.property.pow_dvd_iff_le_factorization nonzero).2 (modulus_depth_succ modulus p).le
    let read := factorialStageToPrime (L := L) p.val level address written
    exact (factorial_stage_to_prime_projection p.val level address written source).symm.trans
      ((congrArg read represents).trans (factorial_to_primes_restriction p.val level address written value).symm)
  change (factorialRestriction (L := L) address).hom (factorialFromPrimes family) = residue
  exact (factorial_from_primes_restriction address family).trans (sourceRead.symm.trans represents)

/-- A single factorial inverse limit realizes the full original product of coherent prime-power towers. -/
def factorialCompletionEquiv : AllPrimeCompletion L ≃ₗ[ℤ] FactorialCompletion (L := L) :=
  LinearEquiv.ofLinearMap factorialFromPrimes factorialToPrimes
    (LinearMap.ext factorial_to_then_from_primes) (LinearMap.ext factorial_to_primes_from_primes)

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
