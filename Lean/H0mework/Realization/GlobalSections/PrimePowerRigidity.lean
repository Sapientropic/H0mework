import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Prime-power rigidity of finitely generated additive groups

An element of a finitely generated abelian group that is divisible by every
positive power of every rational prime is zero.  This is the generic final
rigidity calculation used after a domain has generated its actual
prime-power division history.  It does not request a finite enumeration or
a caller-supplied quotient model.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace FinitelyGeneratedPrimePowerRigidity

/-- The intersection of all positive prime-power multiplication ranges in a
finitely generated abelian group is trivial. -/
theorem eq_zero_of_prime_power_divisible
    {G : Type*} [AddCommGroup G] (finiteGenerated : AddGroup.FG G)
    (element : G)
    (divisible : ∀ (prime : Nat.Primes) (exponent : Nat),
      0 < exponent →
        ∃ root : G, (prime : Nat) ^ exponent • root = element) :
    element = 0 := by
  let _ : AddGroup.FG G := finiteGenerated
  obtain ⟨rank, index, finiteIndex, prime, prime_isPrime, exponent,
      ⟨decomposition⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  apply decomposition.injective
  rw [map_zero]
  apply Prod.ext
  · apply Finsupp.ext
    intro coordinate
    let value : ℤ := (decomposition element).1 coordinate
    by_contra value_ne
    have value_abs_pos : 0 < value.natAbs := Int.natAbs_pos.mpr value_ne
    let two : Nat.Primes := ⟨2, Nat.prime_two⟩
    obtain ⟨root, root_eq⟩ := divisible two value.natAbs value_abs_pos
    have mapped :
        2 ^ value.natAbs • decomposition root = decomposition element := by
      simpa only [map_nsmul] using congrArg decomposition root_eq
    have coordinate_eq := congrArg (fun current => current.1 coordinate) mapped
    have value_dvd : ((2 ^ value.natAbs : Nat) : ℤ) ∣ value := by
      refine ⟨(decomposition root).1 coordinate, ?_⟩
      simpa only [value, Prod.smul_fst, Finsupp.nsmul_apply,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using coordinate_eq.symm
    have too_large := Int.natAbs_le_of_dvd_ne_zero value_dvd value_ne
    have too_large' : 2 ^ value.natAbs ≤ value.natAbs := by
      simpa only [Int.natAbs_natCast] using too_large
    exact (not_le_of_gt value.natAbs.lt_two_pow_self) too_large'
  · apply DFinsupp.ext
    intro coordinate
    by_cases exponent_zero : exponent coordinate = 0
    · have subsingleton :
          Subsingleton (ZMod (prime coordinate ^ exponent coordinate)) := by
        rw [exponent_zero, pow_zero]
        infer_instance
      exact @Subsingleton.elim _ subsingleton _ _
    · have exponent_pos : 0 < exponent coordinate :=
        Nat.pos_of_ne_zero exponent_zero
      let currentPrime : Nat.Primes :=
        ⟨prime coordinate, prime_isPrime coordinate⟩
      obtain ⟨root, root_eq⟩ :=
        divisible currentPrime (exponent coordinate) exponent_pos
      have mapped :
          prime coordinate ^ exponent coordinate • decomposition root =
            decomposition element := by
        simpa only [map_nsmul] using congrArg decomposition root_eq
      have coordinate_eq :=
        congrArg (fun current => current.2 coordinate) mapped
      calc
        (decomposition element).2 coordinate =
            prime coordinate ^ exponent coordinate •
              (decomposition root).2 coordinate := coordinate_eq.symm
        _ = 0 := ZModModule.char_nsmul_eq_zero _ _

end FinitelyGeneratedPrimePowerRigidity
end SaturationMonoid
