import H0mework.Arithmetic.PrimeShadow.P306
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic

/-!
# Proposition 307: nondegenerate sigma-atomic support is prime support

Proposition 306 defined the prime-generated sigma-atomic support and showed the
honest boundary: untagged rates need an injective/nonperiodic iteration bridge.

This file closes that boundary on the real salience-shaped carrier.  More
generally, in any linear ordered field, a base rate in the open interval
`0 < σ < 1` has keep-rate `0 < 1 - σ < 1`; powers of that keep-rate are
injective in the exponent.  Therefore untagged effective rates no longer
collapse.

It also separates the two operations:

* serial `satOr` composition corresponds to addition of iteration counts;
* prime atomicity belongs to the multiplicative, iteration-of-iteration
  structure on counts.

So `σ`-atomicity is formalized as multiplicative indecomposability of the
iteration exponent, then transported across the nondegenerate `σ` bridge.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Multiplicative atomicity on iteration counts -/

/-- A natural-number exponent is multiplicatively atomic when it is nontrivial
and has no nontrivial multiplicative factorization.  This is the arithmetic
notion that corresponds to prime numbers. -/
def MultiplicativelyAtomicExponent (n : ℕ) : Prop :=
  1 < n ∧ ∀ a b : ℕ, n = a * b → a = 1 ∨ b = 1

/-- THEOREM 1: multiplicative atomicity of iteration exponents is exactly
ordinary primality. -/
theorem multiplicativelyAtomicExponent_iff_prime
    (n : ℕ) :
    MultiplicativelyAtomicExponent n ↔ Nat.Prime n := by
  constructor
  · intro h
    rw [Nat.prime_def]
    constructor
    · exact h.1
    · intro m hm
      rcases hm with ⟨b, hb⟩
      rcases h.2 m b hb with hm1 | hb1
      · exact Or.inl hm1
      · right
        rw [hb1, mul_one] at hb
        exact hb.symm
  · intro hp
    constructor
    · exact hp.one_lt
    · intro a b h
      have hdvd : a ∣ n := ⟨b, h⟩
      rcases hp.eq_one_or_self_of_dvd a hdvd with ha | ha
      · exact Or.inl ha
      · right
        have h' : n = n * b := by
          simpa [ha] using h
        have hn0 : n ≠ 0 := by
          exact Nat.ne_of_gt (lt_trans Nat.zero_lt_one hp.one_lt)
        have hmul : n * 1 = n * b := by
          simpa using h'
        exact (mul_left_cancel₀ hn0 hmul).symm

/-- Sigma-atomic support defined by multiplicative indecomposability of the
iteration exponent, rather than by naming `Nat.Prime` directly. -/
def SigmaFactorAtomicRateSupport
    (σ : K) (hσ : σ ≠ 1) : Type _ :=
  { r : NonAbsorbingRate (α := K) //
      ∃ n : ℕ,
        MultiplicativelyAtomicExponent n ∧
          r = iteratedNonAbsorbingRate σ hσ n }

/-- Multiplicative sigma-atomic support is the same support as the
prime-generated support from Proposition 306. -/
def sigmaFactorAtomicRateSupportEquivPrimeSupport
    (σ : K) (hσ : σ ≠ 1) :
    SigmaFactorAtomicRateSupport σ hσ ≃
      SigmaAtomicRateSupport σ hσ where
  toFun r :=
    ⟨r.1, by
      rcases r.2 with ⟨n, hn, hr⟩
      exact ⟨n, (multiplicativelyAtomicExponent_iff_prime n).mp hn, hr⟩⟩
  invFun r :=
    ⟨r.1, by
      rcases r.2 with ⟨p, hp, hr⟩
      exact ⟨p, (multiplicativelyAtomicExponent_iff_prime p).mpr hp, hr⟩⟩
  left_inv := by
    intro r
    apply Subtype.ext
    rfl
  right_inv := by
    intro r
    apply Subtype.ext
    rfl

/-! ## The open salience interval excludes collapse -/

/-- THEOREM 2: for `0 < σ < 1`, effective `σ`-rates are injective in the
iteration exponent.  This turns the earlier nonperiodicity assumption into a
theorem on the framework's intended carrier. -/
theorem iteratedNonAbsorbingRate_injective_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Function.Injective
      (fun n : ℕ =>
        iteratedNonAbsorbingRate σ (ne_of_lt hσ1) n) := by
  intro n m h
  have hval : iteratedRate σ n = iteratedRate σ m := by
    have hv := congrArg Subtype.val h
    simpa [iteratedNonAbsorbingRate] using hv
  have hpows : (1 - σ) ^ n = (1 - σ) ^ m := by
    calc
      (1 - σ) ^ n = 1 - iteratedRate σ n := (keep_iteratedRate σ n).symm
      _ = 1 - iteratedRate σ m := by rw [hval]
      _ = (1 - σ) ^ m := keep_iteratedRate σ m
  have hkeep_pos : 0 < 1 - σ := sub_pos.mpr hσ1
  have hkeep_ne_one : (1 - σ) ≠ 1 := by nlinarith
  have hz :
      (1 - σ) ^ (n : ℤ) = (1 - σ) ^ (m : ℤ) := by
    simpa using hpows
  have hcast : (n : ℤ) = (m : ℤ) :=
    zpow_right_injective₀ hkeep_pos hkeep_ne_one hz
  exact Int.ofNat.inj hcast

/-- THEOREM 3: on the nontrivial open interval `0 < σ < 1`, the untagged
prime-generated sigma-atomic support is canonically equivalent to the set of
prime natural numbers. -/
def sigmaAtomicRateSupportEquivPrimes_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaAtomicRateSupport σ (ne_of_lt hσ1) ≃ PrimeExponent :=
  sigmaAtomicRateSupportEquivPrimes σ (ne_of_lt hσ1)
    (iteratedNonAbsorbingRate_injective_of_mem_Ioo hσ0 hσ1)

/-- THEOREM 4: the factorization-defined sigma-atomic support is equivalent to
prime numbers on `0 < σ < 1`. -/
def sigmaFactorAtomicRateSupportEquivPrimes_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaFactorAtomicRateSupport σ (ne_of_lt hσ1) ≃ PrimeExponent :=
  (sigmaFactorAtomicRateSupportEquivPrimeSupport σ (ne_of_lt hσ1)).trans
    (sigmaAtomicRateSupportEquivPrimes_of_mem_Ioo hσ0 hσ1)

/-- THEOREM 5: serial noisy-OR still reads as addition of iteration counts.  It
is deliberately not the operation whose atoms are primes. -/
theorem sigmaAtomic_serial_satOr_is_addition
    (σ : K) (n m : ℕ) :
    iteratedRate σ (n + m) =
      satOrField (iteratedRate σ n) (iteratedRate σ m) :=
  iteratedRate_add σ n m

/-- THEOREM 6: prime atomicity is attached to iteration-of-iteration, i.e. to
multiplication of iteration counts. -/
theorem sigmaAtomic_iteration_of_iteration_is_multiplication
    (σ : K) (n m : ℕ) :
    iteratedRate (iteratedRate σ n) m =
      iteratedRate σ (n * m) :=
  iteratedRate_iteratedRate σ n m

/-- A compact certificate for the nondegenerate sigma-atomic prime bridge. -/
structure NondegenerateSigmaAtomicPrimeCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  exponent_atomic_iff_prime :
    ∀ n : ℕ, MultiplicativelyAtomicExponent n ↔ Nat.Prime n
  no_collapse :
    Function.Injective
      (fun n : ℕ =>
        iteratedNonAbsorbingRate σ (ne_of_lt hσ1) n)
  prime_support_equiv :
    SigmaAtomicRateSupport σ (ne_of_lt hσ1) ≃ PrimeExponent
  factor_atomic_support_equiv :
    SigmaFactorAtomicRateSupport σ (ne_of_lt hσ1) ≃ PrimeExponent
  serial_is_addition :
    ∀ n m : ℕ,
      iteratedRate σ (n + m) =
        satOrField (iteratedRate σ n) (iteratedRate σ m)
  iteration_is_multiplication :
    ∀ n m : ℕ,
      iteratedRate (iteratedRate σ n) m =
        iteratedRate σ (n * m)

/-- THEOREM 7: the canonical certificate on the nontrivial open salience
interval. -/
def nondegenerateSigmaAtomicPrimeCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    NondegenerateSigmaAtomicPrimeCertificate σ hσ0 hσ1 where
  exponent_atomic_iff_prime := multiplicativelyAtomicExponent_iff_prime
  no_collapse := iteratedNonAbsorbingRate_injective_of_mem_Ioo hσ0 hσ1
  prime_support_equiv :=
    sigmaAtomicRateSupportEquivPrimes_of_mem_Ioo hσ0 hσ1
  factor_atomic_support_equiv :=
    sigmaFactorAtomicRateSupportEquivPrimes_of_mem_Ioo hσ0 hσ1
  serial_is_addition := sigmaAtomic_serial_satOr_is_addition σ
  iteration_is_multiplication :=
    sigmaAtomic_iteration_of_iteration_is_multiplication σ

end AffineRelaxation
end SaturationMonoid
