import H0mework.Arithmetic.ZetaReadout.P325

/-!
# Proposition 326: relative factorization length in headroom space

P323 ruled out the false shortcut that the self-dual point `sigma = 1/2`
collapses addition and multiplication.  P325 then forced the number-theoretic
bridge onto an arithmetic-admissible domain.

This file records the corrected Goldbach/FTA viewpoint in the residual or
headroom coordinate

`h_n = (1 - sigma)^n`.

In headroom space, ordinary multiplication of headrooms corresponds to addition
of iteration exponents:

`h_n * h_m = h_{n+m}`.

Thus a product of prime headrooms is an additive prime decomposition of the
exponent.  FTA supplies multiplicative factorization of the exponent in the
iteration/nested face; it does not fix a headroom factorization length.  The
Goldbach question is exactly the special length-two headroom factorization
question.

Boundary: this does not prove Goldbach.  It proves that the framework's
headroom formulation is a faithful restatement of Goldbach as a length-two
prime-headroom factorization, and it demonstrates the relativity of
factorization length at `sigma = 1/2` with `h_10`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Headroom powers -/

/-- The residual/headroom coordinate after `n` iterations at rate `sigma`. -/
def headroomPower (σ : K) (n : ℕ) : K :=
  (1 - σ) ^ n

@[simp] theorem headroomPower_zero (σ : K) :
    headroomPower σ 0 = 1 := by
  simp [headroomPower]

@[simp] theorem headroomPower_one (σ : K) :
    headroomPower σ 1 = 1 - σ := by
  simp [headroomPower]

/-- THEOREM 1: serializing headroom exponents is multiplication in H-space. -/
theorem headroomPower_mul
    (σ : K) (n m : ℕ) :
    headroomPower σ (n + m) =
      headroomPower σ n * headroomPower σ m := by
  simp [headroomPower, pow_add]

/-- THEOREM 2: repeating a headroom factor `m` times multiplies its exponent. -/
theorem headroomPower_pow
    (σ : K) (n m : ℕ) :
    (headroomPower σ n) ^ m = headroomPower σ (n * m) := by
  simp [headroomPower, pow_mul]

/-- THEOREM 3: headroom powers are injective on the nondegenerate salience
interval. -/
theorem headroomPower_injective_of_mem_Ioo
    {σ : K} (_hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Function.Injective (fun n : ℕ => headroomPower σ n) := by
  intro n m h
  have hkeep_pos : 0 < 1 - σ := sub_pos.mpr hσ1
  have hkeep_ne_one : (1 - σ) ≠ 1 := by
    intro hone
    have hσ_zero : σ = 0 := by linarith
    linarith
  have hz : (1 - σ) ^ (n : ℤ) = (1 - σ) ^ (m : ℤ) := by
    simpa [headroomPower] using h
  have hcast : (n : ℤ) = (m : ℤ) :=
    zpow_right_injective₀ hkeep_pos hkeep_ne_one hz
  exact Int.ofNat.inj hcast

/-- THEOREM 4: headroom multiplication is the residual form of serial
noisy-OR composition. -/
theorem headroomPower_eq_keep_iteratedRate
    (σ : K) (n : ℕ) :
    headroomPower σ n = 1 - iteratedRate σ n := by
  exact (keep_iteratedRate σ n).symm

/-! ## Prime headroom decompositions and length -/

/-- A prime-headroom decomposition of exponent `n` with a specified list
length.  The length lives in H-space; the factors are prime exponents read as
headroom factors. -/
def HeadroomPrimeDecompositionOfLength
    (σ : K) (n length : ℕ) : Prop :=
  ∃ factors : List PrimeExponent,
    factors.length = length ∧
      headroomPower σ n =
        (factors.map (fun p : PrimeExponent => headroomPower σ p.1)).prod

/-- Two-prime headroom factorization: the Goldbach-shaped H-space question. -/
def HeadroomPrimeTwoFactorization (σ : K) (n : ℕ) : Prop :=
  ∃ p q : PrimeExponent,
    headroomPower σ n = headroomPower σ p.1 * headroomPower σ q.1

/-- THEOREM 5: a list of prime headrooms multiplies to the headroom whose
exponent is the sum of the listed prime exponents. -/
theorem headroomPrimeList_prod_eq_sum
    (σ : K) (factors : List PrimeExponent) :
    (factors.map (fun p : PrimeExponent => headroomPower σ p.1)).prod =
      headroomPower σ ((factors.map fun p : PrimeExponent => p.1).sum) := by
  induction factors with
  | nil => simp [headroomPower]
  | cons p ps ih =>
      change
        headroomPower σ p.1 *
            (ps.map (fun p : PrimeExponent => headroomPower σ p.1)).prod =
          headroomPower σ
            (p.1 + (ps.map fun p : PrimeExponent => p.1).sum)
      rw [ih]
      exact (headroomPower_mul σ p.1
        ((ps.map fun p : PrimeExponent => p.1).sum)).symm

/-- THEOREM 6: on the nondegenerate interval, an H-space prime decomposition
of a fixed length is exactly an exponent-side prime-sum decomposition of that
same list length. -/
theorem headroomPrimeDecompositionOfLength_iff_sum_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {n length : ℕ} :
    HeadroomPrimeDecompositionOfLength σ n length ↔
      ∃ factors : List PrimeExponent,
        factors.length = length ∧
          n = (factors.map fun p : PrimeExponent => p.1).sum := by
  constructor
  · rintro ⟨factors, hlen, hprod⟩
    refine ⟨factors, hlen, ?_⟩
    apply headroomPower_injective_of_mem_Ioo hσ0 hσ1
    calc
      headroomPower σ n =
          (factors.map (fun p : PrimeExponent => headroomPower σ p.1)).prod :=
        hprod
      _ = headroomPower σ ((factors.map fun p : PrimeExponent => p.1).sum) :=
        headroomPrimeList_prod_eq_sum σ factors
  · rintro ⟨factors, hlen, hsum⟩
    refine ⟨factors, hlen, ?_⟩
    rw [hsum]
    exact (headroomPrimeList_prod_eq_sum σ factors).symm

/-- THEOREM 7: length-two H-space factorization is exactly ordinary Goldbach
at that exponent. -/
theorem headroomPrimeTwoFactorization_iff_goldbach_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n : ℕ} :
    HeadroomPrimeTwoFactorization σ n ↔
      HasPrimeAdditiveDecomposition n := by
  constructor
  · rintro ⟨p, q, hfac⟩
    refine ⟨p, q, ?_⟩
    apply headroomPower_injective_of_mem_Ioo hσ0 hσ1
    calc
      headroomPower σ n = headroomPower σ p.1 * headroomPower σ q.1 := hfac
      _ = headroomPower σ (p.1 + q.1) := (headroomPower_mul σ p.1 q.1).symm
  · rintro ⟨p, q, hn⟩
    refine ⟨p, q, ?_⟩
    rw [hn]
    exact headroomPower_mul σ p.1 q.1

/-- THEOREM 8: the even Goldbach statement is exactly length-two H-space
prime factorization for every even exponent. -/
theorem headroomEvenLengthTwo_iff_evenGoldbach_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (∀ n : ℕ, 2 ≤ n -> HeadroomPrimeTwoFactorization σ (2 * n)) ↔
      EvenGoldbachStatement := by
  constructor
  · intro h n hn
    exact (headroomPrimeTwoFactorization_iff_goldbach_of_mem_Ioo
      hσ0 hσ1).mp (h n hn)
  · intro h n hn
    exact (headroomPrimeTwoFactorization_iff_goldbach_of_mem_Ioo
      hσ0 hσ1).mpr (h n hn)

/-! ## The self-dual example: `h_10` has several prime lengths -/

/-- Prime exponent `2`. -/
def primeTwo : PrimeExponent := ⟨2, by norm_num⟩

/-- Prime exponent `3`. -/
def primeThree : PrimeExponent := ⟨3, by norm_num⟩

/-- Prime exponent `5`. -/
def primeFive : PrimeExponent := ⟨5, by norm_num⟩

/-- Prime exponent `7`. -/
def primeSeven : PrimeExponent := ⟨7, by norm_num⟩

/-- THEOREM 9: at `sigma = 1/2`, `h_10` has a length-five decomposition as
five copies of `h_2`. -/
theorem halfSigma_headroom10_length_five_twos :
    HeadroomPrimeDecompositionOfLength (1 / 2 : ℝ) 10 5 := by
  rw [headroomPrimeDecompositionOfLength_iff_sum_of_mem_Ioo
    halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2]
  refine ⟨[primeTwo, primeTwo, primeTwo, primeTwo, primeTwo], ?_, ?_⟩
  · rfl
  · norm_num [primeTwo]

/-- THEOREM 10: at `sigma = 1/2`, `h_10` has a length-two decomposition
`h_3 * h_7`. -/
theorem halfSigma_headroom10_length_two_three_seven :
    HeadroomPrimeDecompositionOfLength (1 / 2 : ℝ) 10 2 := by
  rw [headroomPrimeDecompositionOfLength_iff_sum_of_mem_Ioo
    halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2]
  refine ⟨[primeThree, primeSeven], ?_, ?_⟩
  · rfl
  · norm_num [primeThree, primeSeven]

/-- THEOREM 11: at `sigma = 1/2`, `h_10` also has a length-two decomposition
`h_5 * h_5`. -/
theorem halfSigma_headroom10_length_two_five_five :
    HeadroomPrimeDecompositionOfLength (1 / 2 : ℝ) 10 2 := by
  rw [headroomPrimeDecompositionOfLength_iff_sum_of_mem_Ioo
    halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2]
  refine ⟨[primeFive, primeFive], ?_, ?_⟩
  · rfl
  · norm_num [primeFive]

/-- THEOREM 12: the same `h_10` equality can be read as a repeated prime
headroom factor. -/
theorem halfSigma_headroom10_eq_headroom2_pow5 :
    headroomPower (1 / 2 : ℝ) 10 =
      (headroomPower (1 / 2 : ℝ) 2) ^ 5 := by
  rw [headroomPower_pow]

/-- THEOREM 13: the same `h_10` equality can be read as `h_3 * h_7`. -/
theorem halfSigma_headroom10_eq_headroom3_mul_headroom7 :
    headroomPower (1 / 2 : ℝ) 10 =
      headroomPower (1 / 2 : ℝ) 3 * headroomPower (1 / 2 : ℝ) 7 := by
  rw [← headroomPower_mul]

/-- THEOREM 14: the same `h_10` equality can be read as `h_5 * h_5`. -/
theorem halfSigma_headroom10_eq_headroom5_mul_headroom5 :
    headroomPower (1 / 2 : ℝ) 10 =
      headroomPower (1 / 2 : ℝ) 5 * headroomPower (1 / 2 : ℝ) 5 := by
  rw [← headroomPower_mul]

/-- A compact certificate for the H-space length-relativity theorem. -/
structure HeadroomFactorizationRelativityCertificate where
  headroom_mul :
    ∀ (σ : ℝ) (n m : ℕ),
      headroomPower σ (n + m) = headroomPower σ n * headroomPower σ m
  headroom_pow :
    ∀ (σ : ℝ) (n m : ℕ),
      (headroomPower σ n) ^ m = headroomPower σ (n * m)
  length_decomposition_iff_sum :
    ∀ {σ : ℝ}, 0 < σ -> σ < 1 -> ∀ {n length : ℕ},
      HeadroomPrimeDecompositionOfLength σ n length ↔
        ∃ factors : List PrimeExponent,
          factors.length = length ∧
            n = (factors.map fun p : PrimeExponent => p.1).sum
  length_two_iff_goldbach :
    ∀ {σ : ℝ}, 0 < σ -> σ < 1 -> ∀ {n : ℕ},
      HeadroomPrimeTwoFactorization σ n ↔ HasPrimeAdditiveDecomposition n
  h10_length5 : HeadroomPrimeDecompositionOfLength (1 / 2 : ℝ) 10 5
  h10_length2_37 : HeadroomPrimeDecompositionOfLength (1 / 2 : ℝ) 10 2
  h10_length2_55 : HeadroomPrimeDecompositionOfLength (1 / 2 : ℝ) 10 2

/-- THEOREM 15: the canonical H-space factorization-relativity certificate. -/
theorem headroomFactorizationRelativityCertificate :
    HeadroomFactorizationRelativityCertificate := by
  exact {
  headroom_mul := headroomPower_mul
  headroom_pow := headroomPower_pow
  length_decomposition_iff_sum := by
    intro σ hσ0 hσ1 n length
    exact headroomPrimeDecompositionOfLength_iff_sum_of_mem_Ioo hσ0 hσ1
  length_two_iff_goldbach := by
    intro σ hσ0 hσ1 n
    exact headroomPrimeTwoFactorization_iff_goldbach_of_mem_Ioo hσ0 hσ1
  h10_length5 := halfSigma_headroom10_length_five_twos
  h10_length2_37 := halfSigma_headroom10_length_two_three_seven
  h10_length2_55 := halfSigma_headroom10_length_two_five_five
  }

end AffineRelaxation
end SaturationMonoid
