import H0mework.Arithmetic.PrimeSearch.P331

/-!
# Proposition 332: Goldbach as a prime-indicator convolution coefficient

P328 supplies a finite pair search.  This file compresses that search into the
usual coefficient formula:

`G(n) = Σ_{p = 0}^n 1_Prime(p) * 1_Prime(n - p)`.

The theorem proved here is pointwise and computational:

`0 < G(n) ↔ n` has an additive decomposition into two primes.

Together with P330/P331, the same coefficient is therefore also the half-sigma
rate predicate and the H-space length-two headroom predicate.

Boundary: this is still not the global Goldbach theorem.  It is the closed
coefficient/algorithm surface for each fixed exponent.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Generic finite-list positivity lemmas -/

theorem list_countP_pos_iff_exists
    {α : Type*} (l : List α) (p : α → Bool) :
    0 < l.countP p ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil =>
      simp
  | cons a as ih =>
      by_cases hp : p a = true
      · simp [hp]
      · have hpfalse : p a = false := Bool.eq_false_iff.mpr hp
        simp [hpfalse, ih]

theorem list_sum_map_pos_iff_exists
    {α : Type*} (l : List α) (f : α → ℕ) :
    0 < (l.map f).sum ↔ ∃ a ∈ l, 0 < f a := by
  induction l with
  | nil =>
      simp
  | cons a as ih =>
      constructor
      · intro h
        by_cases hfa : f a = 0
        · have hsum : 0 < (as.map f).sum := by
            simpa [hfa] using h
          rcases ih.mp hsum with ⟨b, hbmem, hbpos⟩
          exact ⟨b, by simp [hbmem], hbpos⟩
        · exact ⟨a, by simp, Nat.pos_of_ne_zero hfa⟩
      · rintro ⟨b, hb, hbpos⟩
        rw [List.mem_cons] at hb
        rcases hb with hb | hb
        · subst hb
          have hle : f b ≤ f b + (as.map f).sum :=
            Nat.le_add_right _ _
          exact lt_of_lt_of_le hbpos hle
        · have hsum : 0 < (as.map f).sum :=
            ih.mpr ⟨b, hb, hbpos⟩
          have hle : (as.map f).sum ≤ f a + (as.map f).sum :=
            Nat.le_add_left _ _
          exact lt_of_lt_of_le hsum hle

/-! ## Prime-indicator convolution -/

/-- Prime indicator as a natural-number coefficient. -/
def primeIndicator (n : ℕ) : ℕ :=
  if Nat.Prime n then 1 else 0

@[simp] theorem primeIndicator_pos_iff (n : ℕ) :
    0 < primeIndicator n ↔ Nat.Prime n := by
  unfold primeIndicator
  by_cases hp : Nat.Prime n <;> simp [hp]

theorem primeIndicator_mul_pos_iff (p q : ℕ) :
    0 < primeIndicator p * primeIndicator q ↔
      Nat.Prime p ∧ Nat.Prime q := by
  unfold primeIndicator
  by_cases hp : Nat.Prime p <;> by_cases hq : Nat.Prime q <;>
    simp [hp, hq]

/-- Ordered Goldbach representation coefficient:
`Σ_{p≤n} 1_Prime(p) * 1_Prime(n-p)`. -/
def goldbachConvolutionCoefficient (n : ℕ) : ℕ :=
  ((List.range (n + 1)).map
    (fun p : ℕ => primeIndicator p * primeIndicator (n - p))).sum

/-- THEOREM 1: the convolution coefficient is positive exactly when `n` has
an additive prime decomposition. -/
theorem goldbachConvolutionCoefficient_pos_iff
    (n : ℕ) :
    0 < goldbachConvolutionCoefficient n ↔
      HasPrimeAdditiveDecomposition n := by
  rw [goldbachConvolutionCoefficient, list_sum_map_pos_iff_exists]
  constructor
  · rintro ⟨p, hmem, hpos⟩
    have hp_le : p ≤ n := Nat.lt_succ_iff.mp (List.mem_range.mp hmem)
    have hprime :
        Nat.Prime p ∧ Nat.Prime (n - p) :=
      (primeIndicator_mul_pos_iff p (n - p)).mp hpos
    refine ⟨⟨p, hprime.1⟩, ⟨n - p, hprime.2⟩, ?_⟩
    exact (Nat.add_sub_of_le hp_le).symm
  · rintro ⟨p, q, hsum⟩
    refine ⟨p.1, ?_, ?_⟩
    · rw [List.mem_range]
      have hp_le : p.1 ≤ n := by
        rw [hsum]
        exact Nat.le_add_right p.1 q.1
      exact Nat.lt_succ_of_le hp_le
    · have hsub : n - p.1 = q.1 := by
        rw [hsum]
        exact Nat.add_sub_cancel_left p.1 q.1
      rw [hsub]
      exact (primeIndicator_mul_pos_iff p.1 q.1).mpr ⟨p.2, q.2⟩

/-- THEOREM 2: the coefficient formula and P328's direct finite search have
the same success bit. -/
theorem goldbachConvolutionCoefficient_pos_iff_search
    (n : ℕ) :
    0 < goldbachConvolutionCoefficient n ↔
      (goldbachSearchNat n).isSome = true := by
  exact (goldbachConvolutionCoefficient_pos_iff n).trans
    (goldbachSearchNat_isSome_iff n).symm

/-- THEOREM 3: at half sigma, the coefficient formula is exactly the raw-rate
Goldbach predicate on the named iterated rate. -/
theorem halfSigmaRateGoldbachComplete_iff_convolutionCoefficient_pos
    (n : ℕ) :
    HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) n) ↔
      0 < goldbachConvolutionCoefficient n := by
  exact (halfSigmaRateGoldbachComplete_iteratedRate_iff n).trans
    (goldbachConvolutionCoefficient_pos_iff n).symm

/-- THEOREM 4: at half sigma, the H-space lifted search succeeds exactly when
the convolution coefficient is positive. -/
theorem halfSigmaHeadroomGoldbachSearch_iff_convolutionCoefficient_pos
    (n : ℕ) :
    (headroomGoldbachSearch (1 / 2 : ℝ) n).isSome = true ↔
      0 < goldbachConvolutionCoefficient n := by
  exact (halfSigmaHeadroomGoldbachSearch_iff_rateGoldbachComplete n).trans
    (halfSigmaRateGoldbachComplete_iff_convolutionCoefficient_pos n)

/-- A compact certificate for the convolution-coefficient computation surface.
-/
structure P332GoldbachConvolutionCoefficientCertificate where
  coefficient_pos_iff_goldbach :
    ∀ n : ℕ,
      0 < goldbachConvolutionCoefficient n ↔
        HasPrimeAdditiveDecomposition n
  coefficient_pos_iff_search :
    ∀ n : ℕ,
      0 < goldbachConvolutionCoefficient n ↔
        (goldbachSearchNat n).isSome = true
  half_sigma_rate_iff_coefficient_pos :
    ∀ n : ℕ,
      HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) n) ↔
        0 < goldbachConvolutionCoefficient n
  half_sigma_headroom_search_iff_coefficient_pos :
    ∀ n : ℕ,
      (headroomGoldbachSearch (1 / 2 : ℝ) n).isSome = true ↔
        0 < goldbachConvolutionCoefficient n

/-- THEOREM 5: the canonical convolution-coefficient certificate. -/
theorem p332GoldbachConvolutionCoefficientCertificate :
    P332GoldbachConvolutionCoefficientCertificate where
  coefficient_pos_iff_goldbach :=
    goldbachConvolutionCoefficient_pos_iff
  coefficient_pos_iff_search :=
    goldbachConvolutionCoefficient_pos_iff_search
  half_sigma_rate_iff_coefficient_pos :=
    halfSigmaRateGoldbachComplete_iff_convolutionCoefficient_pos
  half_sigma_headroom_search_iff_coefficient_pos :=
    halfSigmaHeadroomGoldbachSearch_iff_convolutionCoefficient_pos

end AffineRelaxation
end SaturationMonoid
