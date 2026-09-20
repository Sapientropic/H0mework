import H0mework.Arithmetic.PrimeShadow.P328

/-!
# Proposition 329: direct Goldbach search lifted back to headroom space

P326 identifies ordinary Goldbach with a length-two prime-headroom
factorization:

`h_n = h_p * h_q`.

P328 then supplies a finite direct search over natural-number prime pairs.
This file welds the two layers: the same finite search is a sound and complete
direct computation surface for the H-space length-two factorization predicate
on every nondegenerate salience rate `0 < sigma < 1`.

Boundary: this is still pointwise computation.  It proves that the algorithm
decides the fixed input predicate whenever it terminates on that fixed finite
search space; it does not prove the global Goldbach statement.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Prime-pair search as a typed certificate surface -/

/-- Retype a raw pair as a pair of prime exponents exactly when the raw pair is
a certified Goldbach pair. -/
def goldbachRawPairToPrimePair (n : ℕ) (pair : ℕ × ℕ) :
    Option (PrimeExponent × PrimeExponent) :=
  if hp : GoldbachPairPredicate n pair then
    some (⟨pair.1, hp.1⟩, ⟨pair.2, hp.2.1⟩)
  else
    none

/-- The direct Goldbach search with the returned pair retyped as prime
exponents.  The computational search is still `goldbachSearchNat`; this layer
only attaches prime proofs to a returned raw pair. -/
def goldbachSearchPrimePair (n : ℕ) :
    Option (PrimeExponent × PrimeExponent) :=
  (goldbachSearchNat n).bind (goldbachRawPairToPrimePair n)

/-- THEOREM 1: retyping the returned pair preserves the success bit exactly.
-/
theorem goldbachSearchPrimePair_isSome_eq
    (n : ℕ) :
    (goldbachSearchPrimePair n).isSome =
      (goldbachSearchNat n).isSome := by
  unfold goldbachSearchPrimePair
  cases hsearch : goldbachSearchNat n with
  | none =>
      simp
  | some pair =>
      have hp : GoldbachPairPredicate n pair := goldbachSearchNat_sound hsearch
      simp [goldbachRawPairToPrimePair, hp]

/-- THEOREM 2: the typed prime-pair search succeeds exactly at the ordinary
pointwise Goldbach predicate. -/
theorem goldbachSearchPrimePair_isSome_iff
    (n : ℕ) :
    (goldbachSearchPrimePair n).isSome = true ↔
      HasPrimeAdditiveDecomposition n := by
  rw [goldbachSearchPrimePair_isSome_eq, goldbachSearchNat_isSome_iff]

/-- THEOREM 3: any typed pair returned by the direct search has the correct
additive exponent equation. -/
theorem goldbachSearchPrimePair_sound
    {n : ℕ} {p q : PrimeExponent}
    (h : goldbachSearchPrimePair n = some (p, q)) :
    n = p.1 + q.1 := by
  unfold goldbachSearchPrimePair at h
  cases hsearch : goldbachSearchNat n with
  | none =>
      simp [hsearch] at h
  | some pair =>
      have hp : GoldbachPairPredicate n pair := goldbachSearchNat_sound hsearch
      simp [hsearch, goldbachRawPairToPrimePair, hp] at h
      have hpval : p.1 = pair.1 := by
        rw [← h.1]
      have hqval : q.1 = pair.2 := by
        rw [← h.2]
      rw [hpval, hqval]
      exact hp.2.2

/-! ## The same search as an H-space factorization calculator -/

/-- Direct search for a length-two prime-headroom factorization.  The algorithm
does not depend on `sigma`; `sigma` supplies the H-space interpretation of the
returned exponents. -/
def headroomGoldbachSearch (_σ : K) (n : ℕ) :
    Option (PrimeExponent × PrimeExponent) :=
  goldbachSearchPrimePair n

/-- THEOREM 4: if the headroom search returns `p,q`, it really computes the
factorization `h_n = h_p * h_q`. -/
theorem headroomGoldbachSearch_sound
    (σ : K) {n : ℕ} {p q : PrimeExponent}
    (h : headroomGoldbachSearch σ n = some (p, q)) :
    headroomPower σ n =
      headroomPower σ p.1 * headroomPower σ q.1 := by
  have hsum : n = p.1 + q.1 := goldbachSearchPrimePair_sound (by
    simpa [headroomGoldbachSearch] using h)
  rw [hsum]
  exact headroomPower_mul σ p.1 q.1

/-- THEOREM 5: a returned pair is a full H-space length-two factorization
witness. -/
theorem headroomGoldbachSearch_sound_factorization
    (σ : K) {n : ℕ} {p q : PrimeExponent}
    (h : headroomGoldbachSearch σ n = some (p, q)) :
    HeadroomPrimeTwoFactorization σ n := by
  exact ⟨p, q, headroomGoldbachSearch_sound σ h⟩

/-- THEOREM 6: on `0 < sigma < 1`, the direct search succeeds exactly when the
H-space length-two prime-headroom factorization exists. -/
theorem headroomGoldbachSearch_isSome_iff_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) (n : ℕ) :
    (headroomGoldbachSearch σ n).isSome = true ↔
      HeadroomPrimeTwoFactorization σ n := by
  unfold headroomGoldbachSearch
  exact (goldbachSearchPrimePair_isSome_iff n).trans
    (headroomPrimeTwoFactorization_iff_goldbach_of_mem_Ioo
      hσ0 hσ1).symm

/-- THEOREM 7: any existing H-space length-two factorization on the
nondegenerate interval makes the finite search succeed. -/
theorem headroomGoldbachSearch_complete_of_factorization
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {n : ℕ} (hfac : HeadroomPrimeTwoFactorization σ n) :
    (headroomGoldbachSearch σ n).isSome = true :=
  (headroomGoldbachSearch_isSome_iff_of_mem_Ioo hσ0 hσ1 n).mpr hfac

/-- THEOREM 8: on even input, the lifted search is exactly the pointwise
even-Goldbach H-space predicate. -/
theorem headroomGoldbachSearch_even_isSome_iff_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) (n : ℕ) :
    (headroomGoldbachSearch σ (2 * n)).isSome = true ↔
      HeadroomPrimeTwoFactorization σ (2 * n) :=
  headroomGoldbachSearch_isSome_iff_of_mem_Ioo hσ0 hσ1 (2 * n)

/-- Compact certificate for the lifted direct-search surface. -/
structure P329HeadroomGoldbachSearchCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  typed_search_complete :
    ∀ n : ℕ,
      (goldbachSearchPrimePair n).isSome = true ↔
        HasPrimeAdditiveDecomposition n
  typed_search_sound :
    ∀ {n : ℕ} {p q : PrimeExponent},
      goldbachSearchPrimePair n = some (p, q) ->
        n = p.1 + q.1
  headroom_search_sound :
    ∀ {n : ℕ} {p q : PrimeExponent},
      headroomGoldbachSearch σ n = some (p, q) ->
        headroomPower σ n =
          headroomPower σ p.1 * headroomPower σ q.1
  headroom_search_complete :
    ∀ n : ℕ,
      (headroomGoldbachSearch σ n).isSome = true ↔
        HeadroomPrimeTwoFactorization σ n
  even_headroom_search_complete :
    ∀ n : ℕ,
      (headroomGoldbachSearch σ (2 * n)).isSome = true ↔
        HeadroomPrimeTwoFactorization σ (2 * n)

/-- THEOREM 9: the canonical lifted direct-search certificate. -/
theorem p329HeadroomGoldbachSearchCertificate
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    P329HeadroomGoldbachSearchCertificate σ hσ0 hσ1 where
  typed_search_complete := goldbachSearchPrimePair_isSome_iff
  typed_search_sound := by
    intro n p q h
    exact goldbachSearchPrimePair_sound h
  headroom_search_sound := by
    intro n p q h
    exact headroomGoldbachSearch_sound σ h
  headroom_search_complete :=
    headroomGoldbachSearch_isSome_iff_of_mem_Ioo hσ0 hσ1
  even_headroom_search_complete :=
    headroomGoldbachSearch_even_isSome_iff_of_mem_Ioo hσ0 hσ1

end AffineRelaxation
end SaturationMonoid
