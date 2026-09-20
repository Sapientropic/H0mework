import H0mework.Arithmetic.PrimeShadow.P329

/-!
# Proposition 330: finite search as the half-sigma projection frontend

P320 proves that the half-sigma arithmetic/rate predicates faithfully reflect
ordinary additive prime decomposition.  P328/P329 then provide a finite search
surface for that same pointwise predicate and lift it back to H-space.

This file closes that triangle:

* image-level half-sigma Goldbach is equivalent to finite search at the stored
  exponent;
* raw half-sigma rate Goldbach on image points is equivalent to the same search;
* named half-sigma iterated rates are equivalent to the same search;
* the H-space lifted search and the raw-rate predicate have the same success
  bit at each exponent.

Boundary: these are pointwise equivalences and computation surfaces.  They do
not assert the global even Goldbach statement.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Half-sigma projection predicates as finite-search predicates -/

/-- THEOREM 1: image-level half-sigma Goldbach is exactly finite search at the
image exponent. -/
theorem halfSigmaImageGoldbachComplete_iff_goldbachSearchNat_exponent
    (r : HalfSigmaArithmeticImage) :
    HalfSigmaImageGoldbachComplete r ↔
      (goldbachSearchNat (SigmaExponentImage.exponent r)).isSome = true := by
  exact (halfSigmaImageGoldbachComplete_iff_exponentGoldbach r).trans
    (goldbachSearchNat_isSome_iff
      (SigmaExponentImage.exponent r)).symm

/-- THEOREM 2: raw-rate half-sigma Goldbach on an image point is exactly
finite search at that point's exponent. -/
theorem halfSigmaRateGoldbachComplete_image_iff_goldbachSearchNat_exponent
    (r : HalfSigmaArithmeticImage) :
    HalfSigmaRateGoldbachComplete r.1 ↔
      (goldbachSearchNat (SigmaExponentImage.exponent r)).isSome = true := by
  exact (halfSigmaRateGoldbachComplete_of_image r).trans
    (halfSigmaImageGoldbachComplete_iff_goldbachSearchNat_exponent r)

/-- THEOREM 3: on named half-sigma iterated rates, the raw-rate predicate is
exactly the finite search success bit. -/
theorem halfSigmaRateGoldbachComplete_iteratedRate_iff_goldbachSearchNat
    (n : ℕ) :
    HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) n) ↔
      (goldbachSearchNat n).isSome = true := by
  exact (halfSigmaRateGoldbachComplete_iteratedRate_iff n).trans
    (goldbachSearchNat_isSome_iff n).symm

/-- THEOREM 4: the typed prime-pair search has the same half-sigma rate
meaning as the raw search on named iterated rates. -/
theorem halfSigmaRateGoldbachComplete_iteratedRate_iff_primePairSearch
    (n : ℕ) :
    HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) n) ↔
      (goldbachSearchPrimePair n).isSome = true := by
  exact (halfSigmaRateGoldbachComplete_iteratedRate_iff n).trans
    (goldbachSearchPrimePair_isSome_iff n).symm

/-- THEOREM 5: at half sigma, the lifted H-space search and the raw-rate
half-sigma predicate are equivalent pointwise at every exponent. -/
theorem halfSigmaHeadroomGoldbachSearch_iff_rateGoldbachComplete
    (n : ℕ) :
    (headroomGoldbachSearch (1 / 2 : ℝ) n).isSome = true ↔
      HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) n) := by
  exact
    (headroomGoldbachSearch_isSome_iff_of_mem_Ioo
      halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2 n).trans
      ((headroomPrimeTwoFactorization_iff_goldbach_of_mem_Ioo
        halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2).trans
        (halfSigmaRateGoldbachComplete_iteratedRate_iff n).symm)

/-- THEOREM 6: the even half-sigma H-space search success bit is exactly the
raw-rate half-sigma predicate at the even exponent. -/
theorem halfSigmaEvenHeadroomGoldbachSearch_iff_rateGoldbachComplete
    (n : ℕ) :
    (headroomGoldbachSearch (1 / 2 : ℝ) (2 * n)).isSome = true ↔
      HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) (2 * n)) :=
  halfSigmaHeadroomGoldbachSearch_iff_rateGoldbachComplete (2 * n)

/-- Compact certificate for the half-sigma finite-search frontend. -/
structure P330HalfSigmaSearchProjectionCertificate where
  image_search_complete :
    ∀ r : HalfSigmaArithmeticImage,
      HalfSigmaImageGoldbachComplete r ↔
        (goldbachSearchNat (SigmaExponentImage.exponent r)).isSome = true
  rate_image_search_complete :
    ∀ r : HalfSigmaArithmeticImage,
      HalfSigmaRateGoldbachComplete r.1 ↔
        (goldbachSearchNat (SigmaExponentImage.exponent r)).isSome = true
  rate_iterated_search_complete :
    ∀ n : ℕ,
      HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) n) ↔
        (goldbachSearchNat n).isSome = true
  rate_iterated_prime_pair_search_complete :
    ∀ n : ℕ,
      HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) n) ↔
        (goldbachSearchPrimePair n).isSome = true
  headroom_search_matches_rate :
    ∀ n : ℕ,
      (headroomGoldbachSearch (1 / 2 : ℝ) n).isSome = true ↔
        HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) n)
  even_headroom_search_matches_rate :
    ∀ n : ℕ,
      (headroomGoldbachSearch (1 / 2 : ℝ) (2 * n)).isSome = true ↔
        HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) (2 * n))

/-- THEOREM 7: the canonical half-sigma finite-search projection certificate.
-/
theorem p330HalfSigmaSearchProjectionCertificate :
    P330HalfSigmaSearchProjectionCertificate where
  image_search_complete :=
    halfSigmaImageGoldbachComplete_iff_goldbachSearchNat_exponent
  rate_image_search_complete :=
    halfSigmaRateGoldbachComplete_image_iff_goldbachSearchNat_exponent
  rate_iterated_search_complete :=
    halfSigmaRateGoldbachComplete_iteratedRate_iff_goldbachSearchNat
  rate_iterated_prime_pair_search_complete :=
    halfSigmaRateGoldbachComplete_iteratedRate_iff_primePairSearch
  headroom_search_matches_rate :=
    halfSigmaHeadroomGoldbachSearch_iff_rateGoldbachComplete
  even_headroom_search_matches_rate :=
    halfSigmaEvenHeadroomGoldbachSearch_iff_rateGoldbachComplete

end AffineRelaxation
end SaturationMonoid
