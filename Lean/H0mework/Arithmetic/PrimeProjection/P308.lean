import H0mework.Arithmetic.PrimeShadow.P307

/-!
# Proposition 308: the Goldbach boundary on the P307 carrier

P307 proves that, on the nondegenerate salience carrier `0 < σ < 1`,
factor-atomic sigma rates are prime exponents.  This file records the next
honest boundary.

Serial `satOr` composition is addition of iteration counts, so a Goldbach
decomposition of an even count transports to a two-atomic `satOr`
decomposition on the sigma carrier.  Conversely, on the nondegenerate carrier,
injectivity transports such a sigma decomposition back to an ordinary
Goldbach decomposition.

Therefore a proposed theorem

`FTA -> every even sigma rate is a satOr of two sigma-atomic rates`

has exactly the same strength as

`FTA -> ordinary Goldbach`.

The multiplicative prime factorization supplied by FTA does not by itself
produce the additive two-prime decomposition; that would be an additional
Goldbach-strength bridge.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Ordinary exponent-side statements -/

/-- A natural number has a multiplicative factorization into prime exponents.
This is the FTA-shaped hypothesis; it is intentionally multiplicative. -/
def HasPrimeMultiplicativeFactorization (n : ℕ) : Prop :=
  ∃ factors : List PrimeExponent,
    n = (factors.map (fun p : PrimeExponent => p.1)).prod

/-- The FTA-shaped global statement used in this file. -/
def PrimeMultiplicativeFactorizationStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → HasPrimeMultiplicativeFactorization n

/-- Goldbach at one exponent: the exponent is a sum of two prime exponents. -/
def HasPrimeAdditiveDecomposition (n : ℕ) : Prop :=
  ∃ p q : PrimeExponent, n = p.1 + q.1

/-- Goldbach for even exponents `2 * n`, with `n ≥ 2` so the even number is
at least `4`. -/
def EvenGoldbachStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → HasPrimeAdditiveDecomposition (2 * n)

/-! ## Sigma-carrier Goldbach -/

/-- Goldbach at one sigma-carrier point: an effective rate at exponent `n` is
the serial `satOr` composition of two prime-exponent effective rates. -/
def SigmaGoldbachDecomposition (σ : K) (n : ℕ) : Prop :=
  ∃ p q : PrimeExponent,
    iteratedRate σ n =
      satOrField (iteratedRate σ p.1) (iteratedRate σ q.1)

/-- Sigma-carrier Goldbach for even exponents. -/
def SigmaEvenGoldbachStatement (σ : K) : Prop :=
  ∀ n : ℕ, 2 ≤ n → SigmaGoldbachDecomposition σ (2 * n)

/-- THEOREM 1: ordinary additive Goldbach transports to the sigma carrier by
the serial `satOr = addition of exponents` law. -/
theorem sigmaGoldbachDecomposition_of_goldbach
    (σ : K) {n : ℕ}
    (h : HasPrimeAdditiveDecomposition n) :
    SigmaGoldbachDecomposition σ n := by
  rcases h with ⟨p, q, hn⟩
  refine ⟨p, q, ?_⟩
  rw [hn]
  exact iteratedRate_add σ p.1 q.1

/-- The raw effective-rate map is injective on `0 < σ < 1`.  P307 proves the
bundled non-absorbing version; this is the unbundled form needed to pull a
sigma-carrier Goldbach decomposition back to exponents. -/
theorem iteratedRate_injective_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Function.Injective (fun n : ℕ => iteratedRate σ n) := by
  intro n m h
  have hinj :=
    iteratedNonAbsorbingRate_injective_of_mem_Ioo
      (K := K) hσ0 hσ1
  apply hinj
  apply Subtype.ext
  simpa [iteratedNonAbsorbingRate] using h

/-- THEOREM 2: on the nondegenerate P307 carrier, sigma-carrier Goldbach
reflects back to ordinary additive Goldbach. -/
theorem goldbach_of_sigmaGoldbachDecomposition_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n : ℕ}
    (h : SigmaGoldbachDecomposition σ n) :
    HasPrimeAdditiveDecomposition n := by
  rcases h with ⟨p, q, hn⟩
  refine ⟨p, q, ?_⟩
  apply iteratedRate_injective_of_mem_Ioo hσ0 hσ1
  calc
    iteratedRate σ n =
        satOrField (iteratedRate σ p.1) (iteratedRate σ q.1) := hn
    _ = iteratedRate σ (p.1 + q.1) := (iteratedRate_add σ p.1 q.1).symm

/-- THEOREM 3: on `0 < σ < 1`, sigma-carrier Goldbach at an exponent is
equivalent to ordinary exponent Goldbach. -/
theorem sigmaGoldbachDecomposition_iff_goldbach_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n : ℕ} :
    SigmaGoldbachDecomposition σ n ↔
      HasPrimeAdditiveDecomposition n := by
  constructor
  · exact goldbach_of_sigmaGoldbachDecomposition_of_mem_Ioo hσ0 hσ1
  · exact sigmaGoldbachDecomposition_of_goldbach σ

/-- THEOREM 4: the even global statements are equivalent on the P307 carrier. -/
theorem sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaEvenGoldbachStatement σ ↔ EvenGoldbachStatement := by
  constructor
  · intro h n hn
    exact goldbach_of_sigmaGoldbachDecomposition_of_mem_Ioo
      hσ0 hσ1 (h n hn)
  · intro h n hn
    exact sigmaGoldbachDecomposition_of_goldbach σ (h n hn)

/-! ## FTA does not supply the additive bridge -/

/-- THEOREM 5: any proposed `FTA -> sigma-Goldbach` theorem is exactly as
strong as a proposed `FTA -> ordinary Goldbach` theorem on the nondegenerate
P307 carrier.  Thus FTA alone has not produced Goldbach; the missing content is
precisely an additive two-prime bridge. -/
theorem fta_to_sigmaGoldbach_iff_fta_to_goldbach_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (PrimeMultiplicativeFactorizationStatement →
        SigmaEvenGoldbachStatement σ) ↔
      (PrimeMultiplicativeFactorizationStatement →
        EvenGoldbachStatement) := by
  constructor
  · intro h hfta
    exact (sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1).mp
      (h hfta)
  · intro h hfta
    exact (sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1).mpr
      (h hfta)

/-- THEOREM 6: once an FTA certificate is available, a proof that FTA implies
sigma-carrier Goldbach is exactly a proof of ordinary Goldbach.  The shared
carrier adds no extra transfer principle by itself; it faithfully transports
the ordinary additive question. -/
theorem fta_bridge_reduces_to_goldbach_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hfta : PrimeMultiplicativeFactorizationStatement) :
    (PrimeMultiplicativeFactorizationStatement →
        SigmaEvenGoldbachStatement σ) ↔
      EvenGoldbachStatement := by
  constructor
  · intro h
    exact (sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1).mp
      (h hfta)
  · intro h _
    exact (sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1).mpr h

/-- A named certificate for the boundary: proving the requested bridge from
FTA to carrier-Goldbach is interchangeable with proving FTA to Goldbach. -/
structure GoldbachBoundaryCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  pointwise_iff :
    ∀ n : ℕ,
      SigmaGoldbachDecomposition σ n ↔
        HasPrimeAdditiveDecomposition n
  even_iff :
    SigmaEvenGoldbachStatement σ ↔ EvenGoldbachStatement
  fta_bridge_iff :
      (PrimeMultiplicativeFactorizationStatement →
        SigmaEvenGoldbachStatement σ) ↔
      (PrimeMultiplicativeFactorizationStatement →
        EvenGoldbachStatement)
  fta_reduces_bridge_to_goldbach :
    PrimeMultiplicativeFactorizationStatement →
      ((PrimeMultiplicativeFactorizationStatement →
          SigmaEvenGoldbachStatement σ) ↔
        EvenGoldbachStatement)

/-- THEOREM 7: the canonical Goldbach-boundary certificate on the P307 carrier. -/
theorem goldbachBoundaryCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    GoldbachBoundaryCertificate σ hσ0 hσ1 where
  pointwise_iff := by
    intro n
    exact sigmaGoldbachDecomposition_iff_goldbach_of_mem_Ioo hσ0 hσ1
  even_iff := sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1
  fta_bridge_iff :=
    fta_to_sigmaGoldbach_iff_fta_to_goldbach_of_mem_Ioo hσ0 hσ1
  fta_reduces_bridge_to_goldbach := by
    intro hfta
    exact fta_bridge_reduces_to_goldbach_of_mem_Ioo hσ0 hσ1 hfta

end AffineRelaxation
end SaturationMonoid
