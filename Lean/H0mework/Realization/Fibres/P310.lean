import H0mework.Arithmetic.PrimeProjection.P309

/-!
# Proposition 310: what FTA actually transfers on the sigma carrier

P307/P309 show that serial `satOr` and nested iteration share the same
`iteratedRate` carrier.  This file tests the tempting bridge precisely.

FTA does transfer to the sigma carrier, but it transfers to the
**nested-iteration / multiplicative** face: a prime product decomposition of an
exponent becomes a nested prime-iteration decomposition of the corresponding
effective rate.

To turn that nested decomposition into a two-prime serial `satOr`
decomposition, the missing content is exactly the exponent-side equation

`product factors = p + q`.

Thus the shared carrier is real, but faithful: it exposes the required bridge
rather than supplying Goldbach for free.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Nested iteration over a list of exponents -/

/-- Apply a list of iteration counts as nested effective-rate updates.

For `[a,b,c]` this is

`iteratedRate (iteratedRate (iteratedRate σ a) b) c`,

which corresponds to exponent product `a*b*c`.
-/
def nestedIteratedRate (σ : K) : List ℕ → K
  | [] => σ
  | n :: ns => nestedIteratedRate (iteratedRate σ n) ns

@[simp] theorem nestedIteratedRate_nil (σ : K) :
    nestedIteratedRate σ [] = σ := rfl

@[simp] theorem nestedIteratedRate_cons
    (σ : K) (n : ℕ) (ns : List ℕ) :
    nestedIteratedRate σ (n :: ns) =
      nestedIteratedRate (iteratedRate σ n) ns := rfl

/-- THEOREM 1: nested iteration by a list is the effective rate at the product
of the list's exponents. -/
theorem nestedIteratedRate_eq_iteratedRate_prod
    (σ : K) (ns : List ℕ) :
    nestedIteratedRate σ ns = iteratedRate σ ns.prod := by
  induction ns generalizing σ with
  | nil =>
      simp [nestedIteratedRate]
  | cons n ns ih =>
      simp [nestedIteratedRate, ih, iteratedRate_iteratedRate]

/-! ## FTA transfers to the nested/multiplicative face -/

/-- A sigma-carrier prime nested decomposition: the effective rate at exponent
`n` is obtained by nesting prime-exponent iteration steps. -/
def HasPrimeNestedSigmaDecomposition (σ : K) (n : ℕ) : Prop :=
  ∃ factors : List PrimeExponent,
    nestedIteratedRate σ (factors.map (fun p : PrimeExponent => p.1)) =
      iteratedRate σ n

/-- Global sigma-carrier nested prime factorization. -/
def SigmaNestedPrimeFactorizationStatement (σ : K) : Prop :=
  ∀ n : ℕ, 2 ≤ n → HasPrimeNestedSigmaDecomposition σ n

/-- THEOREM 2: ordinary prime multiplicative factorization transports to the
sigma carrier as nested prime iteration.  This direction does not need
nondegeneracy; it is just the multiplication face of `iteratedRate`. -/
theorem sigmaNestedPrimeDecomposition_of_primeFactorization
    (σ : K) {n : ℕ}
    (h : HasPrimeMultiplicativeFactorization n) :
    HasPrimeNestedSigmaDecomposition σ n := by
  rcases h with ⟨factors, hn⟩
  refine ⟨factors, ?_⟩
  rw [nestedIteratedRate_eq_iteratedRate_prod, ← hn]

/-- THEOREM 3: an FTA-shaped statement supplies the full nested sigma
factorization statement. -/
theorem fta_to_sigmaNestedPrimeFactorization
    (σ : K) :
    PrimeMultiplicativeFactorizationStatement →
      SigmaNestedPrimeFactorizationStatement σ := by
  intro hfta n hn
  exact sigmaNestedPrimeDecomposition_of_primeFactorization σ (hfta n hn)

/-- THEOREM 4: on `0 < σ < 1`, nested sigma prime factorization is exactly
ordinary multiplicative prime factorization. -/
theorem sigmaNestedPrimeDecomposition_iff_primeFactorization_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n : ℕ} :
    HasPrimeNestedSigmaDecomposition σ n ↔
      HasPrimeMultiplicativeFactorization n := by
  constructor
  · intro h
    rcases h with ⟨factors, hrate⟩
    refine ⟨factors, ?_⟩
    have hprod :
        (factors.map (fun p : PrimeExponent => p.1)).prod = n := by
      apply iteratedRate_injective_of_mem_Ioo hσ0 hσ1
      calc
        iteratedRate σ (factors.map (fun p : PrimeExponent => p.1)).prod =
            nestedIteratedRate σ (factors.map (fun p : PrimeExponent => p.1)) :=
          (nestedIteratedRate_eq_iteratedRate_prod σ
            (factors.map (fun p : PrimeExponent => p.1))).symm
        _ = iteratedRate σ n := hrate
    exact hprod.symm
  · intro h
    exact sigmaNestedPrimeDecomposition_of_primeFactorization σ h

/-- THEOREM 5: the global nested sigma factorization statement is equivalent
to the FTA-shaped multiplicative statement on the nondegenerate carrier. -/
theorem sigmaNestedPrimeFactorization_iff_fta_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaNestedPrimeFactorizationStatement σ ↔
      PrimeMultiplicativeFactorizationStatement := by
  constructor
  · intro h n hn
    exact (sigmaNestedPrimeDecomposition_iff_primeFactorization_of_mem_Ioo
      hσ0 hσ1).mp (h n hn)
  · intro h
    exact fta_to_sigmaNestedPrimeFactorization σ h

/-! ## The missing bridge to Goldbach is exactly product equals sum -/

/-- THEOREM 6: a nested prime-iteration decomposition equals a two-prime
serial `satOr` decomposition precisely when the product of its factor exponents
equals the sum of those two prime exponents.

This is the formal version of the key boundary: the shared carrier connects
the multiplicative and additive faces, but on `0 < σ < 1` it does so
faithfully.  The extra bridge needed for Goldbach is the exponent equation
`∏ factors = p + q`; it is not supplied by FTA's product decomposition alone.
-/
theorem nestedPrimeSigma_eq_twoPrimeSatOr_iff_product_eq_sum_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (factors : List PrimeExponent) (p q : PrimeExponent) :
    nestedIteratedRate σ (factors.map (fun r : PrimeExponent => r.1)) =
        satOrField (iteratedRate σ p.1) (iteratedRate σ q.1) ↔
      (factors.map (fun r : PrimeExponent => r.1)).prod = p.1 + q.1 := by
  constructor
  · intro h
    apply iteratedRate_injective_of_mem_Ioo hσ0 hσ1
    calc
      iteratedRate σ (factors.map (fun r : PrimeExponent => r.1)).prod =
          nestedIteratedRate σ (factors.map (fun r : PrimeExponent => r.1)) :=
        (nestedIteratedRate_eq_iteratedRate_prod σ
          (factors.map (fun r : PrimeExponent => r.1))).symm
      _ = satOrField (iteratedRate σ p.1) (iteratedRate σ q.1) := h
      _ = iteratedRate σ (p.1 + q.1) := (iteratedRate_add σ p.1 q.1).symm
  · intro h
    calc
      nestedIteratedRate σ (factors.map (fun r : PrimeExponent => r.1)) =
          iteratedRate σ (factors.map (fun r : PrimeExponent => r.1)).prod :=
        nestedIteratedRate_eq_iteratedRate_prod σ
          (factors.map (fun r : PrimeExponent => r.1))
      _ = iteratedRate σ (p.1 + q.1) := by rw [h]
      _ = satOrField (iteratedRate σ p.1) (iteratedRate σ q.1) :=
        iteratedRate_add σ p.1 q.1

/-- A compact certificate for the exact shape of the FTA transfer on the
shared sigma carrier. -/
structure FtaSigmaCarrierTransferCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  nested_list_product :
    ∀ ns : List ℕ,
      nestedIteratedRate σ ns = iteratedRate σ ns.prod
  fta_supplies_nested :
    PrimeMultiplicativeFactorizationStatement →
      SigmaNestedPrimeFactorizationStatement σ
  nested_iff_fta :
    SigmaNestedPrimeFactorizationStatement σ ↔
      PrimeMultiplicativeFactorizationStatement
  nested_to_two_prime_satOr_boundary :
    ∀ factors : List PrimeExponent, ∀ p q : PrimeExponent,
      nestedIteratedRate σ (factors.map (fun r : PrimeExponent => r.1)) =
          satOrField (iteratedRate σ p.1) (iteratedRate σ q.1) ↔
        (factors.map (fun r : PrimeExponent => r.1)).prod = p.1 + q.1
  goldbach_boundary :
    (PrimeMultiplicativeFactorizationStatement →
        SigmaEvenGoldbachStatement σ) ↔
      (PrimeMultiplicativeFactorizationStatement →
        EvenGoldbachStatement)

/-- THEOREM 7: the canonical transfer certificate. -/
theorem ftaSigmaCarrierTransferCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    FtaSigmaCarrierTransferCertificate σ hσ0 hσ1 where
  nested_list_product := nestedIteratedRate_eq_iteratedRate_prod σ
  fta_supplies_nested := fta_to_sigmaNestedPrimeFactorization σ
  nested_iff_fta := sigmaNestedPrimeFactorization_iff_fta_of_mem_Ioo hσ0 hσ1
  nested_to_two_prime_satOr_boundary := by
    intro factors p q
    exact nestedPrimeSigma_eq_twoPrimeSatOr_iff_product_eq_sum_of_mem_Ioo
      hσ0 hσ1 factors p q
  goldbach_boundary :=
    fta_to_sigmaGoldbach_iff_fta_to_goldbach_of_mem_Ioo hσ0 hσ1

end AffineRelaxation
end SaturationMonoid
