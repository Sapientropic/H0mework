import H0mework.Arithmetic.PrimeProjection.P308

/-!
# Proposition 309: faithful arithmetic on the nondegenerate sigma carrier

P303 proved the transport laws:

* serial `satOr` composition is addition of iteration exponents;
* iteration-of-iteration is multiplication of iteration exponents.

P307 proved that the effective-rate map is injective on the intended
nondegenerate carrier `0 < σ < 1`.  P308 used that injectivity to show that
carrier-Goldbach is exactly ordinary Goldbach.

This file packages the general principle behind that boundary: on `0 < σ < 1`,
the sigma carrier faithfully reflects the natural-number arithmetic spine.
Carrier equalities obtained from the additive or multiplicative face are true
if and only if the corresponding exponent equations are true.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 1: on `0 < σ < 1`, equality of effective rates is exactly equality
of iteration exponents. -/
theorem iteratedRate_eq_iff_exponent_eq_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n m : ℕ} :
    iteratedRate σ n = iteratedRate σ m ↔ n = m := by
  constructor
  · intro h
    exact iteratedRate_injective_of_mem_Ioo hσ0 hσ1 h
  · intro h
    rw [h]

/-- THEOREM 2: the serial `satOr` face faithfully reflects addition of
iteration exponents. -/
theorem satOr_iteratedRate_eq_iff_add_eq_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n m k : ℕ} :
    satOrField (iteratedRate σ n) (iteratedRate σ m) =
        iteratedRate σ k ↔
      n + m = k := by
  constructor
  · intro h
    apply iteratedRate_injective_of_mem_Ioo hσ0 hσ1
    calc
      iteratedRate σ (n + m) =
          satOrField (iteratedRate σ n) (iteratedRate σ m) :=
        iteratedRate_add σ n m
      _ = iteratedRate σ k := h
  · intro h
    rw [← h]
    exact (iteratedRate_add σ n m).symm

/-- THEOREM 3: the iteration-of-iteration face faithfully reflects
multiplication of iteration exponents. -/
theorem iteratedRate_iteratedRate_eq_iff_mul_eq_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n m k : ℕ} :
    iteratedRate (iteratedRate σ n) m =
        iteratedRate σ k ↔
      n * m = k := by
  constructor
  · intro h
    apply iteratedRate_injective_of_mem_Ioo hσ0 hσ1
    calc
      iteratedRate σ (n * m) =
          iteratedRate (iteratedRate σ n) m :=
        (iteratedRate_iteratedRate σ n m).symm
      _ = iteratedRate σ k := h
  · intro h
    rw [← h]
    exact iteratedRate_iteratedRate σ n m

/-- THEOREM 4: a carrier equality between an additive face and a
multiplicative face is exactly the corresponding semiring equation on
exponents. -/
theorem satOr_eq_nested_iteratedRate_iff_add_eq_mul_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {a b c d : ℕ} :
    satOrField (iteratedRate σ a) (iteratedRate σ b) =
        iteratedRate (iteratedRate σ c) d ↔
      a + b = c * d := by
  constructor
  · intro h
    apply iteratedRate_injective_of_mem_Ioo hσ0 hσ1
    calc
      iteratedRate σ (a + b) =
          satOrField (iteratedRate σ a) (iteratedRate σ b) :=
        iteratedRate_add σ a b
      _ = iteratedRate (iteratedRate σ c) d := h
      _ = iteratedRate σ (c * d) := iteratedRate_iteratedRate σ c d
  · intro h
    calc
      satOrField (iteratedRate σ a) (iteratedRate σ b) =
          iteratedRate σ (a + b) :=
        (iteratedRate_add σ a b).symm
      _ = iteratedRate σ (c * d) := by rw [h]
      _ = iteratedRate (iteratedRate σ c) d :=
        (iteratedRate_iteratedRate σ c d).symm

/-- THEOREM 5: the `satOr` face and the nested-iteration face share a carrier,
but the shared carrier is faithful rather than collapsing addition into
multiplication.  Any bridge from multiplicative factorization to additive
two-prime decomposition must therefore be a genuine exponent-side bridge. -/
theorem carrier_add_mul_bridge_reflects_to_exponents_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (∀ a b c d : ℕ,
        satOrField (iteratedRate σ a) (iteratedRate σ b) =
            iteratedRate (iteratedRate σ c) d →
          a + b = c * d) := by
  intro a b c d h
  exact (satOr_eq_nested_iteratedRate_iff_add_eq_mul_of_mem_Ioo
    hσ0 hσ1).mp h

/-- A compact certificate for the faithful arithmetic spine on the
nondegenerate sigma carrier. -/
structure SigmaCarrierArithmeticFaithfulnessCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  injective :
    Function.Injective (fun n : ℕ => iteratedRate σ n)
  equality_reflects_exponents :
    ∀ n m : ℕ,
      iteratedRate σ n = iteratedRate σ m ↔ n = m
  serial_add_reflection :
    ∀ n m k : ℕ,
      satOrField (iteratedRate σ n) (iteratedRate σ m) =
          iteratedRate σ k ↔
        n + m = k
  nested_mul_reflection :
    ∀ n m k : ℕ,
      iteratedRate (iteratedRate σ n) m =
          iteratedRate σ k ↔
        n * m = k
  add_mul_face_reflection :
    ∀ a b c d : ℕ,
      satOrField (iteratedRate σ a) (iteratedRate σ b) =
          iteratedRate (iteratedRate σ c) d ↔
        a + b = c * d
  fta_bridge_reduces_to_goldbach :
    PrimeMultiplicativeFactorizationStatement →
      ((PrimeMultiplicativeFactorizationStatement →
          SigmaEvenGoldbachStatement σ) ↔
        EvenGoldbachStatement)

/-- THEOREM 6: the canonical faithful arithmetic certificate on `0 < σ < 1`. -/
theorem sigmaCarrierArithmeticFaithfulnessCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaCarrierArithmeticFaithfulnessCertificate σ hσ0 hσ1 where
  injective := iteratedRate_injective_of_mem_Ioo hσ0 hσ1
  equality_reflects_exponents := by
    intro n m
    exact iteratedRate_eq_iff_exponent_eq_of_mem_Ioo hσ0 hσ1
  serial_add_reflection := by
    intro n m k
    exact satOr_iteratedRate_eq_iff_add_eq_of_mem_Ioo hσ0 hσ1
  nested_mul_reflection := by
    intro n m k
    exact iteratedRate_iteratedRate_eq_iff_mul_eq_of_mem_Ioo hσ0 hσ1
  add_mul_face_reflection := by
    intro a b c d
    exact satOr_eq_nested_iteratedRate_iff_add_eq_mul_of_mem_Ioo hσ0 hσ1
  fta_bridge_reduces_to_goldbach := by
    intro hfta
    exact fta_bridge_reduces_to_goldbach_of_mem_Ioo hσ0 hσ1 hfta

end AffineRelaxation
end SaturationMonoid
