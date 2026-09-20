import H0mework.Realization.Residual.P326

/-!
# Proposition 327: FTA transfers to nested headroom powers, not length two

P326 rewrote Goldbach as a length-two factorization statement in H-space:

`h_(2n) = h_p * h_q`.

This file records the companion statement for FTA.  Multiplicative prime
factorization of an exponent does transfer to H-space, but it transfers to the
nested-power face:

`h_n = (((h_1)^p1)^p2 ...)^pk`

when `n = p1 * p2 * ... * pk`.

Thus FTA and Goldbach live on two different H-space factorization shapes:

* FTA supplies a nested-power decomposition whose exponents multiply;
* Goldbach asks for a length-two ordinary H-space product whose exponents add.

The bridge between them is exactly the arithmetic equation

`product factors = p + q`.

Boundary: this is not Goldbach.  It proves the coordinate-correct statement
that converting an FTA-style nested headroom decomposition into a length-two
prime-headroom product is precisely a Goldbach-strength additive bridge.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Nested powers in H-space -/

/-- Iterated exponentiation starting from a headroom value. -/
def nestedHeadroomPowerFrom : K -> List ℕ -> K
  | h, [] => h
  | h, n :: ns => nestedHeadroomPowerFrom (h ^ n) ns

/-- The H-space nested-power face generated from the one-step headroom. -/
def nestedHeadroomPower (σ : K) (ns : List ℕ) : K :=
  nestedHeadroomPowerFrom (headroomPower σ 1) ns

@[simp] theorem nestedHeadroomPowerFrom_nil (h : K) :
    nestedHeadroomPowerFrom h [] = h := rfl

@[simp] theorem nestedHeadroomPowerFrom_cons (h : K) (n : ℕ) (ns : List ℕ) :
    nestedHeadroomPowerFrom h (n :: ns) =
      nestedHeadroomPowerFrom (h ^ n) ns := rfl

@[simp] theorem nestedHeadroomPower_nil (σ : K) :
    nestedHeadroomPower σ [] = headroomPower σ 1 := rfl

/-- THEOREM 1: nested headroom powers multiply their exponents. -/
theorem nestedHeadroomPowerFrom_eq_headroomPower_mul_prod
    (σ : K) (a : ℕ) (ns : List ℕ) :
    nestedHeadroomPowerFrom (headroomPower σ a) ns =
      headroomPower σ (a * ns.prod) := by
  induction ns generalizing a with
  | nil =>
      simp [nestedHeadroomPowerFrom]
  | cons n ns ih =>
      simp [nestedHeadroomPowerFrom]
      rw [headroomPower_pow]
      rw [ih (a * n)]
      rw [Nat.mul_assoc]

/-- THEOREM 2: nested H-space powers from `h_1` are exactly headroom at the
product of the listed exponents. -/
theorem nestedHeadroomPower_eq_headroomPower_prod
    (σ : K) (ns : List ℕ) :
    nestedHeadroomPower σ ns = headroomPower σ ns.prod := by
  have h :=
    nestedHeadroomPowerFrom_eq_headroomPower_mul_prod σ 1 ns
  simpa [nestedHeadroomPower] using h

/-! ## FTA-shaped nested headroom decomposition -/

/-- A prime nested-headroom decomposition: `h_n` is obtained by nested
exponentiation along a list of prime exponents. -/
def HasPrimeNestedHeadroomDecomposition
    (σ : K) (n : ℕ) : Prop :=
  ∃ factors : List PrimeExponent,
    nestedHeadroomPower σ (factors.map (fun p : PrimeExponent => p.1)) =
      headroomPower σ n

/-- Global nested-headroom prime factorization. -/
def HeadroomNestedPrimeFactorizationStatement
    (σ : K) : Prop :=
  ∀ n : ℕ, 2 ≤ n -> HasPrimeNestedHeadroomDecomposition σ n

/-- THEOREM 3: ordinary prime multiplicative factorization transports to
H-space as nested headroom powers. -/
theorem headroomNestedPrimeDecomposition_of_primeFactorization
    (σ : K) {n : ℕ}
    (h : HasPrimeMultiplicativeFactorization n) :
    HasPrimeNestedHeadroomDecomposition σ n := by
  rcases h with ⟨factors, hn⟩
  refine ⟨factors, ?_⟩
  rw [nestedHeadroomPower_eq_headroomPower_prod, ← hn]

/-- THEOREM 4: FTA supplies the full nested-headroom factorization statement.
This is the H-space face that FTA genuinely owns. -/
theorem fta_to_headroomNestedPrimeFactorization
    (σ : K) :
    PrimeMultiplicativeFactorizationStatement ->
      HeadroomNestedPrimeFactorizationStatement σ := by
  intro hfta n hn
  exact headroomNestedPrimeDecomposition_of_primeFactorization σ (hfta n hn)

/-- THEOREM 5: on the nondegenerate salience interval, nested H-space prime
factorization is exactly ordinary multiplicative prime factorization. -/
theorem headroomNestedPrimeDecomposition_iff_primeFactorization_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n : ℕ} :
    HasPrimeNestedHeadroomDecomposition σ n ↔
      HasPrimeMultiplicativeFactorization n := by
  constructor
  · intro h
    rcases h with ⟨factors, hhead⟩
    refine ⟨factors, ?_⟩
    have hprod :
        (factors.map (fun p : PrimeExponent => p.1)).prod = n := by
      apply headroomPower_injective_of_mem_Ioo hσ0 hσ1
      calc
        headroomPower σ (factors.map (fun p : PrimeExponent => p.1)).prod =
            nestedHeadroomPower σ
              (factors.map (fun p : PrimeExponent => p.1)) :=
          (nestedHeadroomPower_eq_headroomPower_prod σ
            (factors.map (fun p : PrimeExponent => p.1))).symm
        _ = headroomPower σ n := hhead
    exact hprod.symm
  · intro h
    exact headroomNestedPrimeDecomposition_of_primeFactorization σ h

/-- THEOREM 6: the global nested-headroom statement is equivalent to the
FTA-shaped multiplicative statement on `0 < σ < 1`. -/
theorem headroomNestedPrimeFactorization_iff_fta_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    HeadroomNestedPrimeFactorizationStatement σ ↔
      PrimeMultiplicativeFactorizationStatement := by
  constructor
  · intro h n hn
    exact (headroomNestedPrimeDecomposition_iff_primeFactorization_of_mem_Ioo
      hσ0 hσ1).mp (h n hn)
  · intro h
    exact fta_to_headroomNestedPrimeFactorization σ h

/-! ## The exact boundary between FTA and length-two Goldbach -/

/-- THEOREM 7: converting a nested FTA-shaped H-space decomposition into a
length-two prime-headroom product is exactly the exponent equation
`product factors = p + q`.

This is the H-space version of P310's boundary theorem. -/
theorem nestedPrimeHeadroom_eq_twoPrimeProduct_iff_product_eq_sum_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (factors : List PrimeExponent) (p q : PrimeExponent) :
    nestedHeadroomPower σ (factors.map (fun r : PrimeExponent => r.1)) =
        headroomPower σ p.1 * headroomPower σ q.1 ↔
      (factors.map (fun r : PrimeExponent => r.1)).prod = p.1 + q.1 := by
  constructor
  · intro h
    apply headroomPower_injective_of_mem_Ioo hσ0 hσ1
    calc
      headroomPower σ (factors.map (fun r : PrimeExponent => r.1)).prod =
          nestedHeadroomPower σ
            (factors.map (fun r : PrimeExponent => r.1)) :=
        (nestedHeadroomPower_eq_headroomPower_prod σ
          (factors.map (fun r : PrimeExponent => r.1))).symm
      _ = headroomPower σ p.1 * headroomPower σ q.1 := h
      _ = headroomPower σ (p.1 + q.1) :=
        (headroomPower_mul σ p.1 q.1).symm
  · intro h
    calc
      nestedHeadroomPower σ (factors.map (fun r : PrimeExponent => r.1)) =
          headroomPower σ (factors.map (fun r : PrimeExponent => r.1)).prod :=
        nestedHeadroomPower_eq_headroomPower_prod σ
          (factors.map (fun r : PrimeExponent => r.1))
      _ = headroomPower σ (p.1 + q.1) := by rw [h]
      _ = headroomPower σ p.1 * headroomPower σ q.1 :=
        headroomPower_mul σ p.1 q.1

/-- THEOREM 8: FTA gives nested H-space factorization, but a theorem that
turns FTA into length-two H-space factorization is still exactly a theorem
that turns FTA into ordinary Goldbach. -/
theorem fta_to_headroomLengthTwo_iff_fta_to_goldbach_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (PrimeMultiplicativeFactorizationStatement ->
        (∀ n : ℕ, 2 ≤ n -> HeadroomPrimeTwoFactorization σ (2 * n))) ↔
      (PrimeMultiplicativeFactorizationStatement ->
        EvenGoldbachStatement) := by
  constructor
  · intro h hfta
    exact (headroomEvenLengthTwo_iff_evenGoldbach_of_mem_Ioo
      hσ0 hσ1).mp (h hfta)
  · intro h hfta
    exact (headroomEvenLengthTwo_iff_evenGoldbach_of_mem_Ioo
      hσ0 hσ1).mpr (h hfta)

/-- A compact certificate for the H-space FTA/Goldbach boundary. -/
structure HeadroomFtaBoundaryCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  nested_power_product :
    ∀ ns : List ℕ,
      nestedHeadroomPower σ ns = headroomPower σ ns.prod
  fta_supplies_nested_headroom :
    PrimeMultiplicativeFactorizationStatement ->
      HeadroomNestedPrimeFactorizationStatement σ
  nested_headroom_iff_fta :
    HeadroomNestedPrimeFactorizationStatement σ ↔
      PrimeMultiplicativeFactorizationStatement
  nested_to_length_two_boundary :
    ∀ factors : List PrimeExponent, ∀ p q : PrimeExponent,
      nestedHeadroomPower σ (factors.map (fun r : PrimeExponent => r.1)) =
          headroomPower σ p.1 * headroomPower σ q.1 ↔
        (factors.map (fun r : PrimeExponent => r.1)).prod = p.1 + q.1
  fta_to_length_two_iff_goldbach :
    (PrimeMultiplicativeFactorizationStatement ->
        (∀ n : ℕ, 2 ≤ n -> HeadroomPrimeTwoFactorization σ (2 * n))) ↔
      (PrimeMultiplicativeFactorizationStatement ->
        EvenGoldbachStatement)

/-- THEOREM 9: the canonical H-space FTA boundary certificate. -/
theorem headroomFtaBoundaryCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    HeadroomFtaBoundaryCertificate σ hσ0 hσ1 where
  nested_power_product := nestedHeadroomPower_eq_headroomPower_prod σ
  fta_supplies_nested_headroom :=
    fta_to_headroomNestedPrimeFactorization σ
  nested_headroom_iff_fta :=
    headroomNestedPrimeFactorization_iff_fta_of_mem_Ioo hσ0 hσ1
  nested_to_length_two_boundary := by
    intro factors p q
    exact nestedPrimeHeadroom_eq_twoPrimeProduct_iff_product_eq_sum_of_mem_Ioo
      hσ0 hσ1 factors p q
  fta_to_length_two_iff_goldbach :=
    fta_to_headroomLengthTwo_iff_fta_to_goldbach_of_mem_Ioo hσ0 hσ1

end AffineRelaxation
end SaturationMonoid
