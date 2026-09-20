import H0mework.Realization.Fibres.P310

/-!
# Proposition 311: the sigma exponent image is the arithmetic carrier

P303-P310 established the equations:

* `satOr` of effective rates is addition of iteration exponents;
* nested iteration is multiplication of iteration exponents;
* on `0 < σ < 1`, the effective-rate map is faithful.

This file packages those facts as an image-level carrier.  The carrier is the
actual set of effective rates `{r | ∃ n, r = iteratedRate σ n}`.  Its additive
face is represented by serial `satOr`; its multiplicative face is represented
by nested iteration.  On the nondegenerate interval, this carrier is equivalent
to `ℕ`, and the two operations reflect exactly the usual `ℕ` addition and
multiplication.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The image of the natural-number iteration spine inside the sigma carrier. -/
def SigmaExponentImage (σ : K) : Type _ :=
  { r : K // ∃ n : ℕ, r = iteratedRate σ n }

namespace SigmaExponentImage

/-- The effective-rate image point corresponding to an exponent. -/
def ofNat (σ : K) (n : ℕ) : SigmaExponentImage σ :=
  ⟨iteratedRate σ n, ⟨n, rfl⟩⟩

/-- A chosen exponent for an image point.  On `0 < σ < 1` this choice is
unique; outside that interval it is merely a representative. -/
def exponent {σ : K} (r : SigmaExponentImage σ) : ℕ :=
  Classical.choose r.2

/-- The chosen exponent represents the image point. -/
theorem val_eq_iteratedRate_exponent
    {σ : K} (r : SigmaExponentImage σ) :
    r.1 = iteratedRate σ (exponent r) :=
  Classical.choose_spec r.2

/-- Every image point is the `ofNat` point of its chosen exponent. -/
theorem ofNat_exponent_eq
    {σ : K} (r : SigmaExponentImage σ) :
    ofNat σ (exponent r) = r := by
  apply Subtype.ext
  exact (val_eq_iteratedRate_exponent r).symm

/-- On the nondegenerate carrier, the `ofNat` map is injective. -/
theorem ofNat_injective_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Function.Injective (ofNat σ) := by
  intro n m h
  apply iteratedRate_injective_of_mem_Ioo hσ0 hσ1
  exact congrArg Subtype.val h

/-- On the nondegenerate carrier, the chosen exponent of `ofNat n` is `n`. -/
theorem exponent_ofNat_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) (n : ℕ) :
    exponent (ofNat σ n) = n := by
  apply iteratedRate_injective_of_mem_Ioo hσ0 hσ1
  have h := val_eq_iteratedRate_exponent (ofNat σ n)
  simpa [ofNat] using h.symm

/-- The sigma exponent image is equivalent to `ℕ` on `0 < σ < 1`. -/
def equivNatOfMemIoo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaExponentImage σ ≃ ℕ where
  toFun r := exponent r
  invFun n := ofNat σ n
  left_inv := ofNat_exponent_eq
  right_inv := exponent_ofNat_of_mem_Ioo hσ0 hσ1

/-- The additive face of the image carrier: addition of chosen exponents.
Theorem `add_val_eq_satOr` below proves that this is exactly serial `satOr`
on the underlying effective rates. -/
def add {σ : K} (x y : SigmaExponentImage σ) : SigmaExponentImage σ :=
  ofNat σ (exponent x + exponent y)

/-- The multiplicative face of the image carrier: multiplication of chosen
exponents.  Theorem `mul_val_eq_nested` below proves that this is exactly
nested iteration on the underlying effective rates. -/
def mul {σ : K} (x y : SigmaExponentImage σ) : SigmaExponentImage σ :=
  ofNat σ (exponent x * exponent y)

/-- Zero for the additive face. -/
def zero (σ : K) : SigmaExponentImage σ :=
  ofNat σ 0

/-- One for the multiplicative face. -/
def one (σ : K) : SigmaExponentImage σ :=
  ofNat σ 1

/-- THEOREM 1: the image-level additive operation is serial `satOr` on values. -/
theorem add_val_eq_satOr
    {σ : K} (x y : SigmaExponentImage σ) :
    (add x y).1 = satOrField x.1 y.1 := by
  calc
    (add x y).1 = iteratedRate σ (exponent x + exponent y) := rfl
    _ = satOrField (iteratedRate σ (exponent x))
        (iteratedRate σ (exponent y)) := iteratedRate_add σ (exponent x) (exponent y)
    _ = satOrField x.1 y.1 := by
      rw [← val_eq_iteratedRate_exponent x,
        ← val_eq_iteratedRate_exponent y]

/-- THEOREM 2: the image-level multiplicative operation is nested iteration on
values. -/
theorem mul_val_eq_nested
    {σ : K} (x y : SigmaExponentImage σ) :
    (mul x y).1 = iteratedRate x.1 (exponent y) := by
  calc
    (mul x y).1 = iteratedRate σ (exponent x * exponent y) := rfl
    _ = iteratedRate (iteratedRate σ (exponent x)) (exponent y) :=
      (iteratedRate_iteratedRate σ (exponent x) (exponent y)).symm
    _ = iteratedRate x.1 (exponent y) := by
      rw [← val_eq_iteratedRate_exponent x]

/-- THEOREM 3: adding two named exponent points gives the named sum. -/
theorem add_ofNat_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) (n m : ℕ) :
    add (ofNat σ n) (ofNat σ m) = ofNat σ (n + m) := by
  simp [add, exponent_ofNat_of_mem_Ioo hσ0 hσ1]

/-- THEOREM 4: multiplying two named exponent points gives the named product. -/
theorem mul_ofNat_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) (n m : ℕ) :
    mul (ofNat σ n) (ofNat σ m) = ofNat σ (n * m) := by
  simp [mul, exponent_ofNat_of_mem_Ioo hσ0 hσ1]

/-- THEOREM 5: image addition reflects exactly natural-number addition. -/
theorem add_eq_ofNat_iff_add_eq_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n m k : ℕ} :
    add (ofNat σ n) (ofNat σ m) = ofNat σ k ↔ n + m = k := by
  constructor
  · intro h
    apply ofNat_injective_of_mem_Ioo hσ0 hσ1
    calc
      ofNat σ (n + m) = add (ofNat σ n) (ofNat σ m) :=
        (add_ofNat_of_mem_Ioo hσ0 hσ1 n m).symm
      _ = ofNat σ k := h
  · intro h
    rw [← h]
    exact add_ofNat_of_mem_Ioo hσ0 hσ1 n m

/-- THEOREM 6: image multiplication reflects exactly natural-number
multiplication. -/
theorem mul_eq_ofNat_iff_mul_eq_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n m k : ℕ} :
    mul (ofNat σ n) (ofNat σ m) = ofNat σ k ↔ n * m = k := by
  constructor
  · intro h
    apply ofNat_injective_of_mem_Ioo hσ0 hσ1
    calc
      ofNat σ (n * m) = mul (ofNat σ n) (ofNat σ m) :=
        (mul_ofNat_of_mem_Ioo hσ0 hσ1 n m).symm
      _ = ofNat σ k := h
  · intro h
    rw [← h]
    exact mul_ofNat_of_mem_Ioo hσ0 hσ1 n m

/-- THEOREM 7: associativity of image addition, transported from `ℕ`. -/
theorem add_assoc_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x y z : SigmaExponentImage σ) :
    add (add x y) z = add x (add y z) := by
  rw [← ofNat_exponent_eq x, ← ofNat_exponent_eq y, ← ofNat_exponent_eq z]
  simp [add, exponent_ofNat_of_mem_Ioo hσ0 hσ1, Nat.add_assoc]

/-- THEOREM 8: commutativity of image addition, transported from `ℕ`. -/
theorem add_comm_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x y : SigmaExponentImage σ) :
    add x y = add y x := by
  rw [← ofNat_exponent_eq x, ← ofNat_exponent_eq y]
  simp [add, exponent_ofNat_of_mem_Ioo hσ0 hσ1, Nat.add_comm]

/-- THEOREM 9: associativity of image multiplication, transported from `ℕ`. -/
theorem mul_assoc_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x y z : SigmaExponentImage σ) :
    mul (mul x y) z = mul x (mul y z) := by
  rw [← ofNat_exponent_eq x, ← ofNat_exponent_eq y, ← ofNat_exponent_eq z]
  simp [mul, exponent_ofNat_of_mem_Ioo hσ0 hσ1, Nat.mul_assoc]

/-- THEOREM 10: commutativity of image multiplication, transported from `ℕ`. -/
theorem mul_comm_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x y : SigmaExponentImage σ) :
    mul x y = mul y x := by
  rw [← ofNat_exponent_eq x, ← ofNat_exponent_eq y]
  simp [mul, exponent_ofNat_of_mem_Ioo hσ0 hσ1, Nat.mul_comm]

/-- THEOREM 11: left distributivity of the multiplicative face over the
additive face. -/
theorem left_distrib_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x y z : SigmaExponentImage σ) :
    mul x (add y z) = add (mul x y) (mul x z) := by
  rw [← ofNat_exponent_eq x, ← ofNat_exponent_eq y, ← ofNat_exponent_eq z]
  simp [add, mul, exponent_ofNat_of_mem_Ioo hσ0 hσ1, Nat.left_distrib]

/-- THEOREM 12: right distributivity of the multiplicative face over the
additive face. -/
theorem right_distrib_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x y z : SigmaExponentImage σ) :
    mul (add x y) z = add (mul x z) (mul y z) := by
  rw [← ofNat_exponent_eq x, ← ofNat_exponent_eq y, ← ofNat_exponent_eq z]
  simp [add, mul, exponent_ofNat_of_mem_Ioo hσ0 hσ1, Nat.right_distrib]

/-- A compact image-level arithmetic certificate. -/
structure ArithmeticImageCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  carrier_equiv_nat :
    SigmaExponentImage σ ≃ ℕ
  add_is_satOr :
    ∀ x y : SigmaExponentImage σ,
      (add x y).1 = satOrField x.1 y.1
  mul_is_nested :
    ∀ x y : SigmaExponentImage σ,
      (mul x y).1 = iteratedRate x.1 (exponent y)
  add_reflects_nat :
    ∀ n m k : ℕ,
      add (ofNat σ n) (ofNat σ m) = ofNat σ k ↔ n + m = k
  mul_reflects_nat :
    ∀ n m k : ℕ,
      mul (ofNat σ n) (ofNat σ m) = ofNat σ k ↔ n * m = k
  add_assoc :
    ∀ x y z : SigmaExponentImage σ, add (add x y) z = add x (add y z)
  add_comm :
    ∀ x y : SigmaExponentImage σ, add x y = add y x
  mul_assoc :
    ∀ x y z : SigmaExponentImage σ, mul (mul x y) z = mul x (mul y z)
  mul_comm :
    ∀ x y : SigmaExponentImage σ, mul x y = mul y x
  left_distrib :
    ∀ x y z : SigmaExponentImage σ, mul x (add y z) = add (mul x y) (mul x z)
  right_distrib :
    ∀ x y z : SigmaExponentImage σ, mul (add x y) z = add (mul x z) (mul y z)

/-- THEOREM 13: the sigma exponent image carries the transported arithmetic
of `ℕ`; its two faces are concretely `satOr` and nested iteration. -/
def arithmeticImageCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ArithmeticImageCertificate σ hσ0 hσ1 where
  carrier_equiv_nat := equivNatOfMemIoo hσ0 hσ1
  add_is_satOr := add_val_eq_satOr
  mul_is_nested := mul_val_eq_nested
  add_reflects_nat := by
    intro n m k
    exact add_eq_ofNat_iff_add_eq_of_mem_Ioo hσ0 hσ1
  mul_reflects_nat := by
    intro n m k
    exact mul_eq_ofNat_iff_mul_eq_of_mem_Ioo hσ0 hσ1
  add_assoc := add_assoc_of_mem_Ioo hσ0 hσ1
  add_comm := add_comm_of_mem_Ioo hσ0 hσ1
  mul_assoc := mul_assoc_of_mem_Ioo hσ0 hσ1
  mul_comm := mul_comm_of_mem_Ioo hσ0 hσ1
  left_distrib := left_distrib_of_mem_Ioo hσ0 hσ1
  right_distrib := right_distrib_of_mem_Ioo hσ0 hσ1

end SigmaExponentImage

end AffineRelaxation
end SaturationMonoid
