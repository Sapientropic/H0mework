import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Boys
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Coefficients
import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Evaluate

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025 UnifiedOrbitals BasinRefinement SourceGaussianModel Polynomial MeasureTheory
open scoped BigOperators intervalIntegral Topology
noncomputable section

/-- Product centre on one coordinate axis. -/
def pairAxisCentre (s t : Term) (k : Fin 3) : ℚ :=
  rationalProductCentre s.exponent t.exponent (s.centre k) (t.centre k)

/-- Rational Boys argument `γ·∑_k (P_k − C_k)²`. -/
def boysArgument (s t : Term) (C : Fin 3 → ℚ) : ℚ :=
  pairExponent s t * ∑ k : Fin 3, (pairAxisCentre s t k - C k)^2

/-- `X^j`-coefficient of `(a + d·X)^e` over `ℚ`. -/
def linearPowCoeff (a d : ℚ) (e j : ℕ) : ℚ :=
  if j ≤ e then (e.choose j : ℚ) * a^(e-j) * d^j else 0

/-- `X^j`-coefficient of `(1 - X)^t` over `ℚ`. -/
def oneMinusCoeff (t j : ℕ) : ℚ :=
  if j ≤ t then ((-1 : ℚ)^j) * (t.choose j : ℚ) else 0

/-- `X^r`-coefficient of the `Y^m` component of
`(Y + a + d·X)^p · (Y + b + d·X)^q`. -/
def axisInnerCoeff (a b d : ℚ) (p q m r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (m+1),
    (p.choose i : ℚ) * (q.choose (m-i) : ℚ) *
    ∑ r1 ∈ Finset.range (r+1),
      linearPowCoeff a d (p-i) r1 * linearPowCoeff b d (q-(m-i)) (r-r1)

/-- `X^J`-coefficient of the axis polynomial (computable `ℚ` arithmetic). -/
def axisScaledCoeffQ (a b d : ℚ) (gamma : ℚ) (p q J : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (p+q+1),
    rationalMoment gamma m *
      ∑ r ∈ Finset.range (J+1),
        axisInnerCoeff a b d p q m r * oneMinusCoeff (m/2) (J-r)

/-- `Bp` is the two-variable helper `(Y + a + dX)^p (Y + b + dX)^q`. -/
private def axisHelper (a b d : ℚ) (p q : ℕ) : Polynomial (Polynomial ℚ) :=
  (X + C (C a + C d * X))^p * (X + C (C b + C d * X))^q

/-- The axis polynomial in `σ`, from `(Y + a + d·X)^p (Y + b + d·X)^q`. -/
noncomputable def axisScaledPolynomial (a b d : ℚ) (gamma : ℚ) (p q : ℕ) :
    Polynomial ℚ :=
  ∑ m ∈ Finset.range (p+q+1),
    (axisHelper a b d p q).coeff m *
    Polynomial.C (rationalMoment gamma m) * (1 - Polynomial.X)^(m/2)

/-- `((C a + C d·X)^e).coeff j = linearPowCoeff a d e j`. -/
theorem linear_pow_coeff_eval (a d : ℚ) (e j : ℕ) :
    ((Polynomial.C a + Polynomial.C d * Polynomial.X)^e).coeff j =
      linearPowCoeff a d e j := by
  have hsum : (C a + C d * X)^e =
      ∑ i ∈ Finset.range (e+1),
        (C d * X)^i * (C a)^(e-i) * (e.choose i : ℚ[X]) := by
    rw [add_comm (C a) (C d * X), add_pow]
  rw [hsum, finsetSum_coeff]
  have term_coeff : ∀ i : ℕ,
      ((C d * X)^i * (C a)^(e-i) * (e.choose i : ℚ[X])).coeff j =
        (if j = i then d^i else 0) * a^(e-i) * (e.choose i : ℚ) := by
    intro i
    rw [show (C d * X)^i * (C a)^(e-i) * (e.choose i : ℚ[X]) =
        ((C a)^(e-i) * (e.choose i : ℚ[X])) * (C d * X)^i by ring]
    rw [← C_pow, ← C_eq_natCast]
    rw [show (C (a^(e-i)) * C ↑(e.choose i)) = C (a^(e-i) * ↑(e.choose i)) by
      rw [← C_mul]]
    rw [coeff_C_mul, mul_pow, ← C_pow, coeff_C_mul, coeff_X_pow]
    split_ifs with h <;> ring
  simp_rw [term_coeff]
  by_cases hj : j ≤ e
  · rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
      unfold linearPowCoeff
      rw [if_pos hj]; ring
    · intro i _ hij
      rw [if_neg (Ne.symm hij)]; ring
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)) h
  · rw [linearPowCoeff, if_neg hj]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg]
    · ring
    · intro hji
      exact hj (hji ▸ Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- `((1 - X)^t).coeff j = oneMinusCoeff t j`. -/
theorem one_minus_coeff_eval (t j : ℕ) :
    ((1 - Polynomial.X : Polynomial ℚ)^t).coeff j = oneMinusCoeff t j := by
  rw [show (1 - X : ℚ[X]) = C (1 : ℚ) + C (-1 : ℚ) * X by
    simp only [map_one, map_neg]; ring]
  rw [linear_pow_coeff_eval, linearPowCoeff, oneMinusCoeff]
  split_ifs with h
  · simp [mul_comm]
  · rfl

/-- `X^r`-coefficient of the `Y^m` coefficient of
`(Y + C(C a + C d·X))^p (Y + C(C b + C d·X))^q`. -/
theorem axisInnerCoeff_eval (a b d : ℚ) (p q m r : ℕ) :
    ((axisHelper a b d p q).coeff m).coeff r =
      axisInnerCoeff a b d p q m r := by
  unfold axisHelper
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [coeff_X_add_C_pow]
  rw [finsetSum_coeff]
  unfold axisInnerCoeff
  apply Finset.sum_congr rfl
  intro i _
  rw [show (C a + C d*X)^(p-i) * ↑(p.choose i) *
      ((C b + C d*X)^(q-(m-i)) * ↑(q.choose (m-i))) =
      C ((p.choose i : ℚ)*(q.choose (m-i) : ℚ)) *
        ((C a + C d*X)^(p-i) * (C b + C d*X)^(q-(m-i))) by
    rw [← C_eq_natCast, ← C_eq_natCast, C_mul]; ring]
  rw [coeff_C_mul]
  congr 1
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro r1 _
  rw [linear_pow_coeff_eval, linear_pow_coeff_eval]

/-- `X^J`-coefficient of `axisScaledPolynomial`. -/
theorem axisScaledPolynomial_coeff (a b d : ℚ) (gamma : ℚ) (p q J : ℕ) :
    (axisScaledPolynomial a b d gamma p q).coeff J =
      axisScaledCoeffQ a b d gamma p q J := by
  unfold axisScaledPolynomial axisScaledCoeffQ
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m _
  rw [show ((axisHelper a b d p q).coeff m) * C (rationalMoment gamma m) *
        (1 - X)^(m/2) =
      ((axisHelper a b d p q).coeff m * (1 - X)^(m/2)) *
        C (rationalMoment gamma m) by ring]
  rw [coeff_mul_C, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [axisInnerCoeff_eval, one_minus_coeff_eval]
  ring

/-- The per-axis attraction polynomial of a term pair. -/
noncomputable def axisPolynomial (s t : Term) (C : Fin 3 → ℚ) (k : Fin 3) :
    Polynomial ℚ :=
  axisScaledPolynomial (pairAxisCentre s t k - s.centre k)
    (pairAxisCentre s t k - t.centre k) (C k - pairAxisCentre s t k)
    (pairExponent s t) (s.powers k) (t.powers k)

/-- Computable `X^J`-coefficient of `axisPolynomial s t C k`. -/
def axisCoeffQ (s t : Term) (C : Fin 3 → ℚ) (k : Fin 3) (J : ℕ) : ℚ :=
  axisScaledCoeffQ (pairAxisCentre s t k - s.centre k)
    (pairAxisCentre s t k - t.centre k) (C k - pairAxisCentre s t k)
    (pairExponent s t) (s.powers k) (t.powers k) J

theorem axisPolynomial_coeff (s t : Term) (C : Fin 3 → ℚ) (k : Fin 3) (J : ℕ) :
    (axisPolynomial s t C k).coeff J = axisCoeffQ s t C k J :=
  axisScaledPolynomial_coeff _ _ _ _ _ _ _

/-- The three-axis attraction polynomial `∏_k axisPolynomial_k` in `σ`. -/
noncomputable def attractionPolynomial (s t : Term) (C : Fin 3 → ℚ) :
    Polynomial ℚ :=
  ∏ k : Fin 3, axisPolynomial s t C k

/-- `σ^j`-coefficient of `attractionPolynomial`. -/
def attractionCoefficient (s t : Term) (C : Fin 3 → ℚ) (j : ℕ) : ℚ :=
  (attractionPolynomial s t C).coeff j

/-- Degree of the attraction polynomial. -/
noncomputable def attractionDegree (s t : Term) (C : Fin 3 → ℚ) : ℕ :=
  (attractionPolynomial s t C).natDegree

/-- Deterministic coefficient range bound: total angular momentum. -/
def attractionOrder (s t : Term) : ℕ := ∑ k : Fin 3, (s.powers k + t.powers k)

/-- Computable `σ^j`-coefficient of the attraction polynomial. -/
def attractionCoefficientQ (s t : Term) (C : Fin 3 → ℚ) (j : ℕ) : ℚ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j,
    (∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
      axisCoeffQ s t C 0 q.1 * axisCoeffQ s t C 1 q.2) *
      axisCoeffQ s t C 2 p.2

theorem attraction_coefficient_evaluated (s t : Term) (C : Fin 3 → ℚ) (j : ℕ) :
    attractionCoefficient s t C j = attractionCoefficientQ s t C j := by
  unfold attractionCoefficient attractionPolynomial attractionCoefficientQ
  rw [Fin.prod_univ_three, coeff_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [coeff_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro q _
    rw [axisPolynomial_coeff, axisPolynomial_coeff]
  · rw [axisPolynomial_coeff]

/-- `axisInnerCoeff` vanishes beyond the available `X`-degree `p+q−m`. -/
theorem axisInnerCoeff_eq_zero (a b d : ℚ) (p q m r : ℕ)
    (h : p + q - m < r) : axisInnerCoeff a b d p q m r = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : p.choose i = 0
  · simp [hi]
  · by_cases hmi : q.choose (m-i) = 0
    · simp [hmi]
    · have hi' : i ≤ p := by
        by_contra hc
        exact hi (Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hc))
      have hmi' : m - i ≤ q := by
        by_contra hc
        exact hmi (Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hc))
      suffices h0 : (∑ r1 ∈ Finset.range (r+1),
          linearPowCoeff a d (p-i) r1 *
            linearPowCoeff b d (q-(m-i)) (r-r1)) = 0 by
        rw [h0]; ring
      apply Finset.sum_eq_zero
      intro r1 _
      by_cases h3 : r1 ≤ p - i
      · rw [linearPowCoeff, linearPowCoeff, if_pos h3,
          if_neg (by omega : ¬ r - r1 ≤ q - (m - i))]
        ring
      · rw [linearPowCoeff, if_neg h3]
        ring

/-- `axisScaledCoeffQ` vanishes past degree `p+q`. -/
theorem axisScaledCoeffQ_eq_zero (a b d : ℚ) (gamma : ℚ) (p q J : ℕ)
    (hJ : p + q < J) : axisScaledCoeffQ a b d gamma p q J = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  rw [Finset.mem_range] at hm
  suffices inner :
      (∑ r ∈ Finset.range (J+1),
        axisInnerCoeff a b d p q m r * oneMinusCoeff (m/2) (J-r)) = 0 by
    rw [inner]; ring
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : J - r ≤ m / 2
  · rw [axisInnerCoeff_eq_zero a b d p q m r (by omega)]
    ring
  · rw [oneMinusCoeff, if_neg hr]
    ring

/-- Degree bound of one axis polynomial. -/
theorem axisScaledPolynomial_natDegree_le (a b d : ℚ) (gamma : ℚ) (p q : ℕ) :
    (axisScaledPolynomial a b d gamma p q).natDegree ≤ p + q := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [axisScaledPolynomial_coeff, axisScaledCoeffQ_eq_zero a b d gamma p q N hN]

/-- Per-axis degree bound. -/
theorem axisPolynomial_natDegree_le (s t : Term) (C : Fin 3 → ℚ) (k : Fin 3) :
    (axisPolynomial s t C k).natDegree ≤ s.powers k + t.powers k :=
  axisScaledPolynomial_natDegree_le _ _ _ _ _ _

/-- The attraction polynomial degree is bounded by the total angular order. -/
theorem attraction_degree_le (s t : Term) (C : Fin 3 → ℚ) :
    attractionDegree s t C ≤ attractionOrder s t := by
  unfold attractionDegree attractionPolynomial attractionOrder
  calc (∏ k : Fin 3, axisPolynomial s t C k).natDegree
      ≤ ∑ k : Fin 3, (axisPolynomial s t C k).natDegree :=
        natDegree_prod_le Finset.univ _
    _ ≤ ∑ k : Fin 3, (s.powers k + t.powers k) :=
        Finset.sum_le_sum fun k _ => axisPolynomial_natDegree_le s t C k

/-- Coefficients beyond the total angular order vanish. -/
theorem attractionCoefficient_eq_zero_of_order_lt (s t : Term) (C : Fin 3 → ℚ)
    (j : ℕ) (hj : attractionOrder s t < j) :
    attractionCoefficient s t C j = 0 := by
  rw [attractionCoefficient]
  exact coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (attraction_degree_le s t C) hj)

/-- `momentValue (γ+τ) m` rescaled to the base exponent `γ` with `1−σ = γ/(γ+τ)`. -/
theorem momentValue_scaled (γq : ℚ) (τ : ℝ) (hγ : (0:ℝ) < γq) (hτ : 0 < τ) (m : ℕ) :
    momentValue ((γq:ℝ)+τ) m =
      (rationalMoment γq m : ℝ) * (1 - τ/((γq:ℝ)+τ))^(m/2) *
        Real.sqrt (Real.pi/((γq:ℝ)+τ)) := by
  have hG : (0:ℝ) < (γq:ℝ) + τ := add_pos hγ hτ
  have h1σ : (1:ℝ) - τ/((γq:ℝ)+τ) = (γq:ℝ)/((γq:ℝ)+τ) := by
    field_simp [hG.ne']
    ring
  induction m using Nat.twoStepInduction with
  | zero => simp [momentValue, rationalMoment]
  | one => simp [momentValue, rationalMoment]
  | more n hn0 _ =>
      simp only [momentValue]
      rw [hn0]
      rw [show (rationalMoment γq (n+2) : ℚ) =
        (n+1 : ℚ)/(2*γq) * rationalMoment γq n from rfl]
      push_cast
      rw [show (n+2)/2 = n/2 + 1 by omega, pow_succ, h1σ]
      field_simp [hG.ne', hγ.ne']


theorem axisHelper_natDegree_le (a b d : ℚ) (p q : ℕ) :
    (axisHelper a b d p q).natDegree ≤ p + q := by
  unfold axisHelper
  have lin : ∀ f : Polynomial ℚ, (X + C f : Polynomial (Polynomial ℚ)).natDegree ≤ 1 := by
    intro f
    calc (X + C f).natDegree
        ≤ max (natDegree X) (natDegree (C f)) := natDegree_add_le _ _
      _ = 1 := by
          rw [natDegree_X, natDegree_C]
          rfl
  calc (((X + C (C a + C d * X))^p * (X + C (C b + C d * X))^q :
        Polynomial (Polynomial ℚ)).natDegree)
      ≤ natDegree ((X + C (C a + C d * X))^p : Polynomial (Polynomial ℚ)) +
        natDegree ((X + C (C b + C d * X))^q : Polynomial (Polynomial ℚ)) :=
        natDegree_mul_le
    _ ≤ p + q := by
        have hp : natDegree ((X + C (C a + C d * X))^p : Polynomial (Polynomial ℚ))
            ≤ p := by
          calc natDegree ((X + C (C a + C d * X))^p : Polynomial (Polynomial ℚ))
              ≤ p * natDegree (X + C (C a + C d * X) :
                Polynomial (Polynomial ℚ)) := natDegree_pow_le
            _ ≤ p * 1 := Nat.mul_le_mul_left p (lin _)
            _ = p := mul_one p
        have hq : natDegree ((X + C (C b + C d * X))^q : Polynomial (Polynomial ℚ))
            ≤ q := by
          calc natDegree ((X + C (C b + C d * X))^q : Polynomial (Polynomial ℚ))
              ≤ q * natDegree (X + C (C b + C d * X) :
                Polynomial (Polynomial ℚ)) := natDegree_pow_le
            _ ≤ q * 1 := Nat.mul_le_mul_left q (lin _)
            _ = q := mul_one q
        linarith

/-- Evaluation of `axisHelper` splits into `Y`-coefficients. -/
theorem axisHelper_eval₂ (a b d : ℚ) (p q : ℕ) (σ y : ℝ) :
    (axisHelper a b d p q).eval₂ (eval₂RingHom (Rat.castHom ℝ) σ) y =
      ∑ m ∈ Finset.range (p+q+1),
        ((axisHelper a b d p q).coeff m).eval₂ (Rat.castHom ℝ) σ * y^m := by
  rw [eval₂_eq_sum]
  have hsupp : (axisHelper a b d p q).support ⊆ Finset.range (p+q+1) := by
    intro i hi
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((le_natDegree_of_mem_supp i hi).trans
      (axisHelper_natDegree_le a b d p q))
  rw [Polynomial.sum_eq_of_subset _ (by intro i; simp) hsupp]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Per-axis attraction integral in closed form:
`∫ sG(α,A,p)·sG(β,B,q)·e^{−τ(x−c)²} =
  e^{−pen}·e^{−γτ/(γ+τ)·(P−c)²}·√(π/(γ+τ))·axisPoly(σ)` with `σ = τ/(γ+τ)`. -/
theorem axis_attraction_integral (α β : ℚ) (hα : 0 < α) (hβ : 0 < β)
    (A B c : ℚ) (p q : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    (∫ x : ℝ, shiftedGaussian (α:ℝ) (A:ℝ) p x * shiftedGaussian (β:ℝ) (B:ℝ) q x *
      Real.exp (-τ*(x-((c : ℚ):ℝ))^2)) =
    Real.exp (-(productPenalty (α:ℝ) (β:ℝ) (A:ℝ) (B:ℝ))) *
      (Real.exp (-(((α:ℝ)+(β:ℝ))*τ/((α:ℝ)+(β:ℝ)+τ))*
        (((rationalProductCentre α β A B : ℚ):ℝ)-((c : ℚ):ℝ))^2) *
      Real.sqrt (Real.pi/((α:ℝ)+(β:ℝ)+τ)) *
      ((axisScaledPolynomial
        ((rationalProductCentre α β A B : ℚ) - A)
        ((rationalProductCentre α β A B : ℚ) - B)
        (c - rationalProductCentre α β A B) (α+β) p q).eval₂ (Rat.castHom ℝ)
        (τ/((α:ℝ)+(β:ℝ)+τ)))) := by
  have hαr : (0:ℝ) < α := by exact_mod_cast hα
  have hβr : (0:ℝ) < β := by exact_mod_cast hβ
  set G : ℝ := (α:ℝ) + (β:ℝ) with hGdef
  have hG : 0 < G := add_pos hαr hβr
  have hGτ : (0:ℝ) < G + τ := add_pos hG hτ
  set P : ℚ := rationalProductCentre α β A B with hPdef
  set σ : ℝ := τ/(G+τ) with hσdef
  set Q : ℝ := productCentre G τ (P:ℝ) ((c:ℚ):ℝ) with hQdef
  set pen : ℝ := productPenalty (α:ℝ) (β:ℝ) (A:ℝ) (B:ℝ) with hpendef
  set pen2 : ℝ := productPenalty G τ (P:ℝ) ((c:ℚ):ℝ) with hpen2def
  set Bp : Polynomial (Polynomial ℚ) := axisHelper (P - A) (P - B) (c - P) p q
    with hBpdef
  have hGcast : G = ((α+β : ℚ) : ℝ) := by push_cast [G]; rfl
  have hPcast : (P:ℝ) = productCentre (α:ℝ) (β:ℝ) (A:ℝ) (B:ℝ) := by
    simp only [P, rationalProductCentre, productCentre]
    push_cast
    field_simp [hG.ne']
  have hQr : Q - (P:ℝ) = σ*(((c:ℚ):ℝ)-(P:ℝ)) := by
    simp only [Q, σ, productCentre]
    field_simp [hGτ.ne']
    ring
  have hexp : ∀ x : ℝ, Real.exp (-G*(x-(P:ℝ))^2) * Real.exp (-τ*(x-((c:ℚ):ℝ))^2) =
      Real.exp (-pen2) * Real.exp (-(G+τ)*(x-Q)^2) := by
    intro x
    have hcs := completed_square G τ (P:ℝ) ((c:ℚ):ℝ) x hGτ
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have hpen2u : pen2 = G*τ/(G+τ) * ((P:ℝ)-(c:ℚ):ℝ)^2 := by
      simp only [pen2, productPenalty]
    linarith [hcs]
  have eval_eq : ∀ y : ℝ,
      ((rationalProductPolynomial α β A B p q).map (Rat.castHom ℝ)).eval
        (y + σ*(((c:ℚ):ℝ)-(P:ℝ))) =
      Bp.eval₂ (eval₂RingHom (Rat.castHom ℝ) σ) y := by
    intro y
    simp only [Bp, axisHelper, eval₂_mul, eval₂_pow, eval₂_add, eval₂_X, eval₂_C,
      coe_eval₂RingHom, Rat.coe_castHom]
    simp only [rationalProductPolynomial, eval_map, eval₂_mul, eval₂_pow,
      eval₂_add, eval₂_X, eval₂_C, Rat.coe_castHom]
    have base1 : y + σ*(((c:ℚ):ℝ)-(P:ℝ)) + ((P-A:ℚ):ℝ) =
        y + (((P-A:ℚ):ℝ) + ((c-P):ℝ)*σ) := by push_cast; ring
    have base2 : y + σ*(((c:ℚ):ℝ)-(P:ℝ)) + ((P-B:ℚ):ℝ) =
        y + (((P-B:ℚ):ℝ) + ((c-P):ℝ)*σ) := by push_cast; ring
    rw [base1, base2]
    push_cast
    rfl
  set rppR : Polynomial ℝ :=
    (rationalProductPolynomial α β A B p q).map (Rat.castHom ℝ) with hrppR
  set F : ℝ → ℝ := fun y => rppR.eval (y + (Q-(P:ℝ))) * Real.exp (-(G+τ)*y^2)
    with hFdef
  have core : (∫ x : ℝ, rppR.eval (x - (P:ℝ)) * Real.exp (-(G+τ)*(x-Q)^2)) =
      ∑ m ∈ Finset.range (p+q+1),
        (Bp.coeff m).eval₂ (Rat.castHom ℝ) σ * momentValue (G+τ) m := by
    have key : (∫ x : ℝ, rppR.eval (x - (P:ℝ)) * Real.exp (-(G+τ)*(x-Q)^2)) =
        ∫ x : ℝ, F (x - Q) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hFdef]
      have hx : x - (P:ℝ) = (x - Q) + (Q - (P:ℝ)) := by ring
      rw [hx]
    rw [key, integral_sub_right_eq_self _ Q]
    have step : ∀ y : ℝ, F y =
        ∑ m ∈ Finset.range (p+q+1), (Bp.coeff m).eval₂ (Rat.castHom ℝ) σ *
          (y^m * Real.exp (-(G+τ)*y^2)) := by
      intro y
      rw [hFdef]
      dsimp only
      rw [hQr, eval_eq y, hBpdef, axisHelper_eval₂, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      ring_nf
    simp_rw [step]
    rw [integral_finsetSum _ (fun m _ => (moment_integrable (G+τ) hGτ m).const_mul _)]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_const_mul]
    rw [show (∫ x : ℝ, x^m * Real.exp (-(G+τ)*x^2)) = moment (G+τ) m from rfl]
    rw [moment_evaluated (G+τ) hGτ m]
  calc ∫ x : ℝ, shiftedGaussian (α:ℝ) (A:ℝ) p x * shiftedGaussian (β:ℝ) (B:ℝ) q x *
        Real.exp (-τ*(x-((c:ℚ):ℝ))^2)
      = ∫ x : ℝ, Real.exp (-pen) * Real.exp (-pen2) *
          (((rationalProductPolynomial α β A B p q).map (Rat.castHom ℝ)).eval
            (x - (P:ℝ)) * Real.exp (-(G+τ)*(x-Q)^2)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [product_gaussian (α:ℝ) (β:ℝ) (A:ℝ) (B:ℝ) hG p q x]
        simp only [GaussianPrimitive.gaussian]
        rw [product_polynomial_rational α β A B p q]
        rw [← hPcast, ← hGdef]
        rw [← hrppR]
        rw [show Real.exp (-pen) * (rppR.eval (x - (P:ℝ)) *
              Real.exp (-G*(x-(P:ℝ))^2)) * Real.exp (-τ*(x-(c:ℚ):ℝ)^2) =
            (Real.exp (-pen) * rppR.eval (x - (P:ℝ))) *
              (Real.exp (-G*(x-(P:ℝ))^2) * Real.exp (-τ*(x-(c:ℚ):ℝ)^2)) by
          ring]
        rw [hexp x]
        ring_nf
    _ = Real.exp (-pen) * Real.exp (-pen2) *
          ∫ x : ℝ, ((rationalProductPolynomial α β A B p q).map (Rat.castHom ℝ)).eval
            (x - (P:ℝ)) * Real.exp (-(G+τ)*(x-Q)^2) := by
        rw [integral_const_mul]
    _ = Real.exp (-pen) * Real.exp (-pen2) *
          ∑ m ∈ Finset.range (p+q+1), (Bp.coeff m).eval₂ (Rat.castHom ℝ) σ *
            momentValue (G+τ) m := by
        rw [← hrppR, core]
    _ = Real.exp (-pen) * Real.exp (-pen2) *
          (Real.sqrt (Real.pi/(G+τ)) *
            ∑ m ∈ Finset.range (p+q+1), (Bp.coeff m).eval₂ (Rat.castHom ℝ) σ *
              ((rationalMoment (α+β) m : ℝ) *
                (1 - σ)^(m/2))) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        have hscaled := momentValue_scaled (α+β) τ
          (by exact_mod_cast add_pos hα hβ) hτ m
        rw [← hGcast, ← hσdef] at hscaled
        rw [hscaled]
        ring_nf
    _ = Real.exp (-pen) * Real.exp (-pen2) *
          (Real.sqrt (Real.pi/(G+τ)) *
            ((axisScaledPolynomial
              ((rationalProductCentre α β A B : ℚ) - A)
              ((rationalProductCentre α β A B : ℚ) - B)
              (c - rationalProductCentre α β A B) (α+β) p q).eval₂ (Rat.castHom ℝ)
              σ)) := by
        congr 1
        congr 1
        unfold axisScaledPolynomial
        rw [← hBpdef]
        rw [← coe_eval₂RingHom, map_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [coe_eval₂RingHom]
        rw [eval₂_mul, eval₂_mul, eval₂_pow, eval₂_sub, eval₂_one, eval₂_X,
          eval₂_C]
        simp only [Rat.coe_castHom]
        ring_nf
    _ = _ := by
        have hpen2u : pen2 = G*τ/(G+τ) * ((P:ℝ)-(c:ℚ):ℝ)^2 := by
          simp only [pen2, productPenalty]
        rw [hpen2u, hPdef, hσdef, hGdef, hpendef]
        ring_nf
