import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!
# Actual division-x semantics for arbitrary Weierstrass curves

This module begins by closing the missing actual semantics of Mathlib's
generic addition-and-subtraction map on symmetric x-coordinates.  It is intentionally
source-native and does not import any fixed-curve development.
-/

open scoped Polynomial

noncomputable section

namespace SaturationMonoid.UniversalBSDWeierstrassDivisionXIdentity

open MvPolynomial
open WeierstrassCurve
open WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K)

/-- The generic Kummer biquadratic is the product of the x-coordinates of
`P+Q` and `P-Q`, with the canonical secant denominator. -/
theorem kummerBiquadratic_differentialAddX
    {x₁ y₁ x₂ y₂ : K}
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) *
      W.toAffine.addX x₁ x₂
        (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) *
      (x₁ - x₂) ^ 2 =
        x₁ ^ 2 * x₂ ^ 2 - W.b₄ * x₁ * x₂ - W.b₆ * (x₁ + x₂) - W.b₈ := by
  rw [W.toAffine.slope_of_X_ne hx,
    W.toAffine.slope_of_X_ne (y₁ := y₁) (y₂ := W.toAffine.negY x₂ y₂) hx]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
  field_simp [sub_ne_zero.mpr hx]
  have heq₁ := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁
  have heq₂ := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp h₂
  rw [WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination
    (W.a₁ ^ 2 * x₁ * x₂ - W.a₁ ^ 2 * x₂ ^ 2 + W.a₁ * W.a₃ * x₁ -
      W.a₁ * W.a₃ * x₂ + W.a₁ * x₁ * y₁ - 2 * W.a₁ * x₂ * y₂ -
      W.a₂ * x₁ ^ 2 + 4 * W.a₂ * x₁ * x₂ - 2 * W.a₂ * x₂ ^ 2 +
      W.a₃ * y₁ - 2 * W.a₃ * y₂ + W.a₄ * x₁ + W.a₆ - x₁ ^ 3 +
      2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 2 * x₂ ^ 3 + y₁ ^ 2 -
      2 * y₂ ^ 2) * heq₁ +
    (-W.a₁ ^ 2 * x₁ ^ 2 + W.a₁ ^ 2 * x₁ * x₂ - W.a₁ * W.a₃ * x₁ +
      W.a₁ * W.a₃ * x₂ + W.a₁ * x₂ * y₂ - 4 * W.a₂ * x₁ ^ 2 +
      4 * W.a₂ * x₁ * x₂ - W.a₂ * x₂ ^ 2 + W.a₃ * y₂ - 2 * W.a₄ * x₁ +
      W.a₄ * x₂ - W.a₆ - 4 * x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ +
      2 * x₁ * x₂ ^ 2 - x₂ ^ 3 + y₂ ^ 2) * heq₂

/-- The second Kummer biquadratic is the trace of the two differential additions. -/
theorem kummerBiquadratic_differentialAddX_trace
    {x₁ y₁ x₂ y₂ : K}
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) +
      W.toAffine.addX x₁ x₂
        (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) *
      (x₁ - x₂) ^ 2 =
        2 * (x₁ + x₂) * (x₁ * x₂) + W.b₂ * (x₁ * x₂) +
          W.b₄ * (x₁ + x₂) + W.b₆ := by
  rw [W.toAffine.slope_of_X_ne hx,
    W.toAffine.slope_of_X_ne (y₁ := y₁) (y₂ := W.toAffine.negY x₂ y₂) hx]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
  field_simp [sub_ne_zero.mpr hx]
  have heq₁ := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁
  have heq₂ := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp h₂
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination 2 * heq₁ + 2 * heq₂

omit [DecidableEq K] in
@[simp] theorem addSubMap_eval_zero (s t u : K) :
    (W.addSubMap 0).eval ![s, t, u] =
      s ^ 2 - W.b₄ * s * u - W.b₆ * t * u - W.b₈ * u ^ 2 := by
  simp [addSubMap]

omit [DecidableEq K] in
@[simp] theorem addSubMap_eval_one (s t u : K) :
    (W.addSubMap 1).eval ![s, t, u] =
      2 * t * s + W.b₂ * s * u + W.b₄ * t * u + W.b₆ * u ^ 2 := by
  simp [addSubMap]

omit [DecidableEq K] in
@[simp] theorem addSubMap_eval_two (s t u : K) :
    (W.addSubMap 2).eval ![s, t, u] = t ^ 2 - 4 * s * u := by
  simp [addSubMap]

/-- On two affine points with distinct x-coordinates, `addSubMap` is exactly the
addition/subtraction map, with the canonical scale `(x₁-x₂)²`. -/
theorem addSubMap_eval_some_some_of_X_ne
    {x₁ x₂ y₁ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    let xp := W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)
    let xm := W.toAffine.addX x₁ x₂
      (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))
    (fun i => (W.addSubMap i).eval ![x₁ * x₂, x₁ + x₂, 1]) =
      (x₁ - x₂) ^ 2 • ![xp * xm, xp + xm, 1] := by
  classical
  dsimp only
  funext i
  fin_cases i
  · change (W.addSubMap 0).eval ![x₁ * x₂, x₁ + x₂, 1] =
      (x₁ - x₂) ^ 2 *
        (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) *
          W.toAffine.addX x₁ x₂
            (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)))
    rw [addSubMap_eval_zero]
    simp only [one_pow, mul_one]
    calc
      (x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈ =
          x₁ ^ 2 * x₂ ^ 2 - W.b₄ * x₁ * x₂ - W.b₆ * (x₁ + x₂) - W.b₈ := by ring
      _ =
          W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) *
            W.toAffine.addX x₁ x₂
              (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) *
            (x₁ - x₂) ^ 2 :=
        (kummerBiquadratic_differentialAddX W h₁.left h₂.left hx).symm
      _ = (x₁ - x₂) ^ 2 *
          (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) *
            W.toAffine.addX x₁ x₂
              (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) := by ring
  · change (W.addSubMap 1).eval ![x₁ * x₂, x₁ + x₂, 1] =
      (x₁ - x₂) ^ 2 *
        (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) +
          W.toAffine.addX x₁ x₂
            (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)))
    rw [addSubMap_eval_one]
    simp only [one_pow, mul_one]
    calc
      2 * (x₁ + x₂) * (x₁ * x₂) + W.b₂ * (x₁ * x₂) + W.b₄ * (x₁ + x₂) + W.b₆ =
          (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) +
            W.toAffine.addX x₁ x₂
              (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) *
            (x₁ - x₂) ^ 2 :=
        (kummerBiquadratic_differentialAddX_trace W h₁.left h₂.left hx).symm
      _ = (x₁ - x₂) ^ 2 *
          (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) +
            W.toAffine.addX x₁ x₂
              (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) := by ring
  · simp [addSubMap]
    ring

/-- Point-level semantics of `addSubMap` on the actual affine group law in the
distinct-x branch.  Both readouts are generated from the same two point occurrences. -/
theorem addSubMap_sym2x_some_some_of_X_ne
    {x₁ x₂ y₁ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    let P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x₁ y₁ h₁
    let Q : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x₂ y₂ h₂
    (fun i => (W.addSubMap i).eval (P.sym2x Q)) =
      (x₁ - x₂) ^ 2 • ((P + Q).sym2x (P - Q)) := by
  dsimp only
  rw [WeierstrassCurve.Affine.Point.sym2x_some_some]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp only [sub_eq_add_neg]
  rw [WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  rw [WeierstrassCurve.Affine.Point.sym2x_some_some]
  simpa only [sub_eq_add_neg] using addSubMap_eval_some_some_of_X_ne W h₁ h₂ hx

omit [DecidableEq K] in
/-- The diagonal Kummer map is exactly the level-two division-polynomial pair. -/
theorem addSubMap_eval_diagonal (x : K) :
    (fun i => (W.addSubMap i).eval ![x ^ 2, 2 * x, 1]) =
      ![(W.Φ 2).eval x, (W.ΨSq 2).eval x, 0] := by
  funext i
  fin_cases i <;>
    simp [addSubMap, WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
      WeierstrassCurve.Ψ₂Sq] <;>
    ring

omit [DecidableEq K] in
/-- On an actual affine point, the level-two denominator is the square of the
vertical-tangent gap. -/
theorem psiSq_two_eval_eq_negY_gap_sq
    {x y : K} (h : W.toAffine.Equation x y) :
    (W.ΨSq 2).eval x = (y - W.toAffine.negY x y) ^ 2 := by
  rw [WeierstrassCurve.ΨSq_two, WeierstrassCurve.Ψ₂Sq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C,
    WeierstrassCurve.Affine.negY]
  have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination -4 * heq

omit [DecidableEq K] in
/-- A nonzero level-two denominator internally excludes the vertical tangent branch. -/
theorem ne_negY_of_psiSq_two_eval_ne
    {x y : K} (h : W.toAffine.Nonsingular x y)
    (hden : (W.ΨSq 2).eval x ≠ 0) : y ≠ W.toAffine.negY x y := by
  intro hzero
  apply hden
  have hsub : y - W.toAffine.negY x y = 0 := sub_eq_zero.mpr hzero
  rw [psiSq_two_eval_eq_negY_gap_sq W h.left, hsub]
  norm_num

/-- Actual tangent doubling has the Mathlib division-polynomial x-coordinate,
without assuming any scalar-multiplication formula. -/
theorem addX_self_eq_phi_two_div_psiSq_two
    {x y : K} (h : W.toAffine.Nonsingular x y)
    (hden : (W.ΨSq 2).eval x ≠ 0) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) =
      (W.Φ 2).eval x / (W.ΨSq 2).eval x := by
  let D : K := y - W.toAffine.negY x y
  let A : K := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
  have hgap := ne_negY_of_psiSq_two_eval_ne W h hden
  have hD : D ≠ 0 := sub_ne_zero.mpr hgap
  have hmul : D * (A / D) = A := mul_div_cancel₀ A hD
  rw [W.toAffine.slope_of_Y_ne rfl hgap]
  rw [eq_div_iff hden]
  rw [psiSq_two_eval_eq_negY_gap_sq W h.left]
  rw [WeierstrassCurve.Φ_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, WeierstrassCurve.Affine.addX]
  change ((A / D) ^ 2 + W.a₁ * (A / D) - W.a₂ - x - x) * D ^ 2 =
    x ^ 4 - W.b₄ * x ^ 2 - (2 * W.b₆) * x - W.b₈
  calc
    ((A / D) ^ 2 + W.a₁ * (A / D) - W.a₂ - x - x) * D ^ 2 =
        (D * (A / D)) ^ 2 + W.a₁ * D * (D * (A / D)) -
          (W.a₂ + 2 * x) * D ^ 2 := by ring
    _ = A ^ 2 + W.a₁ * D * A - (W.a₂ + 2 * x) * D ^ 2 := by rw [hmul]
    _ = x ^ 4 - W.b₄ * x ^ 2 - (2 * W.b₆) * x - W.b₈ := by
      have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.left
      dsimp only [A, D]
      rw [WeierstrassCurve.Affine.negY, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      linear_combination -(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) * heq

/-- Point-level diagonal semantics: the same actual point occurrence is doubled by
the affine group law and by the level-two division-polynomial Kummer map. -/
theorem addSubMap_sym2x_diagonal_of_psiSq_ne_zero
    {x y : K} (h : W.toAffine.Nonsingular x y)
    (hden : (W.ΨSq 2).eval x ≠ 0) :
    let P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y h
    (fun i => (W.addSubMap i).eval (P.sym2x P)) =
      (W.ΨSq 2).eval x • ((P + P).sym2x 0) := by
  have hden₂ : W.Ψ₂Sq.eval x ≠ 0 := by simpa using hden
  dsimp only
  rw [WeierstrassCurve.Affine.Point.sym2x_some_some]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (ne_negY_of_psiSq_two_eval_ne W h hden)]
  rw [WeierstrassCurve.Affine.Point.sym2x_some_zero]
  have hv : (![x * x, x + x, 1] : Fin 3 → K) = ![x ^ 2, 2 * x, 1] := by
    funext i
    fin_cases i <;> simp <;> ring
  rw [hv]
  rw [addSubMap_eval_diagonal]
  rw [addX_self_eq_phi_two_div_psiSq_two W h hden]
  funext i
  fin_cases i <;> simp
  field_simp [hden₂]

end SaturationMonoid.UniversalBSDWeierstrassDivisionXIdentity
