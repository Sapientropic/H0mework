import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDWeierstrassDivisionXIdentity
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

/-!
# Full actual semantics of the Weierstrass Kummer addition map

This module closes the remaining zero, opposite, and two-torsion branches of
`WeierstrassCurve.addSubMap` at the projective level.
-/

noncomputable section

open scoped WeierstrassCurve.Projective

namespace SaturationMonoid.UniversalBSDWeierstrassAddSubMapFullSemantics

open MvPolynomial
open WeierstrassCurve
open WeierstrassCurve.Affine
open SaturationMonoid.UniversalBSDWeierstrassDivisionXIdentity

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

omit [DecidableEq K] in
private theorem diagonalInput_eq (x : K) :
    (![x * x, x + x, 1] : Fin 3 → K) = ![x ^ 2, 2 * x, 1] := by
  funext i
  fin_cases i <;> simp <;> ring

omit [W.IsElliptic] in
/-- In the two-torsion branch, the diagonal Kummer output is a nonzero multiple
of the projective origin pair. -/
theorem addSubMap_sym2x_diagonal_of_psiSq_eq_zero
    {x y : K} (h : W.toAffine.Nonsingular x y)
    (hden : (W.ΨSq 2).eval x = 0) :
    let P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y h
    (fun i => (W.addSubMap i).eval (P.sym2x P)) =
      (W.Φ 2).eval x • ((P + P).sym2x 0) := by
  have hden₂ : W.Ψ₂Sq.eval x = 0 := by simpa using hden
  have hgapSq : (y - W.toAffine.negY x y) ^ 2 = 0 := by
    rw [← psiSq_two_eval_eq_negY_gap_sq W h.left]
    exact hden
  have hself : y = W.toAffine.negY x y :=
    sub_eq_zero.mp (sq_eq_zero_iff.mp hgapSq)
  dsimp only
  rw [WeierstrassCurve.Affine.Point.sym2x_some_some]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hself]
  rw [WeierstrassCurve.Affine.Point.sym2x_zero_zero]
  rw [diagonalInput_eq]
  rw [addSubMap_eval_diagonal]
  funext i
  fin_cases i <;> simp [hden₂]

omit [DecidableEq K] in
/-- The level-two numerator cannot also vanish at an actual two-torsion point
on an elliptic Weierstrass curve. -/
theorem phi_two_eval_ne_zero_of_psiSq_two_eval_eq_zero
    {x : K} (hden : (W.ΨSq 2).eval x = 0) : (W.Φ 2).eval x ≠ 0 := by
  have hin : (![x ^ 2, 2 * x, 1] : Fin 3 → K) ≠ 0 := by
    intro hz
    have hone : (1 : K) ≠ 0 := one_ne_zero
    exact hone (by simpa using congrFun hz (2 : Fin 3))
  have hout := W.addSubMap_ne_zero hin
  rw [addSubMap_eval_diagonal] at hout
  intro hphi
  apply hout
  rw [hphi, hden]
  funext i
  fin_cases i <;> rfl

/-- Every actual diagonal occurrence has the expected projective doubling
semantics, including the two-torsion branch. -/
theorem addSubMap_sym2x_diagonal_projective
    {x y : K} (h : W.toAffine.Nonsingular x y) :
    let P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y h
    (⟦fun i => (W.addSubMap i).eval (P.sym2x P)⟧ :
        WeierstrassCurve.Projective.PointClass K) =
      ⟦(P + P).sym2x 0⟧ := by
  dsimp only
  by_cases hden : (W.ΨSq 2).eval x = 0
  · have hscale := addSubMap_sym2x_diagonal_of_psiSq_eq_zero W h hden
    dsimp only at hscale
    calc
      (⟦fun i => (W.addSubMap i).eval
          ((WeierstrassCurve.Affine.Point.some x y h).sym2x
            (WeierstrassCurve.Affine.Point.some x y h))⟧ :
          WeierstrassCurve.Projective.PointClass K) =
          ⟦(W.Φ 2).eval x •
            (((WeierstrassCurve.Affine.Point.some x y h) +
              (WeierstrassCurve.Affine.Point.some x y h)).sym2x 0)⟧ :=
        congrArg Quotient.mk' hscale
      _ = ⟦((WeierstrassCurve.Affine.Point.some x y h) +
            (WeierstrassCurve.Affine.Point.some x y h)).sym2x 0⟧ :=
          WeierstrassCurve.Projective.smul_eq _
          (isUnit_iff_ne_zero.mpr
            (phi_two_eval_ne_zero_of_psiSq_two_eval_eq_zero W hden))
  · have hscale := addSubMap_sym2x_diagonal_of_psiSq_ne_zero W h hden
    dsimp only at hscale
    calc
      (⟦fun i => (W.addSubMap i).eval
          ((WeierstrassCurve.Affine.Point.some x y h).sym2x
            (WeierstrassCurve.Affine.Point.some x y h))⟧ :
          WeierstrassCurve.Projective.PointClass K) =
          ⟦(W.ΨSq 2).eval x •
            (((WeierstrassCurve.Affine.Point.some x y h) +
              (WeierstrassCurve.Affine.Point.some x y h)).sym2x 0)⟧ :=
        congrArg Quotient.mk' hscale
      _ = ⟦((WeierstrassCurve.Affine.Point.some x y h) +
            (WeierstrassCurve.Affine.Point.some x y h)).sym2x 0⟧ :=
        WeierstrassCurve.Projective.smul_eq _ (isUnit_iff_ne_zero.mpr hden)

omit [W.IsElliptic] in
/-- Distinct affine x-coordinates give the projective addition/subtraction mouth. -/
theorem addSubMap_sym2x_some_some_of_X_ne_projective
    {x₁ x₂ y₁ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    let P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x₁ y₁ h₁
    let Q : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x₂ y₂ h₂
    (⟦fun i => (W.addSubMap i).eval (P.sym2x Q)⟧ :
        WeierstrassCurve.Projective.PointClass K) =
      ⟦(P + Q).sym2x (P - Q)⟧ := by
  dsimp only
  have hscale := addSubMap_sym2x_some_some_of_X_ne W h₁ h₂ hx
  dsimp only at hscale
  calc
    (⟦fun i => (W.addSubMap i).eval
        ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁).sym2x
          (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂))⟧ :
        WeierstrassCurve.Projective.PointClass K) =
        ⟦(x₁ - x₂) ^ 2 •
          (((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
            (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)).sym2x
            ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) -
              (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)))⟧ :=
      congrArg Quotient.mk' hscale
    _ = ⟦((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
          (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)).sym2x
          ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) -
            (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂))⟧ :=
      WeierstrassCurve.Projective.smul_eq _
        (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr hx)))

/-- Full-carrier actual semantics of Mathlib's Kummer addition map.  No branch,
coordinate, or non-torsion premise remains at the public mouth. -/
theorem addSubMap_sym2x_projective (P Q : W.toAffine.Point) :
    (⟦fun i => (W.addSubMap i).eval (P.sym2x Q)⟧ :
        WeierstrassCurve.Projective.PointClass K) =
      ⟦(P + Q).sym2x (P - Q)⟧ := by
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
    · simp only [← WeierstrassCurve.Affine.Point.zero_def]
      apply congrArg Quotient.mk'
      funext i
      fin_cases i <;> simp [sub_eq_add_neg, WeierstrassCurve.addSubMap]
    · simp only [← WeierstrassCurve.Affine.Point.zero_def]
      apply congrArg Quotient.mk'
      funext i
      fin_cases i <;> simp [sub_eq_add_neg, WeierstrassCurve.addSubMap] <;> ring
  · rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
    · simp only [← WeierstrassCurve.Affine.Point.zero_def]
      apply congrArg Quotient.mk'
      funext i
      fin_cases i <;> simp [sub_eq_add_neg, WeierstrassCurve.addSubMap] <;> ring
    · by_cases hx : x₁ = x₂
      · subst x₂
        rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.left h₂.left rfl with hy | hy
        ·
          subst y₂
          simpa using addSubMap_sym2x_diagonal_projective W h₁
        · have hPQ : WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ =
              -WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ := by
            rw [WeierstrassCurve.Affine.Point.neg_some]
            rw [WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨rfl, hy⟩
          have hy' : y₂ = W.toAffine.negY x₁ y₁ := by
            rw [hy, W.toAffine.negY_negY]
          have hQP : WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ =
              -WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ := by
            rw [WeierstrassCurve.Affine.Point.neg_some]
            rw [WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨rfl, hy'⟩
          rw [hQP]
          rw [WeierstrassCurve.Affine.Point.sym2x_neg_right]
          rw [add_neg_cancel, sub_neg_eq_add]
          exact (addSubMap_sym2x_diagonal_projective W h₁).trans
            (congrArg Quotient.mk'
              (WeierstrassCurve.Affine.Point.sym2x_comm
                (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
                  WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) 0))
      · exact addSubMap_sym2x_some_some_of_X_ne_projective W h₁ h₂ hx

end SaturationMonoid.UniversalBSDWeierstrassAddSubMapFullSemantics
