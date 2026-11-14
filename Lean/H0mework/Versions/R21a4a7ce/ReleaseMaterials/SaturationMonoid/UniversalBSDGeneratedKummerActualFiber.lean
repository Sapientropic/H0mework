import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeneratedKummerPolynomialSemantics
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual fibres of the generated Kummer multiplication map
-/

open scoped Polynomial

noncomputable section

namespace SaturationMonoid.UniversalBSDGeneratedKummerActualFiber

open Polynomial
open UniversalBSDGeneratedKummerLadder
open UniversalBSDKummerValueSemantics
open UniversalBSDGeneratedKummerPolynomialSemantics

variable {K : Type*} [Field K]

/-- Every x-coordinate over an algebraically closed field has an actual point on
an elliptic Weierstrass curve. -/
theorem exists_nonsingularPoint_with_x
    [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic] (x : K) :
    ∃ y : K, W.toAffine.Nonsingular x y := by
  let rhs : K := x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
  let p : K[X] := C 1 * X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-rhs)
  have hpNat : p.natDegree = 2 := by
    dsimp only [p]
    exact natDegree_quadratic one_ne_zero
  have hpNe : p ≠ 0 := by
    intro hpZero
    have := hpNat
    rw [hpZero, natDegree_zero] at this
    norm_num at this
  have hpDegree : p.degree ≠ 0 := by
    rw [degree_eq_natDegree hpNe, hpNat]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root p hpDegree
  refine ⟨y, WeierstrassCurve.Affine.equation_iff_nonsingular.mp ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  have hyZero : p.eval y = 0 := hy
  dsimp only [p, rhs] at hyZero
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, one_mul] at hyZero
  linear_combination hyZero

/-- A nonzero reciprocal cross identity generates an actual division point.
The possible Kummer sign is removed by negating the source point. -/
theorem exists_actual_divisionPoint_of_cross_identity
    [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) {targetX targetY : K}
    (hTarget : W.toAffine.Nonsingular targetX targetY)
    (b sourceX : K) (hb : b ≠ 0) (hTargetX : b * targetX = 1)
    (hcross : b * (generatedKummerXZ W n).1.eval sourceX =
      (generatedKummerXZ W n).2.eval sourceX) :
    ∃ Q : W.toAffine.Point,
      n • Q = WeierstrassCurve.Affine.Point.some targetX targetY hTarget := by
  obtain ⟨sourceY, hSource⟩ := exists_nonsingularPoint_with_x W sourceX
  let Q₀ : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some sourceX sourceY hSource
  have hrep := generatedKummerXZ_eval_represents W hSource n
  rcases hrep with ⟨a, ha⟩
  rcases hmultiple : n • Q₀ with (_ | ⟨resultX, resultY, hResult⟩)
  · rw [hmultiple] at ha
    have hnum : (generatedKummerXZ W n).1.eval sourceX = (a : K) := by
      have h0 := congrFun ha 0
      simpa [evalKummerXZ, WeierstrassCurve.Affine.Point.xRep] using h0
    have hden : (generatedKummerXZ W n).2.eval sourceX = 0 := by
      have h1 := congrFun ha 1
      simpa [evalKummerXZ, WeierstrassCurve.Affine.Point.xRep] using h1
    have haNe : (a : K) ≠ 0 := a.ne_zero
    exfalso
    apply mul_ne_zero hb haNe
    rw [← hnum, hcross, hden]
  · rw [hmultiple] at ha
    have hnum : (generatedKummerXZ W n).1.eval sourceX = (a : K) * resultX := by
      have h0 := congrFun ha 0
      simpa [evalKummerXZ, WeierstrassCurve.Affine.Point.xRep] using h0
    have hden : (generatedKummerXZ W n).2.eval sourceX = (a : K) := by
      have h1 := congrFun ha 1
      simpa [evalKummerXZ, WeierstrassCurve.Affine.Point.xRep] using h1
    have haNe : (a : K) ≠ 0 := a.ne_zero
    have hResultX : resultX = targetX := by
      have hbx : b * resultX = 1 := by
        apply mul_left_cancel₀ haNe
        calc
          (a : K) * (b * resultX) = b * ((a : K) * resultX) := by ring
          _ = b * (generatedKummerXZ W n).1.eval sourceX := by rw [hnum]
          _ = (generatedKummerXZ W n).2.eval sourceX := hcross
          _ = (a : K) := hden
          _ = (a : K) * 1 := by ring
      apply mul_left_cancel₀ hb
      rw [hbx, hTargetX]
    have hxRep :
        (WeierstrassCurve.Affine.Point.some resultX resultY hResult).xRep =
          (WeierstrassCurve.Affine.Point.some targetX targetY hTarget).xRep := by
      simp [WeierstrassCurve.Affine.Point.xRep, hResultX]
    rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxRep with hEq | hEq
    · exact ⟨Q₀, by rw [hmultiple, hEq]⟩
    · refine ⟨-Q₀, ?_⟩
      rw [neg_nsmul, hmultiple, hEq, neg_neg]

end SaturationMonoid.UniversalBSDGeneratedKummerActualFiber
