import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeneratedKummerActualFiber
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeneratedKummerDegreeTower
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Universal BSD geometric divisibility

The generated Kummer ladder has monic numerator of degree `n²` and a
lower-degree denominator. Over an algebraically closed field this produces an
actual division point above every target, with the Kummer sign removed by
negating the source point.
-/

open scoped Polynomial

set_option autoImplicit false

namespace SaturationMonoid
namespace UniversalBSDGeometricDivisibility

open Polynomial
open UniversalBSDGeneratedKummerActualFiber
open UniversalBSDGeneratedKummerLadder
open UniversalBSDGeneratedKummerPolynomialSemantics
open UniversalBSDKummerValueSemantics

noncomputable section

set_option maxHeartbeats 1200000

section AlgebraicallyClosed

variable {K : Type*} [Field K] [CharZero K]

def generatedKummerFiberPolynomial
    (W : WeierstrassCurve K) (n : ℕ) (targetX : K) : K[X] :=
  (generatedKummerXZ W n).1 - C targetX * (generatedKummerXZ W n).2

theorem generatedKummerFiberPolynomial_isMonicOfDegree
    (W : WeierstrassCurve K) (n : ℕ) (hn : 0 < n) (targetX : K) :
    (generatedKummerFiberPolynomial W n targetX).IsMonicOfDegree (n ^ 2) := by
  let data := generatedKummerXZ_degree W n
  let N := n ^ 2
  have hN : 0 < N := pow_pos hn 2
  have hdenLt : (generatedKummerXZ W n).2.natDegree < N :=
    data.denominator_degree.trans_lt (Nat.sub_lt hN Nat.zero_lt_one)
  have hdenCoeff : (generatedKummerXZ W n).2.coeff N = 0 :=
    coeff_eq_zero_of_natDegree_lt hdenLt
  rw [isMonicOfDegree_iff]
  constructor
  · dsimp only [generatedKummerFiberPolynomial]
    refine (natDegree_sub_le _ _).trans (max_le data.numerator_degree ?_)
    exact (natDegree_C_mul_le targetX _).trans data.denominator_degree |>.trans
      (Nat.sub_le N 1)
  · rw [generatedKummerFiberPolynomial, coeff_sub, coeff_C_mul,
      data.numerator_leading, hdenCoeff, mul_zero, sub_zero]

theorem exists_generatedKummerFiberRoot
    [IsAlgClosed K]
    (W : WeierstrassCurve K) (n : ℕ) (hn : 0 < n) (targetX : K) :
    ∃ sourceX : K,
      (generatedKummerXZ W n).1.eval sourceX =
        targetX * (generatedKummerXZ W n).2.eval sourceX := by
  let F := generatedKummerFiberPolynomial W n targetX
  have hDegreeData : F.IsMonicOfDegree (n ^ 2) :=
    generatedKummerFiberPolynomial_isMonicOfDegree W n hn targetX
  have hDegree : F.degree ≠ 0 := by
    rw [degree_eq_natDegree hDegreeData.monic.ne_zero, hDegreeData.natDegree_eq]
    exact_mod_cast (pow_pos hn 2).ne'
  obtain ⟨sourceX, hroot⟩ := IsAlgClosed.exists_root F hDegree
  refine ⟨sourceX, ?_⟩
  change F.eval sourceX = 0 at hroot
  exact sub_eq_zero.mp (by simpa [F, generatedKummerFiberPolynomial] using hroot)

theorem exists_actual_nsmul_eq
    [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) (hn : 0 < n) (target : W.toAffine.Point) :
    ∃ Q : W.toAffine.Point, n • Q = target := by
  rcases target with (_ | ⟨targetX, targetY, hTarget⟩)
  · exact ⟨0, nsmul_zero n⟩
  obtain ⟨sourceX, hcross⟩ := exists_generatedKummerFiberRoot W n hn targetX
  obtain ⟨sourceY, hSource⟩ := exists_nonsingularPoint_with_x W sourceX
  let Q₀ : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some sourceX sourceY hSource
  obtain ⟨a, ha⟩ := generatedKummerXZ_eval_represents W hSource n
  rcases hmultiple : n • Q₀ with (_ | ⟨resultX, resultY, hResult⟩)
  · rw [hmultiple] at ha
    have hnum : (generatedKummerXZ W n).1.eval sourceX = (a : K) := by
      have h0 := congrFun ha 0
      simpa [evalKummerXZ, WeierstrassCurve.Affine.Point.xRep] using h0
    have hden : (generatedKummerXZ W n).2.eval sourceX = 0 := by
      have h1 := congrFun ha 1
      simpa [evalKummerXZ, WeierstrassCurve.Affine.Point.xRep] using h1
    exfalso
    exact a.ne_zero (by rw [← hnum, hcross, hden, mul_zero])
  · rw [hmultiple] at ha
    have hnum : (generatedKummerXZ W n).1.eval sourceX = (a : K) * resultX := by
      have h0 := congrFun ha 0
      simpa [evalKummerXZ, WeierstrassCurve.Affine.Point.xRep] using h0
    have hden : (generatedKummerXZ W n).2.eval sourceX = (a : K) := by
      have h1 := congrFun ha 1
      simpa [evalKummerXZ, WeierstrassCurve.Affine.Point.xRep] using h1
    have hResultX : resultX = targetX := by
      apply mul_left_cancel₀ a.ne_zero
      calc
        (a : K) * resultX = (generatedKummerXZ W n).1.eval sourceX := hnum.symm
        _ = targetX * (generatedKummerXZ W n).2.eval sourceX := hcross
        _ = (a : K) * targetX := by rw [hden]; ring
    have hxRep :
        (WeierstrassCurve.Affine.Point.some resultX resultY hResult).xRep =
          (WeierstrassCurve.Affine.Point.some targetX targetY hTarget).xRep := by
      simp [WeierstrassCurve.Affine.Point.xRep, hResultX]
    rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxRep with hEq | hEq
    · exact ⟨Q₀, by rw [hmultiple, hEq]⟩
    · exact ⟨-Q₀, by rw [neg_nsmul, hmultiple, hEq, neg_neg]⟩

end AlgebraicallyClosed

end

end UniversalBSDGeometricDivisibility
end SaturationMonoid

