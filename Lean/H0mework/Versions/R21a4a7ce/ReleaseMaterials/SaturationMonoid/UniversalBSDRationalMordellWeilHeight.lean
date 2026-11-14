import Mathlib.GroupTheory.Descent
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeometricGalois
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDKummerValueSemantics

/-!
# Universal BSD rational Mordell--Weil height

The normalized rational x-coordinate gives a Northcott height on actual
rational points. Together with Mathlib's descent theorem, finite weak
Mordell--Weil quotient and one approximate parallelogram law imply finite
generation. No finite-index or height law is hidden in the source.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace UniversalBSDRationalMordellWeilHeight

open Height
open UniversalBSDGeometricGalois
open UniversalBSDWeierstrassAddSubMapFullSemantics
open UniversalBSDKummerValueSemantics

noncomputable section

abbrev RationalPoints (source : RationalEllipticCurveSource) :=
  source.curve.toAffine.Point

def rationalPointX (source : RationalEllipticCurveSource) :
    RationalPoints source → ℚ
  | 0 => 0
  | .some x _ _ => x

theorem rationalPointX_eq_implies_xRep_eq_of_ne_zero
    (source : RationalEllipticCurveSource)
    {P Q : RationalPoints source}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : rationalPointX source P = rationalPointX source Q) :
    P.xRep = Q.xRep := by
  rcases P with (_ | ⟨xP, yP, hPointP⟩)
  · exact (hP rfl).elim
  rcases Q with (_ | ⟨xQ, yQ, hPointQ⟩)
  · exact (hQ rfl).elim
  change xP = xQ at hx
  cases hx
  rfl

theorem rationalPointX_finite_preimage_singleton
    (source : RationalEllipticCurveSource) (x : ℚ) :
    Set.Finite (rationalPointX source ⁻¹' {x}) := by
  by_cases hP : ∃ P : RationalPoints source,
      P ∈ rationalPointX source ⁻¹' {x} ∧ P ≠ 0
  · obtain ⟨P, hPx, hP0⟩ := hP
    apply (Set.toFinite ({0, P, -P} : Set (RationalPoints source))).subset
    intro Q hQ
    by_cases hQ0 : Q = 0
    · simp [hQ0]
    have hxPQ : rationalPointX source P = rationalPointX source Q := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hPx.trans hQ.symm
    rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep
      (rationalPointX_eq_implies_xRep_eq_of_ne_zero source hP0 hQ0 hxPQ) with
      hEq | hNeg
    · simp [hEq]
    · simp [hNeg]
  · apply (Set.toFinite ({0} : Set (RationalPoints source))).subset
    intro Q hQ
    by_contra hQ0
    exact hP ⟨Q, hQ, hQ0⟩

instance rationalPointX_tendstoCofinite
    (source : RationalEllipticCurveSource) :
    Filter.TendstoCofinite (rationalPointX source) :=
  (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr
    (rationalPointX_finite_preimage_singleton source)

def rationalNaiveHeight (source : RationalEllipticCurveSource) :
    RationalPoints source → ℝ :=
  logHeight₁ ∘ rationalPointX source

theorem rationalNaiveHeight_eq_logHeight_xRep
    (source : RationalEllipticCurveSource)
    (P : RationalPoints source) :
    rationalNaiveHeight source P = logHeight P.xRep := by
  rcases P with (_ | ⟨x, y, hPoint⟩)
  · simp [rationalNaiveHeight, rationalPointX,
      logHeight₁_eq_logHeight, WeierstrassCurve.Affine.Point.xRep]
  · simp [rationalNaiveHeight, rationalPointX,
      logHeight₁_eq_logHeight, WeierstrassCurve.Affine.Point.xRep]

theorem abs_logHeight_sym2x_sub_height_sum_le
    (source : RationalEllipticCurveSource) :
    ∃ C, ∀ P Q : RationalPoints source,
      |logHeight (P.sym2x Q) -
        (rationalNaiveHeight source P + rationalNaiveHeight source Q)| ≤ C := by
  obtain ⟨C, hC⟩ := Height.abs_logHeight_sym2_sub_le ℚ
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [rationalNaiveHeight_eq_logHeight_xRep,
    rationalNaiveHeight_eq_logHeight_xRep]
  have hPRep : ![P.xRep 0, P.xRep 1] = P.xRep := by
    funext i
    fin_cases i <;> rfl
  have hQRep : ![Q.xRep 0, Q.xRep 1] = Q.xRep := by
    funext i
    fin_cases i <;> rfl
  have hP : ![P.xRep 0, P.xRep 1] ≠ 0 := by
    rw [hPRep]
    exact WeierstrassCurve.Affine.Point.xRep_ne_zero P
  have hQ : ![Q.xRep 0, Q.xRep 1] ≠ 0 := by
    rw [hQRep]
    exact WeierstrassCurve.Affine.Point.xRep_ne_zero Q
  simpa only [WeierstrassCurve.Affine.Point.sym2x, hPRep, hQRep] using
    (hC (a := P.xRep 0) (b := P.xRep 1)
      (c := Q.xRep 0) (d := Q.xRep 1) hP hQ)

theorem logHeight_addSubMap_sym2x_eq
    (source : RationalEllipticCurveSource)
    (P Q : RationalPoints source) :
    logHeight (fun i ↦ (source.curve.addSubMap i).eval (P.sym2x Q)) =
      logHeight ((P + Q).sym2x (P - Q)) := by
  obtain ⟨u, hu⟩ := exists_unit_smul_of_pointClass_eq
    (addSubMap_sym2x_projective source.curve P Q)
  rw [hu, logHeight_smul_eq_logHeight _ (Units.ne_zero u)]

instance rationalNaiveHeight_northcott
    (source : RationalEllipticCurveSource) :
    Northcott (rationalNaiveHeight source) :=
  Northcott.comp_of_finite_fibers (rationalPointX source) logHeight₁

theorem rationalNaiveHeight_nonneg
    (source : RationalEllipticCurveSource)
    (P : RationalPoints source) :
    0 ≤ rationalNaiveHeight source P :=
  zero_le_logHeight₁ _

theorem rationalNaiveHeight_approx_parallelogram
    (source : RationalEllipticCurveSource) :
    ∃ C, ∀ P Q : RationalPoints source,
      |rationalNaiveHeight source (P + Q) +
          rationalNaiveHeight source (P - Q) -
        2 * (rationalNaiveHeight source P + rationalNaiveHeight source Q)| ≤ C := by
  obtain ⟨Cs, hSym⟩ := abs_logHeight_sym2x_sub_height_sum_le source
  obtain ⟨Ca, hAdd⟩ :=
    WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le source.curve
  refine ⟨Ca + 3 * Cs, fun P Q ↦ ?_⟩
  have hInput := hSym P Q
  have hOutput := hSym (P + Q) (P - Q)
  have hMap := hAdd (P.sym2x Q)
  rw [logHeight_addSubMap_sym2x_eq source P Q] at hMap
  rw [abs_le] at hInput hOutput hMap ⊢
  constructor <;> linarith

theorem rationalMordellWeil_fg_of_finiteIndex_of_parallelogram
    (source : RationalEllipticCurveSource)
    (hindex : (nsmulAddMonoidHom 2 :
      RationalPoints source →+ RationalPoints source).range.FiniteIndex)
    {C : ℝ}
    (hparallelogram : ∀ P Q : RationalPoints source,
      |rationalNaiveHeight source (P + Q) +
          rationalNaiveHeight source (P - Q) -
        2 * (rationalNaiveHeight source P + rationalNaiveHeight source Q)| ≤ C) :
    AddGroup.FG (RationalPoints source) :=
  AddCommGroup.fg_of_descent' hindex
    (rationalNaiveHeight_nonneg source) hparallelogram

theorem rationalMordellWeil_fg_of_finiteIndex
    (source : RationalEllipticCurveSource)
    (hindex : (nsmulAddMonoidHom 2 :
      RationalPoints source →+ RationalPoints source).range.FiniteIndex) :
    AddGroup.FG (RationalPoints source) := by
  obtain ⟨C, hC⟩ := rationalNaiveHeight_approx_parallelogram source
  exact rationalMordellWeil_fg_of_finiteIndex_of_parallelogram source hindex hC

end

end UniversalBSDRationalMordellWeilHeight
end SaturationMonoid
