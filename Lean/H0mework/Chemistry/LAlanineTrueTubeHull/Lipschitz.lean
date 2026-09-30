import H0mework.Chemistry.LAlanineTrueTubeHull.MatrixComplete
import H0mework.Chemistry.LAlanineTrueTube.TraceSignedField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeHull

open SourceGaussianModel SourceSignedEvaluator ContinuousGradient ContinuousChart TrueTubeTrace Set
open scoped BigOperators NNReal
noncomputable section

def rowBound (i : Fin 3) : ℚ := ∑ j : Fin 3, magnitude (TrueTubeHullMatrix.sourceField.hessian i j)
def normBound : ℚ := max (rowBound 0) (max (rowBound 1) (rowBound 2))

theorem rowBound_nonneg (i : Fin 3) : 0 ≤ rowBound i :=
  Finset.sum_nonneg (fun _j _ => (abs_nonneg _).trans (le_max_left _ _))

theorem normBound_nonneg : 0 ≤ normBound :=
  (rowBound_nonneg 0).trans (le_max_left _ _)

theorem rows_le (i : Fin 3) : rowBound i ≤ normBound := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

def lipschitzConstant : ℝ≥0 := ⟨(normBound : ℝ), Rat.cast_nonneg.mpr normBound_nonneg⟩

theorem hessian_norm (x : Point) (inside : InRectangle TrueTubeHullSource.box x) :
    ‖sourceHessianLinear x‖ ≤ (lipschitzConstant : ℝ) := by
  apply matrix_norm_le TrueTubeHullMatrix.sourceField.hessian _ normBound normBound_nonneg
  · intro i j
    rw [hessian_single]
    exact (TrueTubeHullMatrix.actual_source_field x inside).2 i j
  · exact rows_le

theorem common_lipschitz : LipschitzOnWith lipschitzConstant sourceGradient
    (Icc (lowerPoint TrueTubeHullSource.box) (upperPoint TrueTubeHullSource.box)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (sourceGradient_hasFDerivAt x).differentiableAt) _ (convex_Icc _ _)
  intro x hx
  rw [(sourceGradient_hasFDerivAt x).fderiv]
  exact_mod_cast hessian_norm x ((inRectangle_iff _ _).mpr hx)

theorem common_signed_lipschitz (sign : ℝ) (unit : |sign| = 1) :
    LipschitzOnWith lipschitzConstant (signedGradient sign)
      (Icc (lowerPoint TrueTubeHullSource.box) (upperPoint TrueTubeHullSource.box)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa only [signedGradient, dist_smul₀, Real.norm_eq_abs, unit, one_mul] using
    common_lipschitz.dist_le_mul x hx y hy

theorem normBound_strict : 1649 / 1000 < normBound ∧ normBound < 33 / 20 := by decide +kernel

theorem constant_strict : (1649 / 1000 : ℝ) < lipschitzConstant ∧
    (lipschitzConstant : ℝ) < 33 / 20 := by
  change (1649 / 1000 : ℝ) < (normBound : ℝ) ∧ (normBound : ℝ) < 33 / 20
  constructor
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt.mpr normBound_strict.1 : ((1649 / 1000 : ℚ) : ℝ) < (normBound : ℝ))
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt.mpr normBound_strict.2 : (normBound : ℝ) < ((33 / 20 : ℚ) : ℝ))

end
end LAlanine40K2025.BasinRefinement.TrueTubeHull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
